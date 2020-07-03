----------------------------- MODULE MaximallySimple -----------------------------

EXTENDS Naturals, TLC

(* --algorithm foo

variables baseline = {},
          rollup = {},
          time = 0;

process cagg = "cagg"
begin Loop:
  while time < 10 do
  WriteNewData:
    baseline := baseline \union {time};
    time := time + 1;
  end while;
end process

process roll_up = "roll_up"
variables needRollup = {};
begin Loop:
  while time < 10 do
  GetLastDataPoint:
    needRollup := baseline \ rollup;
    if needRollup /= {} then
      either
        WriteRollup:
        rollup := rollup \union {Min(needRollup)};
      or
        skip; \* write failed
      end either;
    end if;
  end while;
end process

end algorithm; *)

Min(S) == CHOOSE x \in S: 
            \A y \in S \ {x}: 
              y > x

Max(S) == CHOOSE x \in S: 
            \A y \in S \ {x}: 
              y < x

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-20bdd0a3dc5900e980628f039053fd8e
\* Label Loop of process cagg at line 13 col 3 changed to Loop_
VARIABLES baseline, rollup, time, pc, needRollup

vars == << baseline, rollup, time, pc, needRollup >>

ProcSet == {"cagg"} \cup {"roll_up"}

Init == (* Global variables *)
        /\ baseline = {}
        /\ rollup = {}
        /\ time = 0
        (* Process roll_up *)
        /\ needRollup = {}
        /\ pc = [self \in ProcSet |-> CASE self = "cagg" -> "Loop_"
                                        [] self = "roll_up" -> "Loop"]

Loop_ == /\ pc["cagg"] = "Loop_"
         /\ IF time < 10
               THEN /\ pc' = [pc EXCEPT !["cagg"] = "WriteNewData"]
               ELSE /\ pc' = [pc EXCEPT !["cagg"] = "Done"]
         /\ UNCHANGED << baseline, rollup, time, needRollup >>

WriteNewData == /\ pc["cagg"] = "WriteNewData"
                /\ baseline' = (baseline \union {time})
                /\ time' = time + 1
                /\ pc' = [pc EXCEPT !["cagg"] = "Loop_"]
                /\ UNCHANGED << rollup, needRollup >>

cagg == Loop_ \/ WriteNewData

Loop == /\ pc["roll_up"] = "Loop"
        /\ IF time < 10
              THEN /\ pc' = [pc EXCEPT !["roll_up"] = "GetLastDataPoint"]
              ELSE /\ pc' = [pc EXCEPT !["roll_up"] = "Done"]
        /\ UNCHANGED << baseline, rollup, time, needRollup >>

GetLastDataPoint == /\ pc["roll_up"] = "GetLastDataPoint"
                    /\ needRollup' = baseline \ rollup
                    /\ IF needRollup' /= {}
                          THEN /\ \/ /\ pc' = [pc EXCEPT !["roll_up"] = "WriteRollup"]
                                  \/ /\ TRUE
                                     /\ pc' = [pc EXCEPT !["roll_up"] = "Loop"]
                          ELSE /\ pc' = [pc EXCEPT !["roll_up"] = "Loop"]
                    /\ UNCHANGED << baseline, rollup, time >>

WriteRollup == /\ pc["roll_up"] = "WriteRollup"
               /\ rollup' = (rollup \union {Min(needRollup)})
               /\ pc' = [pc EXCEPT !["roll_up"] = "Loop"]
               /\ UNCHANGED << baseline, time, needRollup >>

roll_up == Loop \/ GetLastDataPoint \/ WriteRollup

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == cagg \/ roll_up
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-7c772d61dfce49f5ef65120ab83fdd9f

=============================================================================
\* Modification History
\* Last modified Fri Jul 03 13:43:52 PDT 2020 by spencerpearson
\* Created Thu Jul 02 20:49:24 PDT 2020 by spencerpearson
