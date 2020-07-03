----------------------------- MODULE WithQueue -----------------------------

EXTENDS Naturals, TLC

(* --algorithm foo

variables baseline = {},
          rollup = {},
          queue = {},
          time = 0;

process cagg = "cagg"
begin Loop:
  while time < 10 do
  WriteNewData:
    baseline := baseline \union {time};
    time := time + 1;
  end while;
end process

process generator = "generator"
variables needRollup = {};
begin Loop:
  while time < 10 do
  GetLastDataPoint:
    if rollup = {} then
      needRollup := baseline
    else
      needRollup := { x \in baseline : x > Max(rollup) }
    end if;
    if needRollup /= {} then
      either
      Enqueue:
        queue := queue \union needRollup;
      or
        skip; \* write failed
      end either;
    end if;
  end while;
end process

process executor = "executor"
variables job = 9999;
begin Loop:
  while time < 10 do
  Dequeue:
    if queue /= {} then
      job := Min(queue);
      queue := queue \ {job};
    Execute:
      either
        rollup := rollup \union {job};
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


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9b7eea665054634a230601022eaac543
\* Label Loop of process cagg at line 14 col 3 changed to Loop_
\* Label Loop of process generator at line 24 col 3 changed to Loop_g
VARIABLES baseline, rollup, queue, time, pc, needRollup, job

vars == << baseline, rollup, queue, time, pc, needRollup, job >>

ProcSet == {"cagg"} \cup {"generator"} \cup {"executor"}

Init == (* Global variables *)
        /\ baseline = {}
        /\ rollup = {}
        /\ queue = {}
        /\ time = 0
        (* Process generator *)
        /\ needRollup = {}
        (* Process executor *)
        /\ job = 9999
        /\ pc = [self \in ProcSet |-> CASE self = "cagg" -> "Loop_"
                                        [] self = "generator" -> "Loop_g"
                                        [] self = "executor" -> "Loop"]

Loop_ == /\ pc["cagg"] = "Loop_"
         /\ IF time < 10
               THEN /\ pc' = [pc EXCEPT !["cagg"] = "WriteNewData"]
               ELSE /\ pc' = [pc EXCEPT !["cagg"] = "Done"]
         /\ UNCHANGED << baseline, rollup, queue, time, needRollup, job >>

WriteNewData == /\ pc["cagg"] = "WriteNewData"
                /\ baseline' = (baseline \union {time})
                /\ time' = time + 1
                /\ pc' = [pc EXCEPT !["cagg"] = "Loop_"]
                /\ UNCHANGED << rollup, queue, needRollup, job >>

cagg == Loop_ \/ WriteNewData

Loop_g == /\ pc["generator"] = "Loop_g"
          /\ IF time < 10
                THEN /\ pc' = [pc EXCEPT !["generator"] = "GetLastDataPoint"]
                ELSE /\ pc' = [pc EXCEPT !["generator"] = "Done"]
          /\ UNCHANGED << baseline, rollup, queue, time, needRollup, job >>

GetLastDataPoint == /\ pc["generator"] = "GetLastDataPoint"
                    /\ IF rollup = {}
                          THEN /\ needRollup' = baseline
                          ELSE /\ needRollup' = { x \in baseline : x > Max(rollup) }
                    /\ IF needRollup' /= {}
                          THEN /\ \/ /\ pc' = [pc EXCEPT !["generator"] = "Enqueue"]
                                  \/ /\ TRUE
                                     /\ pc' = [pc EXCEPT !["generator"] = "Loop_g"]
                          ELSE /\ pc' = [pc EXCEPT !["generator"] = "Loop_g"]
                    /\ UNCHANGED << baseline, rollup, queue, time, job >>

Enqueue == /\ pc["generator"] = "Enqueue"
           /\ queue' = (queue \union needRollup)
           /\ pc' = [pc EXCEPT !["generator"] = "Loop_g"]
           /\ UNCHANGED << baseline, rollup, time, needRollup, job >>

generator == Loop_g \/ GetLastDataPoint \/ Enqueue

Loop == /\ pc["executor"] = "Loop"
        /\ IF time < 10
              THEN /\ pc' = [pc EXCEPT !["executor"] = "Dequeue"]
              ELSE /\ pc' = [pc EXCEPT !["executor"] = "Done"]
        /\ UNCHANGED << baseline, rollup, queue, time, needRollup, job >>

Dequeue == /\ pc["executor"] = "Dequeue"
           /\ IF queue /= {}
                 THEN /\ job' = Min(queue)
                      /\ queue' = queue \ {job'}
                      /\ pc' = [pc EXCEPT !["executor"] = "Execute"]
                 ELSE /\ pc' = [pc EXCEPT !["executor"] = "Loop"]
                      /\ UNCHANGED << queue, job >>
           /\ UNCHANGED << baseline, rollup, time, needRollup >>

Execute == /\ pc["executor"] = "Execute"
           /\ \/ /\ rollup' = (rollup \union {job})
              \/ /\ TRUE
                 /\ UNCHANGED rollup
           /\ pc' = [pc EXCEPT !["executor"] = "Loop"]
           /\ UNCHANGED << baseline, queue, time, needRollup, job >>

executor == Loop \/ Dequeue \/ Execute

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == cagg \/ generator \/ executor
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-a60ef86e999a1277efb0832da804f4bc

=============================================================================
\* Modification History
\* Last modified Fri Jul 03 13:50:55 PDT 2020 by spencerpearson
\* Created Fri Jul 03 13:42:56 PDT 2020 by spencerpearson
