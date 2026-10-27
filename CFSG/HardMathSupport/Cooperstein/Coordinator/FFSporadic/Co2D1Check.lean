module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2SlpCheck
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D1Data

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Schreier

set_option compiler.extract_closed false

@[expose] def d1Base (_ : Unit := ()) : Array (Array ℕ) := aArrs ++ #[zArr, tArr] ++ cArrs ++ dArrs

@[expose] def d1StageOK (A : Array (Array ℕ)) (st : D1Stage) : Bool :=
  slpTargets (selArr A st.gens) st.slp [(st.w0, aArrs[0]!), (st.w1, aArrs[1]!)]

@[expose] def d1Check (_ : Unit := ()) : Bool :=
  slpOK (d1Base ()) d1SlpA d1EqsA d1NesA &&
    (let A := slpFinal (d1Base ()) d1SlpA
     d1StageOK A d1Stage1 && d1StageOK A d1Stage2 && d1StageOK A d1Stage3)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2
