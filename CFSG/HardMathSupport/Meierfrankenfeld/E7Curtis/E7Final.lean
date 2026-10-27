module

public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.E7Survivor132
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Survivor56

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding CFSG.HardMathSupport.Cooperstein.Coordinator TauCeti

theorem noIrrFFOffender_E7 (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) (hq : q.p = 2) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.E7 q, hv⟩).Group :=
  noIrrFFOffender_E7_of_survivors
    (fun _ _ _ _ _ hn hK => CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.e7SurvivorBound_n7
      hn hK)
    (fun _ _ _ _ _ hn hK => e7SurvivorBound_n1 hn hK) q hv hq

end CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis
