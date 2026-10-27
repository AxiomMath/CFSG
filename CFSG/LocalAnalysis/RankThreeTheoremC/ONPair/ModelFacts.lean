module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.Words

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier
open scoped commutatorElement


@[expose] noncomputable def qP (i : Fin 4) : Pv := ⟨hval qWords[i.val]!, hval_mem _⟩

@[expose] noncomputable def tOut : Pv := ⟨hval tWord, hval_mem _⟩

@[expose] noncomputable def qtGen (h : ℕ) : Pv :=
  if h = 0 then qP 0 else if h = 1 then qP 1 else if h = 2 then qP 2 else tOut

@[expose] noncomputable def b1P : Pv := ⁅qP 0, qP 2⁆

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
