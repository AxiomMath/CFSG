module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ModelFacts
public import CFSG.RankThree.Native.ONSevenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.RankThree.Native


@[expose] noncomputable def onLine (j : ℕ) : Pv :=
  ⟨onSevenLine ⟨j % 57, Nat.mod_lt _ (by norm_num)⟩, onSeven_mem_P.2.1 _⟩

@[expose] noncomputable def planeC (j : ℕ) : Pv :=
  (⟨evalS planeU[j]!, evalS_mem _⟩ : Pv)⁻¹ * ⟨hval planeM[j]!, hval_mem _⟩

@[expose] noncomputable def planeYA (α : Pv ≃* Pv) (j i : ℕ) : Pv :=
  if j < 14 then onLine i else α (onLine i)

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
