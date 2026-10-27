module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Facts
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.List93

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem suzuki_holds : ∀ (S : Type) [Group S] [Finite S], catalogIs S szIdx →
    ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 5 E → Nat.card E < 5 ^ 3 := by
  intro S _ _ hS E hE
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  cases i with
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    have hd : d1 = TauCeti.LieTypeIndex.suzuki 2 := hi
    subst hd
    have hB : Nat.card E ≤ 5 ^ 2 :=
      CFSG.LocalAnalysis.RankFourTheoremC.autRankTwoAt_suzuki (d := ⟨_, hv⟩) rfl S ⟨e⟩ E hE
    exact lt_of_le_of_lt hB (by norm_num)
  | cyclic p h => exact False.elim hi
  | alternating n h => exact False.elim hi
  | sporadic s => exact False.elim hi

end Certs

end CFSG.LocalAnalysis.GLTheoremA.List93

end
