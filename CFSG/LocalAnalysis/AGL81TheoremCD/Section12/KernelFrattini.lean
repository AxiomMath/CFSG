module

public import CFSG.LocalAnalysis.RankThreeUC.WeakClosure.WeakClosureSetting
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.FrattiniAux
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem kerIn_normal (M K : Subgroup G) :
    ((CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn M K).subgroupOf K).Normal :=
  (Subgroup.normal_subgroupOf_iff (H := CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn M K)
    (K := K) (CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_left M K)).mpr <| by
    intro h k hh hk
    obtain ⟨hhK, hhM⟩ := CFSG.LocalAnalysis.RankThreeUC.WeakClosure.mem_kerIn.1 hh
    rw [CFSG.LocalAnalysis.RankThreeUC.WeakClosure.mem_kerIn]
    refine ⟨K.mul_mem (K.mul_mem hk hhK) (K.inv_mem hk), fun j hj => ?_⟩
    have := hhM (j * k) (K.mul_mem hj hk)
    simpa [mul_assoc] using this

theorem not_dvd_card_of_le_kerIn {d : ℕ} [Fact d.Prime] {M H J : Subgroup G} {p : ℕ}
    (hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M) (hJM : ¬ J ≤ M)
    (hsub : (xSub p M H ⊓ M : Subgroup G) ≤ CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn M J) :
    ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G) := by
  intro hd
  exact not_dvd_card_of_normal_le hstr hJM (kerIn_normal M J)
    (CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_left M J)
    (CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_right M J)
    (dvd_trans hd (Subgroup.card_dvd_of_le hsub))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
