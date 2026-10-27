module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardAutRank
import CFSG.LocalAnalysis.ComponentClassification.Walter86.NormalPerfectRank

public section

namespace CFSG.ComponentClassification.GS79bSec5

open CFSG Subgroup

theorem pRank_le_two_mul_add_pRank_inf_centralizer_of_psl_three
    {G : Type} [Group G] [Finite G] {A H : Subgroup G} (hA : Group.IsPerfect A) {m : ℕ}
    (hm : 2 ≤ m) (hX : Blueprint.LieModel (A ⧸ center A) .PSL 3 2 m)
    (hH : H ≤ normalizer (A : Set G)) :
    Open.pRank 2 H ≤ 2 * m + Open.pRank 2 (H ⊓ centralizer (A : Set G)) := by
  have : Finite (MulAut (A ⧸ center A)) :=
    Finite.of_injective (fun f : MulAut (A ⧸ center A) => (f : A ⧸ center A → A ⧸ center A))
      fun f g h => MulEquiv.ext (congrFun h)
  have h := Walter86.NormalPerfectRank.pRank_le_inf_centralizer_add_mulAut_centerQuotient_of_perfect
    Nat.prime_two hH hA.commutator_eq_top
  rw [← SectionRank.pRank_eq_open_pRank_top] at h
  have hc := pRank_mulAut_le_two_mul_of_lieModel_psl_three hm hX
  omega

end CFSG.ComponentClassification.GS79bSec5
