module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56QuotSub
public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Commute
public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Frame

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (SylowFrame)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem exists_not_weakly_closed {T S : Subgroup G}
    (hS : SylowFrame J T S) (hncent : ¬ ∀ t ∈ T, ∀ v ∈ blockU J, t * v = v * t)
    (hQV : S ⊓ Subgroup.normalizer (T : Set G) ⊓ J ≤ blockU J) :
    ∃ y ∈ J, rightConjugate (S ⊓ Subgroup.normalizer (T : Set G)) y ≤ S ∧
      rightConjugate (S ⊓ Subgroup.normalizer (T : Set G)) y ≠
        S ⊓ Subgroup.normalizer (T : Set G) := by
  by_contra hcon
  push Not at hcon
  apply hncent
  have hJ := c.block
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hS.le_normalizer
  have hH : J ⊔ T ≤ Subgroup.normalizer (oTwoIn J : Set G) :=
    sup_le (SixThree.le_normalizer_oTwoIn J)
      (hTN.trans (SixThree.normalizer_le_normalizer_oTwoIn J))
  have : ((oTwoIn J).subgroupOf (J ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer ((oTwoIn_le J).trans le_sup_left)).2 hH
  have hOS : oTwoIn J ≤ S :=
    QBlock.le_of_isPGroup_normal' hS.sylow ((oTwoIn_le J).trans le_sup_left) hH
      (SixThree.isPGroup_oTwoIn J)
  have hWTO : S ⊓ Subgroup.normalizer (T : Set G) ≤ T ⊔ oTwoIn J := by
    intro x hx
    obtain ⟨t, ht, q, hq, rfl⟩ := X_decomp hS hx
    exact Subgroup.mul_mem_sup ht (blockU_le_oTwoIn J (hQV hq))
  have hO2 : ⁅J, T⁆ ≤ oTwoIn J :=
    commutator_le_of_weakly_closed_sub le_sup_left le_sup_right hS.sylow.le (oTwoIn_le J) hOS hH
      hTN hS.inf_eq_bot hS.isPGroup rfl hS.sylow hS.le (le_inf hS.le Subgroup.le_normalizer)
      inf_le_left hWTO hcon (isQuasisimple_image hJ le_sup_left)
  exact c.commutes_of_commutator_le hS.isPGroup hTN (c.commutator_le_blockU_of_le_oTwoIn hTN hO2)

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
