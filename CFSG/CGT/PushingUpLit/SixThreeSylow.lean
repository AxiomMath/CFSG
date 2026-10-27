module

public import CFSG.CGT.PushingUpLit.SixThreeShort
public import CFSG.CGT.PushingUpLit.NineChoiceJ
public import CFSG.GroupTheory.ConjugatePairSubnormality

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement Pointwise

namespace SixThree

variable {G : Type} [Group G]

theorem eq_of_le_isPGroup [Finite G] {Y R P : Subgroup G} (hNo : SubTwo.NoTwoQuotient Y)
    (hR : IsSylowOf 2 R (centralizerModCore Y)) (hYR : Y ≤ Subgroup.normalizer (R : Set G))
    (hsub : (Y.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal) (hP : IsPGroup 2 P)
    (hYP : Y ≤ Subgroup.normalizer (P : Set G)) (hRP : R ≤ P) : R = P := by
  refine Nine.eq_of_inf_normalizer_le hP hRP ?_
  set P₁ : Subgroup G := P ⊓ Subgroup.normalizer (R : Set G) with hP₁
  have hP₁2 : IsPGroup 2 P₁ := hP.to_le inf_le_left
  have hYP₁ : Y ≤ Subgroup.normalizer (P₁ : Set G) :=
    le_trans (le_inf hYP (hYR.trans Subgroup.le_normalizer))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hYP₁R : Y ⊔ P₁ ≤ Subgroup.normalizer (R : Set G) := sup_le hYR inf_le_right
  have hsub' : (Y.subgroupOf (Y ⊔ P₁)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hYP₁R hsub
  have hP₁Y : P₁ ≤ Subgroup.normalizer (Y : Set G) :=
    SubTwo.le_normalizer_of_isSubnormal_sup hNo hP₁2 hYP₁ hsub'
  have hP₁C : P₁ ≤ centralizerModCore Y := by
    intro g hg
    refine ⟨hP₁Y hg, fun x hx => ?_⟩
    have hM : ⁅P₁, Y⁆ ≤ oTwoIn Y := by
      refine le_oTwoIn_of_isPGroup (N := ⁅P₁, Y⁆) ?_ ?_ ?_
      · rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_left.mp hP₁Y
      · exact hP₁2.to_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hYP₁)
      · exact Subgroup.normalizer_commutator_ge_right P₁ Y
    exact hM (Subgroup.commutator_mem_commutator hg hx)
  exact Nine.le_of_isSylowOf_of_le hR hP₁2 (le_inf hRP Subgroup.le_normalizer) hP₁C

theorem normal_le_of_isSylowOf [Finite G] {Y R Q : Subgroup G} [Q.Normal]
    (hNo : SubTwo.NoTwoQuotient Y) (hR : IsSylowOf 2 R (centralizerModCore Y))
    (hYR : Y ≤ Subgroup.normalizer (R : Set G))
    (hsub : (Y.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal) (hQ : IsPGroup 2 Q) :
    Q ≤ R := by
  have hQR : IsPGroup 2 (Q ⊔ R : Subgroup G) := hQ.to_sup_of_normal_left hR.2.1
  have hYQR : Y ≤ Subgroup.normalizer ((Q ⊔ R : Subgroup G) : Set G) :=
    le_trans (le_inf (by rw [Subgroup.normalizer_eq_top Q]; exact le_top) hYR)
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have h := eq_of_le_isPGroup hNo hR hYR hsub hQR hYQR le_sup_right
  exact le_sup_left.trans h.ge

end SixThree

end CFSG.CGT.PushingUpLit
