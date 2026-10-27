module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldCore
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.Chevalley.SteinbergBT

section Entrywise


variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem fieldCoreAt_entrywise_of_quasisimple {p : ℕ} {σ : K ≃+* K} (hσp : orderOf σ = p)
    (hJC : fixedFieldImage τ σ ≤ adjointGroup τ K) (hq : CFSG.IsQuasisimple (fixedFieldImage τ σ))
    (hNδ : ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) ≤
      Subgroup.centralizer {entrywiseAdjointAut τ σ})
    (hnormal : ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))).subgroupOf
      (Subgroup.centralizer {entrywiseAdjointAut τ σ})).Normal)
    (hcent : Subgroup.centralizer {entrywiseAdjointAut τ σ} ⊓
        Subgroup.centralizer ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
          (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) :
            Subgroup (MulAut (adjointGroup τ K))) : Set (MulAut (adjointGroup τ K))) =
      Subgroup.zpowers (entrywiseAdjointAut τ σ))
    (hJp : ¬ Nat.Coprime p (Nat.card (adjointGroup τ (fixSubfield σ)))) :
    FieldCoreAt p (entrywiseAdjointAut τ σ) := by
  have : Finite (ModGL τ K) := finite_modGL
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := τ) (K := K))
  have e1 : ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) ≃* fixedFieldImage τ σ :=
    Subgroup.subgroupOfEquivOfLe hJC
  refine fieldCoreAt_of_canonical_quasisimple hinj
    ((orderOf_entrywiseAdjointAut τ.rank_pos σ).trans hσp)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e1.symm hq) hNδ hnormal hcent ?_
  rwa [Nat.card_congr e1.toEquiv, ← Nat.card_congr (fixedFieldImageEquiv σ).toEquiv]

theorem fieldCoreAt_entrywise_of_data {p : ℕ} {σ : K ≃+* K} (hσp : orderOf σ = p)
    (hJC : fixedFieldImage τ σ ≤ adjointGroup τ K) (hsimple : IsSimpleGroup (fixedFieldImage τ σ))
    (hnc : ¬∀ a b : fixedFieldImage τ σ, a * b = b * a)
    (hNδ : ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) ≤
      Subgroup.centralizer {entrywiseAdjointAut τ σ})
    (hnormal : ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))).subgroupOf
      (Subgroup.centralizer {entrywiseAdjointAut τ σ})).Normal)
    (hcent : Subgroup.centralizer {entrywiseAdjointAut τ σ} ⊓
        Subgroup.centralizer ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
          (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) :
            Subgroup (MulAut (adjointGroup τ K))) : Set (MulAut (adjointGroup τ K))) =
      Subgroup.zpowers (entrywiseAdjointAut τ σ))
    (hJp : ¬ Nat.Coprime p (Nat.card (adjointGroup τ (fixSubfield σ)))) :
    FieldCoreAt p (entrywiseAdjointAut τ σ) :=
  have : IsSimpleGroup (fixedFieldImage τ σ) := hsimple
  fieldCoreAt_entrywise_of_quasisimple hσp hJC (isQuasisimple_of_simple_nonabelian hnc) hNδ
    hnormal hcent hJp

end Entrywise

end CFSG.HardMathSupport.Timmesfeld.CrossChar
