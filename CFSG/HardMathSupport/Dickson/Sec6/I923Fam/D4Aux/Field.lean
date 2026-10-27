module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4Aux.Model
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Layer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

section Field


theorem noL2Layer_entrywiseAdjointAut_D4 (hO : LieOrderFormulasInput) {ℓ d : ℕ} (hℓ : ℓ.Prime)
    (hd : 1 ≤ d) {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hk : Nat.card (fixSubfield σ) = ℓ ^ d) :
    NoL2Layer (entrywiseAdjointAut Tag.D4 σ) := by
  classical
  haveI := finite_adjointD4 K
  set β := entrywiseAdjointAut Tag.D4 σ with hβ
  obtain ⟨hs, hnc⟩ := isSimple_adjointD4 (fixSubfield σ)
  obtain ⟨-, -, -, hJΓ, -, hnormal, hcomm⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup Tag.D4 K σ
  have hJA : fixedFieldImage Tag.D4 σ ≤ adjointGroup Tag.D4 K := hJΓ.trans inf_le_left
  have hΓ : ∀ n : ↥(fixSubgroup β), ((n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈
      entrywiseFixedGroup Tag.D4 σ := fun n =>
    ⟨(n : ↥(adjointGroup Tag.D4 K)).2, by
      have h1 : β n = n := n.2
      have := congrArg Subtype.val h1
      rwa [coe_entrywiseAdjointAut] at this⟩
  set J : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (fixedFieldImage Tag.D4 σ).subgroupOf (adjointGroup Tag.D4 K) with hJ
  have hmemJ : ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ J ↔
      (x : ModGL Tag.D4 K) ∈ fixedFieldImage Tag.D4 σ := fun x => Iff.rfl
  have hJC : J ≤ fixSubgroup β := fun x hx => by
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  haveI hJn : (J.subgroupOf (fixSubgroup β)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, hmemJ] at hn ⊢
    have h1 := hnormal.conj_mem ⟨((n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K), hΓ n⟩
      (Subgroup.mem_subgroupOf.2 hn) ⟨((g : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K), hΓ g⟩
    simpa using Subgroup.mem_subgroupOf.1 h1
  let eJ : ↥J ≃* adjointGroup Tag.D4 (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv σ).symm
  haveI := hs
  haveI : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hncJ : ∃ x y : ↥J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (by simpa using congrArg eJ h)⟩
  have hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ J.subgroupOf (fixSubgroup β)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hq := hcomm (QuotientGroup.mk ⟨((x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K), hΓ x⟩)
      (QuotientGroup.mk ⟨((y : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K), hΓ y⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      hmemJ]
    simpa using hq
  exact OrthAux.noL2Layer_of_normal_simple β J hJC hsol inferInstance hncJ fun r hr hT =>
    not_typeL2_adjointD4 hO hℓ hd (fixSubfield σ) hk r hr (l2fld_isTypeL2_of_mulEquiv eJ hT)

end Field

end CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux
