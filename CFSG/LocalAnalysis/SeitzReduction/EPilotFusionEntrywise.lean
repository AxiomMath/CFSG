module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Basic
public import CFSG.LocalAnalysis.SeitzReduction.Fusion
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.F4Pilot (PerfectTwistedFusion)

variable {K : Type} [Field K]

theorem exists_ringEquiv_apply_eq_pow_two_pow {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ (2 * e)) : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ e := by
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * e) hK
  refine ⟨fr ^ e, fun c => ?_⟩
  clear hK he
  induction e with
  | zero => rw [pow_zero, RingAut.one_apply, pow_zero, pow_one]
  | succ n ih => rw [pow_succ', RingAut.mul_apply, ih, hfr, ← pow_mul, ← pow_succ]


variable {τ : Tag}

section Entrywise

variable (τ) in
noncomputable abbrev pinnedElt (α : Fin τ.rank → ℤ) (c : K) : adjointGroup τ K :=
  ⟨pinnedX τ K α c, pinnedX_mem_adjointGroup α c⟩

theorem entrywiseAdjointAut_pinnedElt (σ : K ≃+* K) (α : Fin τ.rank → ℤ) (c : K) :
    entrywiseAdjointAut τ σ (pinnedElt τ α c) = pinnedElt τ α (σ c) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_entrywiseAdjointAut]
  exact entrywise_pinnedX σ.toRingHom α c

theorem entrywiseAdjointAut_eq_self_of_mem_fixedFieldImage (σ : K ≃+* K)
    {g : adjointGroup τ K} (hg : (g : ModGL τ K) ∈ fixedFieldImage τ σ) :
    entrywiseAdjointAut τ σ g = g :=
  Subtype.ext (by
    rw [coe_entrywiseAdjointAut]
    exact (mem_entrywiseFixedGroup.1 (fixedFieldImage_le hg)).2)

private theorem fixedFieldImage_le_adjointGroup' (σ : K ≃+* K) :
    fixedFieldImage τ σ ≤ adjointGroup τ K := fun _ hg =>
  (mem_entrywiseFixedGroup.1 (fixedFieldImage_le hg)).1

theorem commutator_fixedFieldImage_subgroupOf (σ : K ≃+* K)
    (hperf : Group.IsPerfect (adjointGroup τ (fixSubfield σ))) :
    ⁅(fixedFieldImage τ σ).subgroupOf (adjointGroup τ K),
        (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)⁆ =
      (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) := by
  have hJ : Group.IsPerfect (fixedFieldImage τ σ) :=
    Group.IsPerfect.map (H := adjointGroup τ (fixSubfield σ))
      (baseChangeGL (fixSubfield σ).subtype)
  exact commutator_subgroupOf_eq_self (fixedFieldImage_le_adjointGroup' σ)
    Subgroup.commutator_eq_self

end Entrywise

section Fusion

theorem perfectTwistedFusion_entrywise [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c)
    (hσ1 : ∃ c, σ c ≠ c) (hperf : Group.IsPerfect (adjointGroup τ (fixSubfield σ))) :
    PerfectTwistedFusion (entrywiseAdjointAut τ σ) := by
  obtain ⟨c, hc⟩ := hσ1
  have hi : 0 < τ.rank := by cases τ <;> decide
  set α : Fin τ.rank → ℤ := Pi.single ⟨0, hi⟩ 1 with hαdef
  have hxadd : ∀ a b : K, pinnedElt τ α (a + b) = pinnedElt τ α a * pinnedElt τ α b := fun a b =>
    Subtype.ext (pinnedX_add τ K α a b)
  have hxinv : ∀ a : K, (pinnedElt τ α a)⁻¹ = pinnedElt τ α (-a) := fun a =>
    Subtype.ext (pinnedX_neg τ K α a)
  have hx0 : pinnedElt τ α (0 : K) = 1 := Subtype.ext (pinnedX_zero τ K α)
  have hxinj : Function.Injective (pinnedElt τ α : K → adjointGroup τ K) := fun a b h =>
    pinnedX_injective τ K α (congrArg Subtype.val h)
  refine ⟨pinnedElt τ α c, pinnedElt τ α (σ c + c), fun h1 => hc ?_, ?_,
    (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K),
    commutator_fixedFieldImage_subgroupOf σ hperf, ?_, fun p hp =>
      entrywiseAdjointAut_eq_self_of_mem_fixedFieldImage σ (mem_subgroupOf.1 hp)⟩
  · have h0 : σ c + c = 0 := hxinj (h1.trans hx0.symm)
    exact CharTwo.add_eq_zero.1 h0
  · rw [entrywiseAdjointAut_pinnedElt, hxinv, ← hxadd, CharTwo.neg_eq]
  · refine mem_subgroupOf.2 (pinnedX_mem_fixedFieldImage α ?_)
    rw [map_add, hσ, add_comm]

theorem perfectTwistedFusion_entrywise_of_singleEdge [CharP K 2]
    (hτ : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) (hσ1 : ∃ c, σ c ≠ c) :
    PerfectTwistedFusion (entrywiseAdjointAut τ σ) :=
  perfectTwistedFusion_entrywise σ hσ hσ1
    (Group.isPerfect_def.2 (single_edge_perfect τ (fixSubfield σ) hτ))

theorem perfectTwistedFusion_entrywise_frobenius [Finite K] [CharP K 2]
    (hτ : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    PerfectTwistedFusion (entrywiseAdjointAut τ σ) := by
  have hK' : Nat.card K = (2 ^ e) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  refine perfectTwistedFusion_entrywise_of_singleEdge hτ σ (fun c => ?_) ?_
  · rw [hσ, hσ]
    exact pow_pow_eq_self_of_natCard_eq_sq hK' c
  · by_contra! h
    have hle := natCard_le_of_forall_pow_eq_self (Nat.one_lt_two_pow (by omega : e ≠ 0))
      (Set.univ : Set K) fun a _ => (hσ a).symm.trans (h a)
    rw [Nat.card_univ, hK] at hle
    have hlt : 2 ^ e < 2 ^ (2 * e) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end Fusion

end CFSG.SeitzReduction.EPilot
