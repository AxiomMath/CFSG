module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GroupActions

open scoped commutatorElement

theorem core_free_maximal_normal_sylow {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hM : IsCoatom M) (hcore : M.normalCore = ⊥) {p : ℕ} [Fact p.Prime] (P : Sylow p M)
    (hPn : (P : Subgroup M).Normal) (hP1 : (P : Subgroup M) ≠ ⊥) :
    Subgroup.normalizer (((P : Subgroup M).map M.subtype : Subgroup G) : Set G) = M ∧
      ∃ Q : Sylow p G, (Q : Subgroup G) = (P : Subgroup M).map M.subtype := by
  set P' : Subgroup G := (P : Subgroup M).map M.subtype with hP'
  have hle : P' ≤ M := Subgroup.map_subtype_le _
  have hmemP : ∀ m : M, (m : G) ∈ P' ↔ m ∈ (P : Subgroup M) := fun m =>
    ⟨fun ⟨y, hy, hym⟩ => by rwa [Subtype.ext hym] at hy, fun h => ⟨m, h, rfl⟩⟩
  have hMN : M ≤ Subgroup.normalizer (P' : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, hPn.conj_mem y hy _, rfl⟩
    · intro hx
      have hxM : x ∈ M := by
        have h1 := mul_mem (mul_mem (inv_mem hm) (hle hx)) hm
        simpa [mul_assoc] using h1
      have h2 : (⟨m, hm⟩ * ⟨x, hxM⟩ * (⟨m, hm⟩ : M)⁻¹ : M) ∈ (P : Subgroup M) :=
        (hmemP _).1 hx
      have h3 := hPn.conj_mem _ h2 (⟨m, hm⟩ : M)⁻¹
      have h4 : (⟨m, hm⟩ : M)⁻¹ * (⟨m, hm⟩ * ⟨x, hxM⟩ * (⟨m, hm⟩ : M)⁻¹) * (⟨m, hm⟩ : M)⁻¹⁻¹ =
          ⟨x, hxM⟩ := by group
      rw [h4] at h3
      exact (hmemP ⟨x, hxM⟩).2 h3
  have hnorm : Subgroup.normalizer (P' : Set G) = M := by
    rcases hMN.lt_or_eq with hlt | heq
    · exfalso
      have htop := hM.2 _ hlt
      have hPnG : P'.Normal := Subgroup.normalizer_eq_top_iff.1 htop
      have hbot : P' ≤ M.normalCore := Subgroup.normal_le_normalCore.2 hle
      rw [hcore, le_bot_iff] at hbot
      exact hP1 ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1 hbot)
    · exact heq.symm
  refine ⟨hnorm, ?_⟩
  have hpP : IsPGroup p P' := P.isPGroup'.map M.subtype
  obtain ⟨Q, hPQ⟩ := hpP.exists_le_sylow
  refine ⟨Q, le_antisymm ?_ hPQ⟩
  by_contra hQP
  have hlt : P'.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hQP fun q hq => ?_
    have : (⟨q, hq⟩ : Q) ∈ P'.subgroupOf Q := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (P'.subgroupOf Q) hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hPQ] at hnc
  obtain ⟨⟨x, hxQ⟩, hxN, hxP⟩ := IsConcreteLE.exists_of_lt hnc
  rw [Subgroup.mem_subgroupOf] at hxN hxP
  have hxM : x ∈ M := hnorm ▸ hxN
  have hK : IsPGroup p (Q ⊓ M : Subgroup G) := Q.isPGroup'.to_le inf_le_left
  have hsup : IsPGroup p (P' ⊔ (Q ⊓ M) : Subgroup G) :=
    hpP.to_sup_of_normal_left' hK (hnorm ▸ inf_le_right)
  have hsupM : P' ⊔ (Q ⊓ M) ≤ M := sup_le hle inf_le_right
  have hsub : IsPGroup p ((P' ⊔ (Q ⊓ M)).subgroupOf M) :=
    hsup.of_equiv (Subgroup.subgroupOfEquivOfLe hsupM).symm
  obtain ⟨S, hS⟩ := hsub.exists_le_sylow
  have : Unique (Sylow p M) := Sylow.unique_of_normal P hPn
  have hSP : S = P := Subsingleton.elim S P
  subst hSP
  have hxT : (⟨x, hxM⟩ : M) ∈ (P' ⊔ (Q ⊓ M)).subgroupOf M :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right ⟨hxQ, hxM⟩)
  exact hxP ((hmemP ⟨x, hxM⟩).2 (hS hxT))

theorem additive_scaling_commutator {R Γ : Type*} [CommRing R] [Group Γ]
    (u : Multiplicative R →* Γ) (h : Γ) (lam mu : R) (hmu : mu * (lam - 1) = 1)
    (hconj : ∀ a : R, h * u (Multiplicative.ofAdd a) * h⁻¹ = u (Multiplicative.ofAdd (lam * a)))
    (a : R) :
    u (Multiplicative.ofAdd a) =
        h * u (Multiplicative.ofAdd (mu * a)) * h⁻¹ * (u (Multiplicative.ofAdd (mu * a)))⁻¹ ∧
      u (Multiplicative.ofAdd a) ∈ commutator Γ := by
  have key : u (Multiplicative.ofAdd a) =
      h * u (Multiplicative.ofAdd (mu * a)) * h⁻¹ * (u (Multiplicative.ofAdd (mu * a)))⁻¹ := by
    rw [hconj, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
    congr 2
    linear_combination (-a) * hmu
  refine ⟨key, ?_⟩
  rw [key, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top h) (Subgroup.mem_top _)

end CFSG.GroupActions
