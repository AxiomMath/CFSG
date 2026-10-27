module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem mem_sylow_of_centralizes (S : Sylow p X) {t : X} (ht : IsPGroup p (zpowers t))
    (hS : (S : Subgroup X) ≤ centralizer ({t} : Set X)) : t ∈ (S : Subgroup X) := by
  have hcomm : ∀ s ∈ (S : Subgroup X), s * t = t * s := fun s hs =>
    mem_centralizer_singleton_iff.mp (hS hs)
  have hnorm : t ∈ normalizer (S : Set X) := by
    rw [mem_set_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe]
    constructor
    · intro hh
      have h2 : t * h * t⁻¹ = h := by
        have := hcomm h hh
        calc t * h * t⁻¹ = (t * h) * t⁻¹ := rfl
          _ = (h * t) * t⁻¹ := by rw [this]
          _ = h := by group
      rw [h2]; exact hh
    · intro hh
      have h2 : t⁻¹ * (t * h * t⁻¹) * t = h := by group
      have := hcomm _ hh
      have h3 : t⁻¹ * (t * h * t⁻¹) * t = t * h * t⁻¹ := by
        calc t⁻¹ * (t * h * t⁻¹) * t = t⁻¹ * ((t * h * t⁻¹) * t) := by group
          _ = t⁻¹ * (t * (t * h * t⁻¹)) := by rw [this]
          _ = t * h * t⁻¹ := by group
      rw [← h2, h3]; exact hh
  have h1 := ht.inf_normalizer_sylow S
  have hmem : t ∈ zpowers t ⊓ normalizer (S : Set X) := ⟨mem_zpowers t, hnorm⟩
  rw [h1] at hmem
  exact hmem.2

theorem exists_sylow_subgroupOf_eq (K : Subgroup X) [K.Normal] (S : Sylow p X) :
    ∃ P : Sylow p K, (P : Subgroup K) = (S : Subgroup X).subgroupOf K := by
  obtain ⟨P₀⟩ : Nonempty (Sylow p K) := inferInstance
  obtain ⟨Q, hQ⟩ := P₀.exists_comap_subtype_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q S
  have hcardQ : Nat.card ((Q : Subgroup X).subgroupOf K) = p ^ (Nat.card K).factorization p := by
    have : (Q : Subgroup X).subgroupOf K = (P₀ : Subgroup K) := by rw [← hQ]; rfl
    rw [this]; exact P₀.card_eq_multiplicity
  have hS : ∀ x : X, x ∈ (S : Subgroup X) ↔ g⁻¹ * x * g ∈ (Q : Subgroup X) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, MulAut.conj_apply]
  have hcardS : Nat.card ((S : Subgroup X).subgroupOf K) =
      Nat.card ((Q : Subgroup X).subgroupOf K) := by
    refine Nat.card_congr ((MulAut.conjNormal g : MulAut K).toEquiv.subtypeEquiv fun k => ?_).symm
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show (k : X) ∈ (Q : Subgroup X) ↔ ((MulAut.conjNormal g k : K) : X) ∈ (S : Subgroup X)
    rw [hS]
    have h1 : ((MulAut.conjNormal g k : K) : X) = g * k * g⁻¹ := rfl
    have h2 : g⁻¹ * (g * (k : X) * g⁻¹) * g = k := by group
    rw [h1, h2]
  exact ⟨Sylow.ofCard _ (hcardS.trans hcardQ), rfl⟩

omit [Finite X] in
theorem mem_smul_sylow_iff (g : X) (P : Sylow p X) (x : X) :
    x ∈ ((g • P : Sylow p X) : Subgroup X) ↔ g⁻¹ * x * g ∈ (P : Subgroup X) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, MulAut.conj_apply]

end CFSG.HardMathSupport.Foote.E27
