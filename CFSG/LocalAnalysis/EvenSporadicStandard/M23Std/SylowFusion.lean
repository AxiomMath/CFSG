module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G]

theorem exists_conj_sylow_two [Finite G] {C P₁ P₂ : Subgroup G}
    (h₁ : P₁ ≤ C ∧ IsPGroup 2 P₁ ∧ ¬ 2 ∣ P₁.relIndex C)
    (h₂ : P₂ ≤ C ∧ IsPGroup 2 P₂ ∧ ¬ 2 ∣ P₂.relIndex C) :
    ∃ g ∈ C, ∀ x, x ∈ P₂ ↔ g⁻¹ * x * g ∈ P₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP₁C, hP₁p, hidx₁⟩ := h₁
  obtain ⟨hP₂C, hP₂p, hidx₂⟩ := h₂
  have hp₁ : IsPGroup 2 (P₁.subgroupOf C) :=
    hP₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₁C).symm
  have hp₂ : IsPGroup 2 (P₂.subgroupOf C) :=
    hP₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hP₂C).symm
  let S₁ : Sylow 2 ↥C := hp₁.toSylow hidx₁
  let S₂ : Sylow 2 ↥C := hp₂.toSylow hidx₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C S₁ S₂
  refine ⟨g, g.2, fun x => ?_⟩
  by_cases hx : x ∈ C
  · have h1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [mul_assoc]
    have e1 : (⟨x, hx⟩ : ↥C) ∈ (S₂ : Subgroup ↥C) ↔ x ∈ P₂ := Subgroup.mem_subgroupOf
    have e2 : g⁻¹ * ⟨x, hx⟩ * g ∈ (S₁ : Subgroup ↥C) ↔ (g : G)⁻¹ * x * g ∈ P₁ :=
      Subgroup.mem_subgroupOf (H := P₁) (K := C) (h := g⁻¹ * ⟨x, hx⟩ * g)
    rw [← e1, h1]
    exact e2
  · have hxP₂ : x ∉ P₂ := fun h => hx (hP₂C h)
    have hxP₁ : (g : G)⁻¹ * x * g ∉ P₁ := fun h => hx (by
      have := C.mul_mem (C.mul_mem g.2 (hP₁C h)) (C.inv_mem g.2)
      simpa [mul_assoc] using this)
    exact ⟨fun h => absurd h hxP₂, fun h => absurd h hxP₁⟩

theorem exists_mem_normalizer_conj_eq [Finite G] {z z' g : G} {T : Subgroup G}
    (hT : T ≤ centralizer ({z} : Set G) ∧ IsPGroup 2 T ∧
      ¬ 2 ∣ T.relIndex (centralizer ({z} : Set G)))
    (hg : g * z * g⁻¹ = z') (hTz' : ∀ x ∈ T, x * z' = z' * x) :
    ∃ n : G, (∀ x, x ∈ T ↔ n * x * n⁻¹ ∈ T) ∧ n * z * n⁻¹ = z' := by
  classical
  set C : Subgroup G := centralizer ({z} : Set G) with hC
  obtain ⟨hTC, hTp, hTidx⟩ := hT
  let T₀ : Subgroup G := T.comap (MulAut.conj g).toMonoidHom
  have hmemT₀ : ∀ x, x ∈ T₀ ↔ g * x * g⁻¹ ∈ T := fun x => Iff.rfl
  have hT₀C : T₀ ≤ C := by
    intro x hx
    rw [hmemT₀] at hx
    rw [hC, mem_centralizer_singleton_iff]
    have h1 := hTz' _ hx
    rw [← hg] at h1
    have h2 : g * (x * z) * g⁻¹ = g * (z * x) * g⁻¹ := by
      calc g * (x * z) * g⁻¹ = (g * x * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (g * z * g⁻¹) * (g * x * g⁻¹) := h1
        _ = g * (z * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hT₀p : IsPGroup 2 T₀ := by
    intro y
    obtain ⟨k, hk⟩ := hTp ⟨g * (y : G) * g⁻¹, y.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : (g * (y : G) * g⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have : g * ((y : G) ^ 2 ^ k) * g⁻¹ = 1 := by rw [← conj_pow]; exact hk'
    have h2 : (y : G) ^ 2 ^ k = 1 := conj_eq_one_iff.1 this
    simpa using h2
  have hcard : Nat.card T₀ = Nat.card T := by
    refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv (fun a => Iff.rfl))
  have hrel : T₀.relIndex C = T.relIndex C := by
    have h1 := Subgroup.relIndex_mul_card T₀ C
    have h2 := Subgroup.relIndex_mul_card T C
    rw [inf_eq_left.mpr hT₀C] at h1
    rw [inf_eq_left.mpr hTC] at h2
    rw [hcard] at h1
    have hpos : 0 < Nat.card T := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  obtain ⟨c, hcC, hc⟩ := exists_conj_sylow_two (C := C) (P₁ := T) (P₂ := T₀)
    ⟨hTC, hTp, hTidx⟩ ⟨hT₀C, hT₀p, by rw [hrel]; exact hTidx⟩
  refine ⟨g * c, fun x => ?_, ?_⟩
  · have h1 := hc (g⁻¹ * ((g * c) * x * (g * c)⁻¹) * g)
    rw [hmemT₀] at h1
    have e1 : g * (g⁻¹ * ((g * c) * x * (g * c)⁻¹) * g) * g⁻¹ = (g * c) * x * (g * c)⁻¹ := by
      group
    have e2 : c⁻¹ * (g⁻¹ * ((g * c) * x * (g * c)⁻¹) * g) * c = x := by group
    rw [e1, e2] at h1
    exact h1.symm
  · have hcz : c * z * c⁻¹ = z := by
      have := (mem_centralizer_singleton_iff.1 hcC)
      rw [this]
      group
    calc g * c * z * (g * c)⁻¹ = g * (c * z * c⁻¹) * g⁻¹ := by group
      _ = z' := by rw [hcz, hg]

end CFSG.EvenSporadicStandard.M23Std
