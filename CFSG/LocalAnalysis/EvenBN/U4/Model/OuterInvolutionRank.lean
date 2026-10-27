module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolution
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Involutions

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Model

theorem exists_conj_mem_miyamotoA1 {s : GL (Fin 4) K} (hs : s ∈ gramSU h (miyamotoJ4 K))
    (hs2 : s * s = 1) : ∃ k ∈ gramSU h (miyamotoJ4 K), k⁻¹ * s * k ∈ miyamotoA1 h := by
  have : CharP K 2 := h.charP
  by_cases hs1 : s = 1
  · exact ⟨1, one_mem _, by rw [hs1, inv_one, one_mul, one_mul]; exact one_mem _⟩
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [sq, hs2]) hs1
  obtain ⟨g₁, hg₁, hp⟩ := exists_conj_mem_P h hs hord
  have hp2 : g₁⁻¹ * s * g₁ * (g₁⁻¹ * s * g₁) = 1 := by
    rw [show g₁⁻¹ * s * g₁ * (g₁⁻¹ * s * g₁) = g₁⁻¹ * (s * s) * g₁ by group, hs2]
    group
  obtain ⟨g₂, hg₂, hA⟩ := exists_conj_mem_A1 h hp hp2
  refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, ?_⟩
  rw [show (g₁ * g₂)⁻¹ * s * (g₁ * g₂) = g₂⁻¹ * (g₁⁻¹ * s * g₁) * g₂ by group]
  exact hA

theorem conj_conj_eq_of_conj_mem_miyamotoA1 {s k a : GL (Fin 4) K}
    (hk : k⁻¹ * s * k ∈ miyamotoA1 h) (ha : a ∈ miyamotoA1 h) :
    s * (k * a * k⁻¹) * s⁻¹ = k * a * k⁻¹ := by
  have hcomm := miyamotoA1_mul_comm h hk ha
  calc s * (k * a * k⁻¹) * s⁻¹ = k * ((k⁻¹ * s * k) * a) * (k⁻¹ * s * k)⁻¹ * k⁻¹ := by group
    _ = k * (a * (k⁻¹ * s * k)) * (k⁻¹ * s * k)⁻¹ * k⁻¹ := by rw [hcomm]
    _ = k * a * k⁻¹ := by group

theorem map_conj_le_and_fixes {s : gramSU h (miyamotoJ4 K)} {k : GL (Fin 4) K}
    (hkS : k ∈ gramSU h (miyamotoJ4 K)) (hk : k⁻¹ * (s : GL (Fin 4) K) * k ∈ miyamotoA1 h)
    {M : Subgroup (GL (Fin 4) K)} (hM : M ≤ miyamotoA1 h) :
    M.map (MulAut.conj k).toMonoidHom ≤ gramSU h (miyamotoJ4 K) ∧
      ∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ M.map (MulAut.conj k).toMonoidHom →
        MulAut.conj s g = g := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem hkS (miyamotoUnipotent_le_SU h true false (hM ha))) (inv_mem hkS)
  · rintro g ⟨a, ha, hga⟩
    apply Subtype.ext
    have hga' : (g : GL (Fin 4) K) = k * a * k⁻¹ := hga.symm
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hga']
    exact conj_conj_eq_of_conj_mem_miyamotoA1 h hk (hM ha)

theorem exists_elementaryAbelian_fixed_of_mul_self {α : MulAut (gramSU h (miyamotoJ4 K))}
    (hα : α * α = 1) :
    ∃ E : Subgroup (GL (Fin 4) K), E ≤ gramSU h (miyamotoJ4 K) ∧
      (∀ g : gramSU h (miyamotoJ4 K), (g : GL (Fin 4) K) ∈ E → α g = g) ∧
        CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = (2 ^ f) ^ 3 := by
  by_cases hσ : miyamotoFieldFactor h α = 1
  · obtain ⟨s, rfl⟩ := (miyamotoFieldFactor_eq_one_iff h α).1 hσ
    have hs : s * s = 1 := by rw [← conj_eq_one_iff h, map_mul]; exact hα
    have : CFSG.IsElementaryAbelian 2 (miyamotoA1Bar h) := isElementaryAbelian_miyamotoA1Bar h
    obtain ⟨k, hkS, hk⟩ := exists_conj_mem_miyamotoA1 h s.2 (congrArg Subtype.val hs)
    obtain ⟨hES, hfix⟩ := map_conj_le_and_fixes h hkS hk (M := miyamotoA1Bar h) inf_le_left
    exact ⟨_, hES, hfix, CFSG.IsElementaryAbelian.map _,
      by rw [card_map_of_injective (MulAut.conj k).injective, card_miyamotoA1Bar]⟩
  · refine exists_elementaryAbelian_fixed_of_outer h ?_ hσ
    refine orderOf_eq_prime (by rw [sq, hα]) fun h1 => hσ ?_
    rw [h1, map_one]

theorem exists_elementaryAbelian_fixed_of_mulEquiv {X : Type*} [Group X]
    (ψ : X ≃* gramSU h (miyamotoJ4 K)) {α : MulAut X} (hα : α * α = 1) :
    ∃ E : Subgroup X, (∀ x ∈ E, α x = x) ∧ CFSG.IsElementaryAbelian 2 E ∧
      Nat.card E = (2 ^ f) ^ 3 := by
  set β : MulAut (gramSU h (miyamotoJ4 K)) := MulAut.congr ψ α with hβ
  have hβ2 : β * β = 1 := by rw [hβ, ← map_mul, hα, map_one]
  obtain ⟨E₀, hE₀S, hfix, hE₀e, hE₀c⟩ := exists_elementaryAbelian_fixed_of_mul_self h hβ2
  have : CFSG.IsElementaryAbelian 2 E₀ := hE₀e
  set E₁ : Subgroup (gramSU h (miyamotoJ4 K)) := E₀.subgroupOf (gramSU h (miyamotoJ4 K))
  have hE₁c : Nat.card E₁ = Nat.card E₀ := Nat.card_congr (subgroupOfEquivOfLe hE₀S).toEquiv
  have : CFSG.IsElementaryAbelian 2 E₁ := by
    refine isElementaryAbelian_two_of_forall (fun x hx y hy => ?_) fun x hx => ?_
    · have e : (x : GL (Fin 4) K) * y = y * x :=
        congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E₀) ⟨y, hy⟩)
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, e])
    · have := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E₀) (p := 2) (x : GL (Fin 4) K) hx
      exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, this, Subgroup.coe_one])
  refine ⟨E₁.map ψ.symm.toMonoidHom, ?_, CFSG.IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    have hg' := hfix g hg
    rw [hβ, MulAut.congr_apply] at hg'
    apply ψ.injective
    simpa using hg'
  · rw [card_map_of_injective ψ.symm.injective, hE₁c, hE₀c]

end Model

end CFSG.LocalAnalysis.EvenBN.U4
