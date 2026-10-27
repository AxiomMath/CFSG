module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Shape

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local

variable {P : Type} [Group P] [Finite P]

structure BarShape.Spec (zc : P) (W A B A₃ : Subgroup P) : Prop where
  normal_W : W.Normal
  zc_mem : zc ∈ W
  cp : IsCentralProd A B W
  eA : Nonempty (↥A ≃* QuaternionGroup 2)
  eB : Nonempty (↥B ≃* QuaternionGroup 2)
  normal_A : A.Normal
  eA₃ : Nonempty (↥A₃ ≃* Multiplicative (ZMod 3))
  fit : generalizedFitting P = W
  comm_eq : ⁅W, A₃⁆ = W
  fix : ∀ w ∈ W, (∀ a ∈ A₃, a * w = w * a) → w ∈ zpowers zc
  quot : Nonempty ((P ⧸ W) ≃* Equiv.Perm (Fin 3))

theorem BarShape.exists_spec {zc : P} (hP : BarShape P zc) :
    ∃ W A B A₃ : Subgroup P, BarShape.Spec zc W A B A₃ := by
  obtain ⟨W, A, B, A₃, hWn, hzcW, hcp, ⟨eA⟩, ⟨eB⟩, hAn, ⟨eA₃⟩, hF, hWA, hfix, ⟨eq⟩⟩ := hP.data
  exact ⟨W, A, B, A₃, ⟨hWn, hzcW, hcp, ⟨eA⟩, ⟨eB⟩, hAn, ⟨eA₃⟩, hF, hWA, hfix, ⟨eq⟩⟩⟩

theorem q8_cases : ∀ q : QuaternionGroup 2,
    q = 1 ∨ q = QuaternionGroup.a 2 ∨ q * q = QuaternionGroup.a 2 := by decide

theorem q8_involution : ∀ q : QuaternionGroup 2, q ≠ 1 → q * q = 1 → q = QuaternionGroup.a 2 := by
  decide

theorem q8_comm : ∀ q r : QuaternionGroup 2,
    q * r * q⁻¹ * r⁻¹ = 1 ∨ q * r * q⁻¹ * r⁻¹ = QuaternionGroup.a 2 := by decide

namespace BarShape.Spec

variable {zc : P} {W A B A₃ : Subgroup P} (hS : BarShape.Spec zc W A B A₃)
include hS

theorem zpowers_eq (hP : BarShape P zc) : zpowers zc = A ⊓ B := by
  obtain ⟨eA⟩ := hS.eA
  obtain ⟨eB⟩ := hS.eB
  exact zpowers_zc_eq_inf hP.ne_one hP.sq hP.central hS.zc_mem hS.cp hS.normal_A eA eB

theorem zc_mem_A (hP : BarShape P zc) : zc ∈ A := by
  have : zc ∈ zpowers zc := mem_zpowers zc
  rw [hS.zpowers_eq hP] at this
  exact this.1

theorem zc_mem_B (hP : BarShape P zc) : zc ∈ B := by
  have : zc ∈ zpowers zc := mem_zpowers zc
  rw [hS.zpowers_eq hP] at this
  exact this.2

theorem A_cases (hP : BarShape P zc) : ∀ a ∈ A, a = 1 ∨ a = zc ∨ a * a = zc := by
  obtain ⟨eA⟩ := hS.eA
  intro a ha
  have hzA := hS.zc_mem_A hP
  have hz : eA ⟨zc, hzA⟩ = QuaternionGroup.a 2 := by
    apply q8_involution
    · intro h
      have := eA.injective (h.trans (map_one eA).symm)
      exact hP.ne_one (congrArg Subtype.val this)
    · rw [← map_mul]
      have : (⟨zc, hzA⟩ : ↥A) * ⟨zc, hzA⟩ = 1 := Subtype.ext hP.sq
      rw [this, map_one]
  rcases q8_cases (eA ⟨a, ha⟩) with h | h | h
  · left
    exact congrArg Subtype.val (eA.injective (h.trans (map_one eA).symm))
  · right; left
    have := eA.injective (h.trans hz.symm)
    exact congrArg Subtype.val this
  · right; right
    have h2 : eA (⟨a, ha⟩ * ⟨a, ha⟩) = eA ⟨zc, hzA⟩ := by rw [map_mul, h, hz]
    exact congrArg Subtype.val (eA.injective h2)

theorem B_cases (hP : BarShape P zc) : ∀ b ∈ B, b = 1 ∨ b = zc ∨ b * b = zc := by
  obtain ⟨eB⟩ := hS.eB
  intro b hb
  have hzB := hS.zc_mem_B hP
  have hz : eB ⟨zc, hzB⟩ = QuaternionGroup.a 2 := by
    apply q8_involution
    · intro h
      have := eB.injective (h.trans (map_one eB).symm)
      exact hP.ne_one (congrArg Subtype.val this)
    · rw [← map_mul]
      have : (⟨zc, hzB⟩ : ↥B) * ⟨zc, hzB⟩ = 1 := Subtype.ext hP.sq
      rw [this, map_one]
  rcases q8_cases (eB ⟨b, hb⟩) with h | h | h
  · left
    exact congrArg Subtype.val (eB.injective (h.trans (map_one eB).symm))
  · right; left
    have := eB.injective (h.trans hz.symm)
    exact congrArg Subtype.val this
  · right; right
    have h2 : eB (⟨b, hb⟩ * ⟨b, hb⟩) = eB ⟨zc, hzB⟩ := by rw [map_mul, h, hz]
    exact congrArg Subtype.val (eB.injective h2)

theorem comm_A (hP : BarShape P zc) : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = 1 ∨ a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = zc := by
  obtain ⟨eA⟩ := hS.eA
  intro a₁ h₁ a₂ h₂
  have hzA := hS.zc_mem_A hP
  have hz : eA ⟨zc, hzA⟩ = QuaternionGroup.a 2 := by
    apply q8_involution
    · intro h
      have := eA.injective (h.trans (map_one eA).symm)
      exact hP.ne_one (congrArg Subtype.val this)
    · rw [← map_mul]
      have : (⟨zc, hzA⟩ : ↥A) * ⟨zc, hzA⟩ = 1 := Subtype.ext hP.sq
      rw [this, map_one]
  rcases q8_comm (eA ⟨a₁, h₁⟩) (eA ⟨a₂, h₂⟩) with h | h
  · left
    have h' : eA (⟨a₁, h₁⟩ * ⟨a₂, h₂⟩ * ⟨a₁, h₁⟩⁻¹ * ⟨a₂, h₂⟩⁻¹) = eA 1 := by
      simpa only [map_mul, map_inv, map_one] using h
    exact congrArg Subtype.val (eA.injective h')
  · right
    have h' : eA (⟨a₁, h₁⟩ * ⟨a₂, h₂⟩ * ⟨a₁, h₁⟩⁻¹ * ⟨a₂, h₂⟩⁻¹) = eA ⟨zc, hzA⟩ := by
      rw [hz]
      simpa only [map_mul, map_inv] using h
    exact congrArg Subtype.val (eA.injective h')

theorem comm_B (hP : BarShape P zc) : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ * b₂ * b₁⁻¹ * b₂⁻¹ = 1 ∨ b₁ * b₂ * b₁⁻¹ * b₂⁻¹ = zc := by
  obtain ⟨eB⟩ := hS.eB
  intro b₁ h₁ b₂ h₂
  have hzB := hS.zc_mem_B hP
  have hz : eB ⟨zc, hzB⟩ = QuaternionGroup.a 2 := by
    apply q8_involution
    · intro h
      have := eB.injective (h.trans (map_one eB).symm)
      exact hP.ne_one (congrArg Subtype.val this)
    · rw [← map_mul]
      have : (⟨zc, hzB⟩ : ↥B) * ⟨zc, hzB⟩ = 1 := Subtype.ext hP.sq
      rw [this, map_one]
  rcases q8_comm (eB ⟨b₁, h₁⟩) (eB ⟨b₂, h₂⟩) with h | h
  · left
    have h' : eB (⟨b₁, h₁⟩ * ⟨b₂, h₂⟩ * ⟨b₁, h₁⟩⁻¹ * ⟨b₂, h₂⟩⁻¹) = eB 1 := by
      simpa only [map_mul, map_inv, map_one] using h
    exact congrArg Subtype.val (eB.injective h')
  · right
    have h' : eB (⟨b₁, h₁⟩ * ⟨b₂, h₂⟩ * ⟨b₁, h₁⟩⁻¹ * ⟨b₂, h₂⟩⁻¹) = eB ⟨zc, hzB⟩ := by
      rw [hz]
      simpa only [map_mul, map_inv] using h
    exact congrArg Subtype.val (eB.injective h')

omit [Finite P] in
theorem exists_decomp : ∀ w ∈ W, ∃ a ∈ A, ∃ b ∈ B, w = a * b := by
  intro w hw
  have := hS.normal_A
  obtain ⟨hAB, -, -⟩ := hS.cp
  rw [← hAB] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hw
  exact ⟨a, ha, b, hb, rfl⟩

omit [Finite P] in
theorem A_le_W : A ≤ W := by
  obtain ⟨hAB, -, -⟩ := hS.cp
  rw [← hAB]; exact le_sup_left

omit [Finite P] in
theorem B_le_W : B ≤ W := by
  obtain ⟨hAB, -, -⟩ := hS.cp
  rw [← hAB]; exact le_sup_right

omit [Finite P] in
theorem comm_AB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := hS.cp.2.1

omit [Finite P] in
theorem card_W : Nat.card ↥W = 32 := by
  classical
  obtain ⟨eA⟩ := hS.eA
  obtain ⟨eB⟩ := hS.eB
  have := hS.normal_A
  obtain ⟨hAB, hcomm, hcard⟩ := hS.cp
  have hA8 : Nat.card ↥A = 8 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hB8 : Nat.card ↥B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h1 := card_sup_mul_card_inf_of_normal' B A
  rw [sup_comm, hAB, inf_comm, hcard, hA8, hB8] at h1
  omega

theorem sq_W (hP : BarShape P zc) : ∀ w ∈ W, w * w = 1 ∨ w * w = zc := by
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hS.exists_decomp w hw
  have hc : a * b = b * a := hS.comm_AB a ha b hb
  have h1 : a * b * (a * b) = (a * a) * (b * b) := by
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [← hc]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
  rw [h1]
  have hzc := hP.sq
  have hzcc := hP.central
  rcases hS.A_cases hP a ha with h | h | h <;> rcases hS.B_cases hP b hb with h' | h' | h'
  · left; rw [h, h']; simp
  · left; rw [h, h']; simp [hzc]
  · right; rw [h, h']; simp
  · left; rw [h, h']; simp [hzc]
  · left; rw [h, h']; simp [hzc]
  · right; rw [h, h']; simp [hzc]
  · right; rw [h, h']; simp
  · right; rw [h, h']; simp [hzc]
  · left; rw [h, h']; simp [hzc]

end BarShape.Spec

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
