module

public import CFSG.ClassicalInvolution.Q3.TL4S3DichB
public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.S3Dich

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.Chevalley
open scoped MatrixGroups

theorem exists_sylow_comap {A B : Type} [Group A] [Group B] (Φ : A →* B)
    (hΦ : Function.Injective Φ) {L : Subgroup B} (hL : IsSylow2In L Φ.range) :
    ∃ P : Sylow 2 A, (P : Subgroup A) = L.comap Φ := by
  refine ⟨⟨L.comap Φ, hL.2.1.comap_of_injective Φ hΦ, fun {Q} hQ hle => ?_⟩, rfl⟩
  have hLQ : L ≤ Q.map Φ := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hL.1 hy)
    exact ⟨x, hle hy, rfl⟩
  rw [← hL.2.2 _ (Subgroup.map_le_range Φ Q) (hQ.map Φ) hLQ,
    Subgroup.comap_map_eq_self_of_injective hΦ]

variable {F : Type} [Field F] [Finite F]

theorem exists_conj_quat_mem (hodd : Odd (Nat.card F)) {a b : F} (h : a ^ 2 + b ^ 2 = -1)
    (P : Sylow 2 (SL2 F)) :
    ∃ ρ : SL2 F, ρ * quatI * ρ⁻¹ ∈ P ∧ ρ * quatJ h * ρ⁻¹ ∈ P := by
  have hz2 : (-1 : SL2 F) ^ 2 = 1 := by rw [sq, neg_one_mul, neg_neg]
  obtain ⟨H, hIH, hJH, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_quaternion_subgroup_of_anticommuting
      (sl2_neg_one_ne_one hodd) hz2 (by rw [sq, quatI_mul_self]) (by rw [sq, quatJ_mul_self])
      (quatI_mul_quatJ h)
  have hH : IsPGroup 2 H := IsPGroup.of_card (n := 3) (by
    rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num)
  obtain ⟨S', hS'⟩ := hH.exists_le_sylow
  obtain ⟨ρ, hρ⟩ := MulAction.exists_smul_eq (SL2 F) S' P
  have hmem : ∀ y ∈ H, ρ * y * ρ⁻¹ ∈ P := by
    intro y hy
    rw [← hρ, ← SetLike.mem_coe, Sylow.coe_smul]
    exact Set.mem_smul_set.mpr ⟨y, hS' hy, rfl⟩
  exact ⟨ρ, hmem _ hIH, hmem _ hJH⟩

variable {C : Type} [Group C]

theorem mem_of_centralizes_sylow (hodd : Odd (Nat.card F)) {a b : F} (hab : a ^ 2 + b ^ 2 = -1)
    (Φ : SL2 F →* C) (hΦ : Function.Injective Φ)
    (hlin : ∀ c : C, c * Φ (-1) = Φ (-1) * c → LinAct Φ c)
    (hinv : ∀ x : C, x * x = 1 → (∀ A, x * Φ A = Φ A * x) → x = 1 ∨ x = Φ (-1))
    (g₀ : C) {L₀ : Subgroup C} (hL₀ : IsSylow2In L₀ (conjSub g₀ Φ.range))
    {x : C} (hx2 : x * x = 1) (hxL : ∀ y ∈ L₀, x * y = y * x) : x ∈ L₀ := by
  have hL' := isSylow2In_conj g₀ hL₀
  have hx'L : ∀ y ∈ conjSub g₀⁻¹ L₀, (g₀⁻¹ * x * g₀) * y = y * (g₀⁻¹ * x * g₀) := by
    intro y hy
    rw [mem_conjSub_iff, inv_inv] at hy
    have h1 := hxL _ hy
    calc g₀⁻¹ * x * g₀ * y = g₀⁻¹ * (x * (g₀ * y * g₀⁻¹)) * g₀ := by group
      _ = g₀⁻¹ * ((g₀ * y * g₀⁻¹) * x) * g₀ := by rw [h1]
      _ = y * (g₀⁻¹ * x * g₀) := by group
  have hmemL : ∀ y ∈ conjSub g₀⁻¹ L₀, g₀ * y * g₀⁻¹ ∈ L₀ := by
    intro y hy
    rwa [mem_conjSub_iff, inv_inv] at hy
  obtain ⟨P, hP⟩ := exists_sylow_comap Φ hΦ hL'
  have hPL : ∀ A ∈ P, Φ A ∈ conjSub g₀⁻¹ L₀ := by
    intro A hA
    have hA' : A ∈ (P : Subgroup (SL2 F)) := hA
    rw [hP] at hA'
    exact hA'
  obtain ⟨ρ, hI, hJ⟩ := exists_conj_quat_mem hodd hab P
  have hneg : (-1 : SL2 F) ∈ P := by
    have h1 : ρ * quatI * ρ⁻¹ * (ρ * quatI * ρ⁻¹) = -1 := by
      calc ρ * quatI * ρ⁻¹ * (ρ * quatI * ρ⁻¹) = ρ * (quatI * quatI) * ρ⁻¹ := by group
        _ = -1 := by rw [quatI_mul_self, mul_neg_one, neg_mul, mul_inv_cancel]
    rw [← h1]
    exact mul_mem hI hI
  set x' := g₀⁻¹ * x * g₀ with hx'
  have hcomm : ∀ A ∈ P, x' * Φ A = Φ A * x' := fun A hA => hx'L _ (hPL A hA)
  obtain ⟨D, hD⟩ := hlin x' (hcomm _ hneg)
  have hfix : ∀ A ∈ P, glConjSL D A = A := by
    intro A hA
    apply hΦ
    rw [← hD, hcomm A hA, mul_inv_cancel_right]
  have htriv := glConjSL_eq_of_fix_quaternion hab
    (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd) ρ (hfix _ hI) (hfix _ hJ)
  have hc : ∀ A, x' * Φ A = Φ A * x' := by
    intro A
    have h1 := hD A
    rw [htriv] at h1
    calc x' * Φ A = x' * Φ A * x'⁻¹ * x' := by group
      _ = Φ A * x' := by rw [h1]
  have hx'2 : x' * x' = 1 := by
    rw [hx']
    calc g₀⁻¹ * x * g₀ * (g₀⁻¹ * x * g₀) = g₀⁻¹ * (x * x) * g₀ := by group
      _ = 1 := by rw [hx2]; group
  have hxe : x = g₀ * x' * g₀⁻¹ := by rw [hx']; group
  rcases hinv x' hx'2 hc with h | h
  · rw [hxe, h, mul_one, mul_inv_cancel]
    exact L₀.one_mem
  · rw [hxe, h]
    exact hmemL _ (hPL _ hneg)

end CFSG.ClassicalInvolution.Q3.TL4.S3Dich
