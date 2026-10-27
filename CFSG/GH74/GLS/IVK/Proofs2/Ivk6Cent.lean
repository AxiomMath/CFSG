module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section Cent

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem sq_eq_one_of_mem_fieldAutSub (hF : L2Field F) (e : K ≃* L2 F)
    (hq : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9) {φ : MulAut K}
    (hφ : φ ∈ fieldAutSub e) : φ ^ 2 = 1 := by
  obtain ⟨-, -, hn⟩ := ivk_1_2e F hF K e
  have hord : ∀ n : ℕ, Nat.card ↥(fieldAutSub e) = n → n ≤ 2 → φ ^ 2 = 1 := by
    intro n hn1 hn2
    have h1 : (⟨φ, hφ⟩ : ↥(fieldAutSub e)) ^ Nat.card ↥(fieldAutSub e) = 1 := pow_card_eq_one'
    have h2 : φ ^ n = 1 := by
      have := congrArg Subtype.val h1
      rw [hn1] at this
      simpa using this
    interval_cases n
    · exact absurd hn1 Nat.card_pos.ne'
    · rw [pow_one] at h2
      rw [h2, one_pow]
    · exact h2
  rcases hq with h | h | h
  · exact hord 1 (hn 5 1 (by norm_num) (by rw [h]; norm_num)) (by norm_num)
  · exact hord 1 (hn 7 1 (by norm_num) (by rw [h]; norm_num)) (by norm_num)
  · exact hord 2 (hn 3 2 (by norm_num) (by rw [h]; norm_num)) (by norm_num)

end Cent

section Decomp

variable {X : Type} [Group X]

theorem eq_mul_of_mem_centralizer_eq_sup {U F : Subgroup X}
    (hC : centralizer (U : Set X) = U ⊔ F) {w : X} (hw : w ∈ centralizer (U : Set X)) :
    ∃ u ∈ U, ∃ φ ∈ F, w = u * φ := by
  have hFc : ∀ φ ∈ F, ∀ u ∈ U, u * φ = φ * u := fun φ hφ u hu =>
    mem_centralizer_iff.1 (hC ▸ (Subgroup.mem_sup_right hφ) : φ ∈ centralizer (U : Set X)) u hu
  have hFN : F ≤ normalizer (U : Set X) := by
    intro φ hφ
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 := hFc φ hφ h hh
      have h3 : φ * h * φ⁻¹ = h := by
        calc φ * h * φ⁻¹ = h * φ * φ⁻¹ := by rw [h1]
          _ = h := by group
      rw [h3]
      exact hh
    · intro hh
      have h1 := hFc φ⁻¹ (F.inv_mem hφ) _ hh
      have h2 : φ * h * φ⁻¹ * φ⁻¹ = h * φ⁻¹ := by
        rw [h1]
        group
      have h3 : φ * h * φ⁻¹ = h := mul_right_cancel h2
      rw [← h3]
      exact hh
  have hmem : w ∈ (↑(U ⊔ F) : Set X) := by
    rw [← hC]
    exact hw
  rw [Subgroup.coe_mul_of_right_le_normalizer_left U F hFN] at hmem
  obtain ⟨u, hu, φ, hφ, rfl⟩ := hmem
  exact ⟨u, hu, φ, hφ, rfl⟩

end Decomp

section Main

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_notation_cent
    (hF : L2Field F) (hq : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9) (e : K ≃* L2 F)
    {W E : Subgroup (MulAut K)} (hW : IsPGroup 2 ↥W) (hEW : E ≤ W) (hE : IsFourSubgroup E)
    (hEinn : E ≤ innAut K) :
    ∃ e' : K ≃* L2 F, Nonempty (L2Notation e') ∧ ∀ w ∈ centralizer (E : Set (MulAut K)),
      w ∈ E ∨ (w ∉ innDiagSub e' ∧ w ^ 2 = 1) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hWT⟩ := hW.exists_le_sylow
  obtain ⟨e', N, hNT⟩ := ivk_1_2a_exists F hF K e T
  have hTN : (N.T : Subgroup (MulAut K)) = (T : Subgroup (MulAut K)) := by rw [hNT]
  have hEP : E ≤ N.P := le_inf (by rw [hTN]; exact hEW.trans hWT) hEinn
  obtain ⟨U, hUP, hU4, hUC, -⟩ := ivk_1_3f_b F hF K e' N
  obtain ⟨g, hgPt, hgEU⟩ := ivk_1_3f_a F hF K e' N E U hEP hUP hE hU4
  refine ⟨e', ⟨N⟩, ?_⟩
  intro w hw
  have hUsq : ∀ u ∈ U, u ^ 2 = 1 := fun u hu => by
    have := hU4.1
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian u hu
  have hgfp : fieldProj e' g = 1 := (mem_innDiagSub_iff e' g).1 hgPt.2
  have hw' : g * w * g⁻¹ ∈ centralizer (U : Set (MulAut K)) := by
    rw [mem_centralizer_iff]
    intro u hu
    rw [← hgEU] at hu
    obtain ⟨a, haE, hau⟩ := hu
    have haw : a * w = w * a := mem_centralizer_iff.1 hw a haE
    have hau' : g * a * g⁻¹ = u := hau
    rw [← hau']
    calc g * a * g⁻¹ * (g * w * g⁻¹) = g * (a * w) * g⁻¹ := by group
      _ = g * (w * a) * g⁻¹ := by rw [haw]
      _ = g * w * g⁻¹ * (g * a * g⁻¹) := by group
  obtain ⟨u, hu, φ, hφ, hwuφ⟩ := eq_mul_of_mem_centralizer_eq_sup hUC hw'
  have hw_eq : w = g⁻¹ * (u * φ) * g := by
    rw [← hwuφ]
    group
  by_cases hφ1 : φ = 1
  · left
    rw [hφ1, mul_one] at hw_eq
    have hu' := hu
    rw [← hgEU] at hu'
    obtain ⟨a, haE, hau⟩ := hu'
    have hau' : g * a * g⁻¹ = u := hau
    have : w = a := by
      rw [hw_eq, ← hau']
      group
    rw [this]
    exact haE
  · right
    have hφu : u * φ = φ * u :=
      mem_centralizer_iff.1 (hUC ▸ (Subgroup.mem_sup_right hφ) : φ ∈ centralizer (U : Set (MulAut K)))
        u hu
    have hufp : fieldProj e' u = 1 :=
      (mem_innDiagSub_iff e' u).1 (innAut_le_innDiagSub e' (hUP hu).2)
    obtain ⟨σ, hσ⟩ := hφ
    have hφfp : fieldProj e' φ = σ := by
      rw [← hσ]
      exact fieldProj_fieldAutHom e' σ
    have hσ1 : σ ≠ 1 := by
      intro h
      apply hφ1
      rw [← hσ, h, map_one]
    have hφ' : φ ∈ fieldAutSub e' := ⟨σ, hσ⟩
    refine ⟨?_, ?_⟩
    · intro hwD
      have h1 := (mem_innDiagSub_iff e' w).1 hwD
      rw [hw_eq, map_mul, map_mul, map_mul, map_inv, hgfp, hufp, hφfp] at h1
      simp at h1
      exact hσ1 h1
    · have hφsq := sq_eq_one_of_mem_fieldAutSub hF e' hq hφ'
      have hφφ : φ * φ = 1 := by rwa [← pow_two]
      have huu : u * u = 1 := by rw [← pow_two]; exact hUsq u hu
      have h1 : (u * φ) * (u * φ) = 1 := by
        calc (u * φ) * (u * φ) = u * (φ * u) * φ := by group
          _ = u * (u * φ) * φ := by rw [← hφu]
          _ = (u * u) * (φ * φ) := by group
          _ = 1 := by rw [huu, hφφ, one_mul]
      have h2 : w * w = g⁻¹ * ((u * φ) * (u * φ)) * g := by
        rw [hw_eq]
        group
      rw [pow_two, h2, h1]
      group

end Main

end CFSG.GH74.GLS.IVK.Proofs2
