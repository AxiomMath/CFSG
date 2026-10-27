module

public import CFSG.ClassicalInvolution.Balance.Q27D4Parts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.S3Dich

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance.Q27
open scoped MatrixGroups

@[expose] def y0 : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem y0_pow_three : y0 ^ 3 = 1 := by
  decide +kernel

theorem exists_q8_mul_y0 : ∀ g : SL(2, ZMod 3), ∃ k : SL(2, ZMod 3), k ^ 4 = 1 ∧
    (g = k ∨ g = k * y0 ∨ g = k * (y0 * y0)) := by
  decide +kernel

theorem eq_of_comm_q8 : ∀ g : SL(2, ZMod 3), (∀ k : SL(2, ZMod 3), k ^ 4 = 1 → g * k = k * g) →
    g = 1 ∨ g = -1 := by
  decide +kernel

theorem eq_y0_of_conj : ∀ x : SL(2, ZMod 3), x ^ 3 = 1 →
    (∀ k : SL(2, ZMod 3), k ^ 4 = 1 → x * k * x⁻¹ = y0 * k * y0⁻¹) → x = y0 := by
  decide +kernel

theorem eq_of_mul_self : ∀ g : SL(2, ZMod 3), g * g = 1 → g = 1 ∨ g = -1 := by
  decide +kernel

theorem neg_one_pow_four : (-1 : SL(2, ZMod 3)) ^ 4 = 1 := by
  decide +kernel

theorem neg_one_ne_one : (-1 : SL(2, ZMod 3)) ≠ 1 := by
  decide +kernel

theorem neg_one_mul_self : (-1 : SL(2, ZMod 3)) * (-1) = 1 := by
  decide +kernel

theorem conj_pow_four {g k : SL(2, ZMod 3)} (hk : k ^ 4 = 1) : (g * k * g⁻¹) ^ 4 = 1 := by
  rw [conj_pow, hk, mul_one, mul_inv_cancel]

variable {Y : Type} [Group Y]

theorem comm_of_comm_q8 (ι : SL(2, ZMod 3) →* Y) (hι : Function.Injective ι)
    (hN : ∀ g : Y, g * ι (-1) = ι (-1) * g → ∀ x, ∃ x', g * ι x * g⁻¹ = ι x')
    {g : Y} (hg : ∀ k : SL(2, ZMod 3), k ^ 4 = 1 → g * ι k = ι k * g) :
    ∀ x, g * ι x = ι x * g := by
  have hga : g * ι (-1) = ι (-1) * g := hg _ neg_one_pow_four
  obtain ⟨x', hx'⟩ := hN g hga y0
  have hx3 : x' ^ 3 = 1 := by
    apply hι
    rw [map_pow, ← hx', conj_pow, ← map_pow, y0_pow_three, map_one, mul_one, mul_inv_cancel]
  have hconj : ∀ k : SL(2, ZMod 3), k ^ 4 = 1 → x' * k * x'⁻¹ = y0 * k * y0⁻¹ := by
    intro k hk
    apply hι
    have h1 : g⁻¹ * ι k * g = ι k := by
      calc g⁻¹ * ι k * g = g⁻¹ * (g * ι k) := by rw [hg k hk, mul_assoc]
        _ = ι k := by group
    have h3 : g * ι (y0 * k * y0⁻¹) * g⁻¹ = ι (y0 * k * y0⁻¹) := by
      rw [hg _ (conj_pow_four hk), mul_inv_cancel_right]
    rw [map_mul, map_mul, map_inv, ← hx']
    calc g * ι y0 * g⁻¹ * ι k * (g * ι y0 * g⁻¹)⁻¹ =
          g * (ι y0 * (g⁻¹ * ι k * g) * (ι y0)⁻¹) * g⁻¹ := by group
      _ = g * ι (y0 * k * y0⁻¹) * g⁻¹ := by rw [h1, map_mul, map_mul, map_inv]
      _ = ι (y0 * k * y0⁻¹) := h3
  have hxy : x' = y0 := eq_y0_of_conj x' hx3 hconj
  have hgy : g * ι y0 = ι y0 * g := by
    have h1 : g * ι y0 * g⁻¹ = ι y0 := by rw [hx', hxy]
    calc g * ι y0 = g * ι y0 * g⁻¹ * g := by group
      _ = ι y0 * g := by rw [h1]
  intro x
  obtain ⟨k, hk, hx⟩ := exists_q8_mul_y0 x
  have hgk : Commute g (ι k) := hg k hk
  have hgy' : Commute g (ι y0) := hgy
  rcases hx with rfl | rfl | rfl
  · exact hgk.eq
  · rw [map_mul]; exact (hgk.mul_right hgy').eq
  · rw [map_mul, map_mul]; exact (hgk.mul_right (hgy'.mul_right hgy')).eq

theorem fixes_of_fixes_q8 (hO : InvolutionOddCoreTrivial Y) (ι : SL(2, ZMod 3) →* Y)
    (hι : Function.Injective ι)
    (hN : ∀ g : Y, g * ι (-1) = ι (-1) * g → ∀ x, ∃ x', g * ι x * g⁻¹ = ι x')
    (β : MulAut Y) (hβ : ∀ k : SL(2, ZMod 3), k ^ 4 = 1 → β (ι k) = ι k) :
    ∀ x, β (ι x) = ι x := by
  set a := ι (-1) with ha
  set y := ι y0 with hy
  have haa : a * a = 1 := by rw [ha, ← map_mul, neg_one_mul_self, map_one]
  have ha1 : a ≠ 1 := fun h => neg_one_ne_one (hι (h.trans (map_one ι).symm))
  have hβa : β a = a := hβ _ neg_one_pow_four
  set c := y⁻¹ * β y with hc
  have hβy : β y = y * c := by rw [hc]; group
  have hcL : ∀ k : SL(2, ZMod 3), k ^ 4 = 1 → c * ι k = ι k * c := by
    intro k hk
    have h1 : β y * ι k * (β y)⁻¹ = y * ι k * y⁻¹ := by
      have h2 : y * ι k * y⁻¹ = ι (y0 * k * y0⁻¹) := by rw [hy, map_mul, map_mul, map_inv]
      calc β y * ι k * (β y)⁻¹ = β (y * ι k * y⁻¹) := by rw [map_mul, map_mul, map_inv, hβ k hk]
        _ = y * ι k * y⁻¹ := by rw [h2, hβ _ (conj_pow_four hk)]
    calc c * ι k = y⁻¹ * (β y * ι k * (β y)⁻¹) * β y := by rw [hc]; group
      _ = y⁻¹ * (y * ι k * y⁻¹) * β y := by rw [h1]
      _ = ι k * c := by rw [hc]; group
  have hcR := comm_of_comm_q8 ι hι hN hcL
  have hcy : c * y = y * c := hcR y0
  have hca : c * a = a * c := hcR (-1)
  have hc3 : c ^ 3 = 1 := by
    have h1 : (β y) ^ 3 = 1 := by rw [← map_pow, hy, ← map_pow, y0_pow_three, map_one, map_one]
    rw [hβy, (show Commute y c from hcy.symm).mul_pow, hy, ← map_pow, y0_pow_three, map_one,
      one_mul] at h1
    exact h1
  have hβk : ∀ k : SL(2, ZMod 3), k ^ 4 = 1 → ∀ j : ℕ,
      β (ι (k * y0 ^ j)) = ι (k * y0 ^ j) * c ^ j := by
    intro k hk j
    rw [map_mul, map_mul, hβ k hk, map_pow, map_pow, ← hy, hβy,
      (show Commute y c from hcy.symm).mul_pow, mul_assoc]
  have hnorm : ∀ g : Y, g * a = a * g → g * c * g⁻¹ ∈ Subgroup.zpowers c := by
    intro g hga
    obtain ⟨x₁, hx₁⟩ := hN g hga y0
    have hg'a : β.symm g * a = a * β.symm g := by
      apply β.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hβa, hga]
    obtain ⟨x₂, hx₂⟩ := hN (β.symm g) hg'a y0
    have hβ2 : g * β y * g⁻¹ = β (ι x₂) := by
      rw [← hx₂, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    obtain ⟨k₂, hk₂, j, hj, hxk⟩ : ∃ k₂ : SL(2, ZMod 3), k₂ ^ 4 = 1 ∧ ∃ j : ℕ, j < 3 ∧
        x₂ = k₂ * y0 ^ j := by
      obtain ⟨k, hk, h | h | h⟩ := exists_q8_mul_y0 x₂
      · exact ⟨k, hk, 0, by norm_num, by rw [h, pow_zero, mul_one]⟩
      · exact ⟨k, hk, 1, by norm_num, by rw [h, pow_one]⟩
      · exact ⟨k, hk, 2, by norm_num, by rw [h, sq]⟩
    have hgc : g * c * g⁻¹ = ι (x₁⁻¹ * x₂) * c ^ j := by
      have h1 : g * c * g⁻¹ = (g * y * g⁻¹)⁻¹ * (g * β y * g⁻¹) := by rw [hc]; group
      rw [h1, hβ2, hxk, hβk k₂ hk₂ j, hx₁]
      simp only [map_mul, map_inv, mul_assoc]
    have hgcR : ∀ x, g * c * g⁻¹ * ι x = ι x * (g * c * g⁻¹) := by
      intro x
      have hgi : g⁻¹ * ι (-1) = ι (-1) * g⁻¹ := by
        calc g⁻¹ * ι (-1) = g⁻¹ * (ι (-1) * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * ι (-1)) * g⁻¹ := by rw [← ha, ← hga]
          _ = ι (-1) * g⁻¹ := by group
      obtain ⟨x'', hx''⟩ := hN g⁻¹ hgi x
      have h1 : g⁻¹ * ι x * g = ι x'' := by rw [← hx'', inv_inv]
      calc g * c * g⁻¹ * ι x = g * (c * (g⁻¹ * ι x * g)) * g⁻¹ := by group
        _ = g * (c * ι x'') * g⁻¹ := by rw [h1]
        _ = g * (ι x'' * c) * g⁻¹ := by rw [hcR x'']
        _ = g * ((g⁻¹ * ι x * g) * c) * g⁻¹ := by rw [h1]
        _ = ι x * (g * c * g⁻¹) := by group
    have hcj : ∀ x, c ^ j * ι x = ι x * c ^ j := fun x => ((Commute.pow_left (hcR x) j)).eq
    have hxx : ∀ k : SL(2, ZMod 3), k ^ 4 = 1 → x₁⁻¹ * x₂ * k = k * (x₁⁻¹ * x₂) := by
      intro k _
      apply hι
      have h1 : ι (x₁⁻¹ * x₂) = g * c * g⁻¹ * (c ^ j)⁻¹ := by rw [hgc]; group
      rw [map_mul ι (x₁⁻¹ * x₂) k, map_mul ι k (x₁⁻¹ * x₂), h1]
      calc g * c * g⁻¹ * (c ^ j)⁻¹ * ι k = g * c * g⁻¹ * ((c ^ j)⁻¹ * ι k) := by
            simp only [mul_assoc]
        _ = g * c * g⁻¹ * (ι k * (c ^ j)⁻¹) := by
          rw [show (c ^ j)⁻¹ * ι k = ι k * (c ^ j)⁻¹ from
            ((Commute.inv_left (Commute.pow_left (hcR k) j))).eq]
        _ = (g * c * g⁻¹ * ι k) * (c ^ j)⁻¹ := by simp only [mul_assoc]
        _ = ι k * (g * c * g⁻¹) * (c ^ j)⁻¹ := by rw [hgcR k]
        _ = ι k * (g * c * g⁻¹ * (c ^ j)⁻¹) := by simp only [mul_assoc]
    have hgc3 : (g * c * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hc3, mul_one, mul_inv_cancel]
    rcases eq_of_comm_q8 _ hxx with h | h
    · rw [hgc, h, map_one, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) j
    · exfalso
      rw [hgc, h, ← ha] at hgc3
      have h2 : (a * c ^ j) ^ 3 = a := by
        rw [(Commute.pow_right (show Commute a c from hca.symm) j).mul_pow, ← pow_mul,
          show j * 3 = 3 * j by ring, pow_mul, hc3, one_pow, mul_one, pow_succ, sq, haa,
          one_mul]
      rw [h2] at hgc3
      exact ha1 hgc3
  have hc1 : c = 1 := by
    have hle : Subgroup.zpowers c ≤ Subgroup.centralizer ({a} : Set Y) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hca
    have hN' : ∀ g ∈ Subgroup.centralizer ({a} : Set Y), ∀ n ∈ Subgroup.zpowers c,
        g * n * g⁻¹ ∈ Subgroup.zpowers c := by
      intro g hg n hn
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ (hnorm g (Subgroup.mem_centralizer_singleton_iff.mp hg)) m
    have hodd : Odd (Nat.card (Subgroup.zpowers c)) := by
      rw [Nat.card_zpowers]
      have h3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h <;> rw [h] <;> decide
    have h := hO a haa ha1 _ hle hN' hodd
    have hcm : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
    rw [h, Subgroup.mem_bot] at hcm
    exact hcm
  intro x
  obtain ⟨k, hk, h | h | h⟩ := exists_q8_mul_y0 x
  · rw [h]
    exact hβ k hk
  · have := hβk k hk 1
    rw [hc1, one_pow, mul_one, pow_one] at this
    rw [h]
    exact this
  · have := hβk k hk 2
    rw [hc1, one_pow, mul_one, sq] at this
    rw [h]
    exact this

end CFSG.ClassicalInvolution.Q3.TL4.S3Dich
