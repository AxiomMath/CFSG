module

public import CFSG.GF2Type.Smith1979.IdxFourIdentFL

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

theorem exists_perm_of_card_three : ∀ S : Finset (Fin 6), S.card = 3 →
    ∃ σ : Equiv.Perm (Fin 6), ∀ i, i ∈ S ↔ ((σ i : Fin 6) : ℕ) < 3 := by decide +kernel

theorem diagE_const (m : ZMod 3) : diagE (fun _ => m) = theta0e ^ m.val := by
  have h : ∀ n : ℕ, diagE (fun _ => (n : ZMod 3)) = theta0e ^ n := by
    intro n
    induction n with
    | zero =>
      have : (fun _ : Fin 6 => ((0 : ℕ) : ZMod 3)) = 0 := by ext; simp
      rw [this, diagE_zero, pow_zero]
    | succ n ih =>
      rw [pow_succ, ← ih, ← diagE_const_one, ← diagE_add]
      congr 1
      ext i
      simp
  have := h m.val
  rwa [ZMod.natCast_zmod_val] at this

theorem diagE_const_mem_D5 (m : ZMod 3) : diagE (fun _ => m) ∈ D5 :=
  ⟨fun _ => m, by simp [Finset.sum_const]; decide +revert, rfl⟩

theorem fl_of_type {X : Subgroup G12} (hX : Nat.card X = 39191040) (hN : Nsub ≤ X) {y : G12}
    (hy : y ∈ X) (hyg : y ∈ gammaU) (hyu : y * theta0e = theta0e * y) (hnot : y ∉ monLin)
    {c : Fin 6 → ZMod 3} {S : Finset (Fin 6)} (hS : S.card = 3) {j e : ZMod 3} (he : e ≠ 0)
    (hc : ∀ i, c i = j + if i ∈ S then e else 0) (hd : y⁻¹ * diagE c * y ∈ D5) : M0 ≤ X := by
  have hyθ : Commute y theta0e := hyu
  have hyconst : ∀ m : ZMod 3, y⁻¹ * diagE (fun _ => m) * y = diagE (fun _ => m) := fun m => by
    rw [diagE_const m, (hyθ.pow_right m.val).inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  let ind : Fin 6 → ZMod 3 := fun i => if i ∈ S then 1 else 0
  have hcsplit : c = (fun _ => j) + (fun i => e * ind i) := by
    ext i
    simp only [hc i, Pi.add_apply, ind]
    split_ifs <;> simp
  have h1 : y⁻¹ * diagE (fun i => e * ind i) * y ∈ D5 := by
    have h2 : y⁻¹ * diagE c * y = diagE (fun _ => j) * (y⁻¹ * diagE (fun i => e * ind i) * y) := by
      rw [hcsplit, diagE_add]
      calc y⁻¹ * (diagE (fun _ => j) * diagE fun i => e * ind i) * y
          = (y⁻¹ * diagE (fun _ => j) * y) * (y⁻¹ * diagE (fun i => e * ind i) * y) := by group
        _ = _ := by rw [hyconst j]
    have h3 : y⁻¹ * diagE (fun i => e * ind i) * y =
        (diagE (fun _ => j))⁻¹ * (y⁻¹ * diagE c * y) := by
      rw [h2]; group
    rw [h3]
    exact mul_mem (inv_mem (diagE_const_mem_D5 j)) hd
  have h4 : y⁻¹ * diagE ind * y ∈ D5 := by
    have key : ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = 2 := by decide
    rcases key e he with rfl | rfl
    · simpa [ind] using h1
    · have h5 : (y⁻¹ * diagE (fun i => 2 * ind i) * y) ^ 2 = y⁻¹ * diagE ind * y := by
        rw [pow_two]
        have : y⁻¹ * diagE (fun i => 2 * ind i) * y * (y⁻¹ * diagE (fun i => 2 * ind i) * y) =
            y⁻¹ * (diagE (fun i => 2 * ind i) * diagE (fun i => 2 * ind i)) * y := by group
        rw [this, ← diagE_add]
        have hh : ((fun i => 2 * ind i) + (fun i => 2 * ind i) : Fin 6 → ZMod 3) = ind := by
          ext i
          have : ∀ x : ZMod 3, 2 * x + 2 * x = x := by decide
          exact this (ind i)
        rw [hh]
      rw [← h5]
      exact pow_mem h1 2
  obtain ⟨σ, hσ⟩ := exists_perm_of_card_three S hS
  have hσX : permE σ ∈ X := hN (permE_mem_Nsub σ)
  have hσinv : (permE σ)⁻¹ ∈ X := inv_mem hσX
  set y' : G12 := permE σ * y * (permE σ)⁻¹ with hy'
  have hy'X : y' ∈ X := mul_mem (mul_mem hσX hy) hσinv
  have hy'g : y' ∈ gammaU :=
    mul_mem (mul_mem (permE_mem_gammaU σ) hyg) (inv_mem (permE_mem_gammaU σ))
  have hy'u : y' * theta0e = theta0e * y' := by
    have hp : Commute (permE σ) theta0e := permE_mul_theta0e σ
    exact ((hp.mul_left hyθ).mul_left hp.inv_left).eq
  have hy'not : y' ∉ monLin := by
    intro h
    apply hnot
    have : y = (permE σ)⁻¹ * y' * permE σ := by rw [hy']; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (permE_mem_monLin σ)) h) (permE_mem_monLin σ)
  have hchstd : diagE chStd = permE σ * diagE ind * (permE σ)⁻¹ := by
    rw [permE_mul_diagE_mul_inv]
    congr 1
    ext i
    have h6 := hσ ((σ.symm) i)
    simp only [Equiv.apply_symm_apply] at h6
    simp only [chStd, ind]
    by_cases h : ((i : Fin 6) : ℕ) < 3
    · rw [if_pos h, if_pos (h6.2 h)]
    · rw [if_neg h, if_neg (fun hm => h (h6.1 hm))]
  have hd' : y'⁻¹ * diagE chStd * y' ∈ D5 := by
    have : y'⁻¹ * diagE chStd * y' = permE σ * (y⁻¹ * diagE ind * y) * (permE σ)⁻¹ := by
      rw [hchstd, hy']; group
    rw [this]
    exact mul_mem_D5_of_mem_monGamma (monLin_le_monGamma (permE_mem_monLin σ)) h4
  exact fl_core hX hN hy'X hy'g hy'u hy'not hd'

end CFSG.GF2Type.Smith1979.IdxFour
