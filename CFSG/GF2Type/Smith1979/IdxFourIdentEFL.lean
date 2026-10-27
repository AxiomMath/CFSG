module

public import CFSG.GF2Type.Smith1979.IdxFourIdentECheck
public import CFSG.GF2Type.Smith1979.IdxFourIdent

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

namespace ECheck

open FLCheck

@[expose] def cyc3 : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 0 1

@[expose] def cyc5 : Equiv.Perm (Fin 6) where
  toFun i := if i = 0 then 0 else if i = 5 then 1 else i + 1
  invFun i := if i = 0 then 0 else if i = 1 then 5 else i - 1
  left_inv := by decide
  right_inv := by decide

theorem cyc3_even : cyc3 ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)

theorem cyc5_even : cyc5 ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)

theorem a3_hasRows : HasRows (permE cyc3) a3Rows.toList := by
  have h := permE_hasRows cyc3
  rwa [show monRowsF 0 cyc3 0 = a3Rows.toList by decide +kernel] at h

theorem a5_hasRows : HasRows (permE cyc5) a5Rows.toList := by
  have h := permE_hasRows cyc5
  rwa [show monRowsF 0 cyc5 0 = a5Rows.toList by decide +kernel] at h

theorem exists_even_perm_of_card_three (S : Finset (Fin 6)) (hS : S.card = 3) :
    ∃ σ : Equiv.Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) ∧
      ∀ i, i ∈ S ↔ ((σ i : Fin 6) : ℕ) < 3 := by
  obtain ⟨σ₀, hσ₀⟩ := exists_perm_of_card_three S hS
  by_cases h : σ₀ ∈ alternatingGroup (Fin 6)
  · exact ⟨σ₀, h, hσ₀⟩
  · refine ⟨Equiv.swap 0 1 * σ₀, ?_, fun i => ?_⟩
    · have h1 : Equiv.Perm.sign σ₀ = -1 := by
        have := Equiv.Perm.mem_alternatingGroup (f := σ₀)
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ₀) with h2 | h2
        · exact absurd (this.2 h2) h
        · exact h2
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide), h1]
      rfl
    · rw [hσ₀ i, Equiv.Perm.mul_apply]
      generalize σ₀ i = j
      revert j
      decide

end ECheck

open FLCheck ECheck

theorem Delta0_mem_monGamma (j : ZMod 3) : Delta0 j ∈ monGamma :=
  monLin_le_monGamma (Delta0_mem_monLin j)

theorem conjSub_E0_le {E₁ : Subgroup G12} (hR0 : R0 ≤ E₁) {m : G12} (hm : m ∈ monGamma)
    (hy : m * y3e * m⁻¹ ∈ E₁) : conjSub E0 m ≤ E₁ := by
  unfold conjSub
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).2 ?_
  rintro l ⟨r, hr, hl⟩
  simp only [e0Gens, List.mem_cons, List.mem_nil_iff, or_false] at hr
  show (MulAut.conj m) l ∈ E₁
  rw [MulAut.conj_apply]
  rcases hr with rfl | rfl | rfl
  · rw [HasRows.eq ⟨rfl, hl⟩ a3_hasRows]
    exact hR0 (mul_mem_R0_of_mem_monGamma hm (permE_mem_R0 cyc3_even))
  · rw [HasRows.eq ⟨rfl, hl⟩ a5_hasRows]
    exact hR0 (mul_mem_R0_of_mem_monGamma hm (permE_mem_R0 cyc5_even))
  · rw [HasRows.eq ⟨rfl, hl⟩ y3e_hasRows]
    exact hy

theorem fl_core_E {E₁ : Subgroup G12} (hcard : Nat.card E₁ = 9797760) (hR0 : R0 ≤ E₁) {y : G12}
    (hy : y ∈ E₁) (hyg : y ∈ gammaU) (hyu : y * theta0e = theta0e * y) (hnot : y ∉ monLin)
    (hd : y⁻¹ * diagE chStd * y ∈ D5) : ∃ m ∈ monGamma, conjSub E0 m ≤ E₁ := by
  obtain ⟨a, b, s, c, π, hc, rfl⟩ := adjacent_structure hyg hyu hd
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    apply hnot
    rw [Umat_zero_zero, one_mul]
    exact mul_mem (Delta0_mem_monLin s) (mem_monLin_iff.2 ⟨c, π, rfl⟩)
  have hcand : ∃ ε : ZMod 2,
      Umat a b * Delta0 s * (permE (Equiv.swap 0 1)) ^ ε.val ∈ E₁ := by
    by_cases hπ : π ∈ alternatingGroup (Fin 6)
    · refine ⟨0, ?_⟩
      have hn : diagE c * permE π ∈ R0 := ⟨c, π, hc, hπ, rfl⟩
      have h := mul_mem hy (inv_mem (hR0 hn))
      rw [mul_inv_cancel_right] at h
      rwa [ZMod.val_zero, pow_zero, mul_one]
    · refine ⟨1, ?_⟩
      set τ : Equiv.Perm (Fin 6) := Equiv.swap 0 1 with hτ
      have hsign : Equiv.Perm.sign π = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h2 | h2
        · exact absurd (Equiv.Perm.mem_alternatingGroup.2 h2) hπ
        · exact h2
      have hπτ : π * τ⁻¹ ∈ alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hsign, hτ,
          Equiv.Perm.sign_swap (by decide)]
        rfl
      have hr : diagE c * permE (π * τ⁻¹) ∈ R0 := ⟨c, π * τ⁻¹, hc, hπτ, rfl⟩
      have hn : diagE c * permE π = diagE c * permE (π * τ⁻¹) * permE τ := by
        rw [mul_assoc, ← permE_mul, inv_mul_cancel_right]
      have ht1 : permE τ ∈ monGamma := monLin_le_monGamma (permE_mem_monLin τ)
      have hconj := mul_mem_R0_of_mem_monGamma (inv_mem ht1) (inv_mem hr)
      have h := mul_mem hy (hR0 hconj)
      rw [ZMod.val_one, pow_one]
      convert h using 1
      rw [hn]
      group
  obtain ⟨ε, hZ⟩ := hcand
  rcases candidates_E hR0 a b s ε hab hZ with ⟨j, hj⟩ | ⟨g, hg, h11⟩
  · exact ⟨Delta0 j, Delta0_mem_monGamma j, conjSub_E0_le hR0 (Delta0_mem_monGamma j) hj⟩
  · exfalso
    have h := h11.trans (Subgroup.orderOf_dvd_natCard E₁ hg)
    rw [hcard] at h
    omega

theorem fl_of_type_E {E₁ : Subgroup G12} (hcard : Nat.card E₁ = 9797760) (hR0 : R0 ≤ E₁) {y : G12}
    (hy : y ∈ E₁) (hyg : y ∈ gammaU) (hyu : y * theta0e = theta0e * y) (hnot : y ∉ monLin)
    {c : Fin 6 → ZMod 3} {S : Finset (Fin 6)} (hS : S.card = 3) {j e : ZMod 3} (he : e ≠ 0)
    (hc : ∀ i, c i = j + if i ∈ S then e else 0) (hd : y⁻¹ * diagE c * y ∈ D5) :
    ∃ m ∈ monGamma, conjSub E0 m ≤ E₁ := by
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
  obtain ⟨σ, hσA, hσ⟩ := exists_even_perm_of_card_three S hS
  have hσX : permE σ ∈ E₁ := hR0 (permE_mem_R0 hσA)
  have hσinv : (permE σ)⁻¹ ∈ E₁ := inv_mem hσX
  set y' : G12 := permE σ * y * (permE σ)⁻¹ with hy'
  have hy'X : y' ∈ E₁ := mul_mem (mul_mem hσX hy) hσinv
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
  exact fl_core_E hcard hR0 hy'X hy'g hy'u hy'not hd'

end CFSG.GF2Type.Smith1979.IdxFour
