module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusNum

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

theorem frob_cong_wt {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F) (φ : F ≃+* F) {r : ℕ} (m : Fin r → ℕ)
    (d c : Fin r → ℤ) (k j₁ : Fin r) (hc : ∀ j, |c j| ≤ 2) (hd : ∀ j, j ≠ k → d j = 0 ∨ d j = -1)
    (hd₁ : d j₁ = -1) (hm₁ : m j₁ = 1)
    (h : ∀ (s : Fˣ) (j : Fin r),
      (Units.map (φ : F →+* F) s) ^ ((m j : ℤ) * d j) = s ^ ((m j : ℤ) * c j)) :
    φ = 1 ∧ (∀ j, m j = 1 → j ≠ k → c j = d j) ∧
      ∀ j, ((Nat.card F - 1 : ℕ) : ℤ) ∣ (m j : ℤ) * (d j - c j) := by
  have hp : p.Prime := Fact.out
  have := Fintype.ofFinite F
  obtain ⟨n, -, hcard⟩ := FiniteField.card F p
  have hF : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨e, he, hφe⟩ := exists_ringEquiv_eq_frobenius_pow hp n.pos hF φ
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf ζ = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  have hφζ : Units.map (φ : F →+* F) ζ = ζ ^ (p ^ e) := by
    ext; simp [hφe]
  have hcong : ∀ j, ((Nat.card F - 1 : ℕ) : ℤ) ∣ (m j : ℤ) * ((p ^ e : ℕ) * d j - c j) := by
    intro j
    have h1 := h ζ j
    rw [hφζ, ← zpow_natCast, ← zpow_mul] at h1
    rw [← hord, orderOf_dvd_iff_zpow_eq_one, mul_sub, ← mul_assoc, mul_comm (m j : ℤ),
      mul_assoc, zpow_sub, h1]
    exact mul_inv_cancel _
  have hN1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hNq : p ^ e * 3 ≤ Nat.card F := by
    calc p ^ e * 3 ≤ p ^ e * p := Nat.mul_le_mul_left _ hp3
      _ = p ^ (e + 1) := (pow_succ _ _).symm
      _ ≤ p ^ (n : ℕ) := Nat.pow_le_pow_right hp.pos he
      _ = Nat.card F := hF.symm
  have hNodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have hstep1 : p ^ e = 1 := by
    have h1 := hcong j₁
    rw [hd₁, hm₁] at h1
    have hX : (p ^ e : ℕ) + c j₁ = 0 := by
      have h2 : ((Nat.card F - 1 : ℕ) : ℤ) ∣ (p ^ e : ℕ) + c j₁ := by
        have := dvd_neg.2 h1
        convert this using 1
        push_cast
        ring
      refine Int.eq_zero_of_abs_lt_dvd h2 ?_
      have := hc j₁
      rw [abs_le] at this
      rw [abs_lt]
      have hq' : (5 : ℤ) ≤ (Nat.card F : ℤ) := by exact_mod_cast hq
      have hNq' : ((p ^ e : ℕ) : ℤ) * 3 ≤ (Nat.card F : ℤ) := by exact_mod_cast hNq
      have hN1' : (1 : ℤ) ≤ ((p ^ e : ℕ) : ℤ) := by exact_mod_cast hN1
      have hsub : ((Nat.card F - 1 : ℕ) : ℤ) = (Nat.card F : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hsub]
      constructor <;> omega
    have hc1 := hc j₁
    rw [abs_le] at hc1
    have : ((p ^ e : ℕ) : ℤ) ≤ 2 := by omega
    have h2 : (p ^ e : ℕ) ≤ 2 := by exact_mod_cast this
    obtain ⟨m', hm'⟩ := hNodd
    omega
  have hm4 : (4 : ℤ) ≤ ((Nat.card F - 1 : ℕ) : ℤ) := by
    have : 5 ≤ Nat.card F := hq
    omega
  have hcong' : ∀ j, ((Nat.card F - 1 : ℕ) : ℤ) ∣ (m j : ℤ) * (d j - c j) := fun j => by
    have := hcong j
    rw [hstep1] at this
    simpa using this
  refine ⟨RingEquiv.ext fun x => by rw [hφe x, hstep1, pow_one]; rfl, fun j hmj hj => ?_, hcong'⟩
  have h0 := Int.eq_zero_of_abs_lt_dvd (by simpa [hmj] using hcong' j) (by
    have := hc j
    rw [abs_le] at this
    rw [abs_lt]
    rcases hd j hj with h | h <;> rw [h] <;> omega)
  omega

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
