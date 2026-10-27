module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.AGLEmbedding.Norton.MON5_7

section Indep

variable {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]

theorem eq_one_of_sq_eq_one_of_pow_eq_one (hp2 : p ≠ 2) {x : G} (hx : x ^ p = 1)
    (hsq : x * x = 1) : x = 1 := by
  have hsq' : x ^ 2 = 1 := by rw [pow_two]; exact hsq
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2)
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq'
  have h2 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem pow_eq_one_iff_dvd {x : G} (hx : x ^ p = 1) (hx1 : x ≠ 1) (n : ℕ) :
    x ^ n = 1 ↔ p ∣ n := by
  have : orderOf x = p := orderOf_eq_prime hx hx1
  rw [← this]
  exact orderOf_dvd_iff_pow_eq_one.symm

theorem pow_val_eq_one_iff {x : G} (hx : x ^ p = 1) (hx1 : x ≠ 1) (c : ZMod p) :
    x ^ c.val = 1 ↔ c = 0 := by
  rw [pow_eq_one_iff_dvd hx hx1, ← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]

theorem indep_of_involution (hp2 : p ≠ 2) (D Z E T : G) (hD : D ^ p = 1) (hZ : Z ^ p = 1)
    (hE : E ^ p = 1) (hD1 : D ≠ 1) (hZ1 : Z ≠ 1)
    (hZE : Z * E = E * Z) (hTT : T * T = 1) (hTD : T * D * T = D) (hTZ : T * Z * T = Z⁻¹)
    (hTE : T * E * T = E⁻¹) (hne : ∀ k : ℕ, E ≠ Z ^ k) :
    ∀ c : Fin 3 → ZMod p,
      ((List.finRange 3).map fun k => (![D, Z, E] : Fin 3 → G) k ^ (c k).val).prod = 1 →
        c = 0 := by
  intro c hc
  have hE1 : E ≠ 1 := by simpa using hne 0
  have hc' : D ^ (c 0).val * (Z ^ (c 1).val * E ^ (c 2).val) = 1 := by
    simpa [List.finRange_succ] using hc
  have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right hTT
  let σ : G →* G := (MulAut.conj T).toMonoidHom
  have hσ : ∀ g, σ g = T * g * T := fun g => by simp [σ, hTinv]
  have hσD : σ D = D := by rw [hσ]; exact hTD
  have hσZ : σ Z = Z⁻¹ := by rw [hσ]; exact hTZ
  have hσE : σ E = E⁻¹ := by rw [hσ]; exact hTE
  set x := D ^ (c 0).val with hx
  set y := Z ^ (c 1).val with hy
  set w := E ^ (c 2).val with hw
  have hσx : σ x = x := by rw [hx, map_pow, hσD]
  have hσy : σ y = y⁻¹ := by rw [hy, map_pow, hσZ, inv_pow]
  have hσw : σ w = w⁻¹ := by rw [hw, map_pow, hσE, inv_pow]
  have hcyw : Commute y w := Commute.pow_pow (show Commute Z E from hZE) _ _
  have hyp : y ^ p = 1 := by rw [hy, ← pow_mul, mul_comm, pow_mul, hZ, one_pow]
  have hwp : w ^ p = 1 := by rw [hw, ← pow_mul, mul_comm, pow_mul, hE, one_pow]
  have hconj : x * (y⁻¹ * w⁻¹) = 1 := by
    have := congrArg σ hc'
    rwa [map_mul, map_mul, map_one, hσx, hσy, hσw] at this
  have hyw1 : x = y * w := by
    have h1 : y⁻¹ * w⁻¹ = (y * w)⁻¹ := by rw [mul_inv_rev, hcyw.inv_inv.eq]
    rw [h1] at hconj
    exact mul_inv_eq_one.mp hconj
  have hq : (y * w) * (y * w) = 1 := by
    rw [hyw1] at hc'
    simpa [mul_assoc] using hc'
  have hyw : y * w = 1 :=
    eq_one_of_sq_eq_one_of_pow_eq_one hp2 (by rw [hcyw.mul_pow, hyp, hwp, one_mul]) hq
  have hx1 : x = 1 := by rw [hyw1, hyw]
  have hc0 : c 0 = 0 := (pow_val_eq_one_iff hD hD1 (c 0)).mp hx1
  have hc2 : c 2 = 0 := by
    by_contra h2
    have hk0 : (c 2).val ≠ 0 := fun h => h2 ((ZMod.val_eq_zero (c 2)).mp h)
    have hkp : Nat.Coprime (c 2).val p := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_)
      intro hd
      exact hk0 (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _))
    obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hkp hp.out.one_lt
    have hEk : E ^ (c 2).val = (Z ^ (c 1).val)⁻¹ := eq_inv_of_mul_eq_one_right hyw
    have hZinv : Z⁻¹ = Z ^ (p - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, hZ]
    refine hne ((p - 1) * ((c 1).val * r)) ?_
    calc E = E ^ ((c 2).val * r) := by rw [pow_eq_pow_mod ((c 2).val * r) hE, hr, pow_one]
      _ = (E ^ (c 2).val) ^ r := pow_mul _ _ _
      _ = ((Z ^ (c 1).val)⁻¹) ^ r := by rw [hEk]
      _ = ((Z⁻¹) ^ (c 1).val) ^ r := by rw [← inv_pow]
      _ = Z ^ ((p - 1) * ((c 1).val * r)) := by
        rw [hZinv, ← pow_mul, ← pow_mul]
  have hw1 : w = 1 := by
    rw [hw, hc2]; simp
  have hy1 : y = 1 := by rw [hw1, mul_one] at hyw; exact hyw
  have hc1 : c 1 = 0 := (pow_val_eq_one_iff hZ hZ1 (c 1)).mp hy1
  funext i
  fin_cases i <;> simp [hc0, hc1, hc2]

theorem exists_eq_pow_of_pow_eq_pow {X Z : G} (hX : X ^ p = 1) (b : ZMod p) (hb : b ≠ 0) {n : ℕ}
    (h : X ^ b.val = Z ^ n) : ∃ k : ℕ, X = Z ^ k := by
  have hk0 : b.val ≠ 0 := fun h0 => hb ((ZMod.val_eq_zero b).mp h0)
  have hkp : Nat.Coprime b.val p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_)
    intro hd
    exact hk0 (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _))
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hkp hp.out.one_lt
  refine ⟨n * r, ?_⟩
  calc X = X ^ (b.val * r) := by rw [pow_eq_pow_mod (b.val * r) hX, hr, pow_one]
    _ = (X ^ b.val) ^ r := pow_mul _ _ _
    _ = (Z ^ n) ^ r := by rw [h]
    _ = Z ^ (n * r) := (pow_mul _ _ _).symm

theorem inv_eq_pow_pred {D : G} (hD : D ^ p = 1) : D⁻¹ = D ^ (p - 1) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, hD]

theorem indep_two_of_not_pow (D X : G) (hD : D ^ p = 1) (hX : X ^ p = 1) (hD1 : D ≠ 1)
    (hne : ∀ k : ℕ, X ≠ D ^ k) :
    ∀ c : Fin 2 → ZMod p,
      ((List.finRange 2).map fun k => (![D, X] : Fin 2 → G) k ^ (c k).val).prod = 1 → c = 0 := by
  intro c hc
  have hc' : D ^ (c 0).val * X ^ (c 1).val = 1 := by
    simpa [List.finRange_succ] using hc
  have hc1 : c 1 = 0 := by
    by_contra h1
    obtain ⟨k, hk⟩ := exists_eq_pow_of_pow_eq_pow hX (c 1) h1 (Z := D)
      (n := (p - 1) * (c 0).val) (by
        have : X ^ (c 1).val = (D ^ (c 0).val)⁻¹ := eq_inv_of_mul_eq_one_right hc'
        rw [this, ← inv_pow, inv_eq_pow_pred hD, ← pow_mul])
    exact hne k hk
  have hX0 : X ^ (c 1).val = 1 := by rw [hc1]; simp
  have hD0 : D ^ (c 0).val = 1 := by rw [hX0, mul_one] at hc'; exact hc'
  have hc0 : c 0 = 0 := (pow_val_eq_one_iff hD hD1 (c 0)).mp hD0
  funext i
  fin_cases i <;> simp [hc0, hc1]

theorem indep_three_of_involution (hp2 : p ≠ 2) (D X Z T : G) (hD : D ^ p = 1) (hX : X ^ p = 1)
    (hZ : Z ^ p = 1) (hD1 : D ≠ 1) (hZ1 : Z ≠ 1) (hTT : T * T = 1) (hTD : T * D * T = D) (hTX : T * X * T = X)
    (hTZ : T * Z * T = Z⁻¹) (hne : ∀ k : ℕ, X ≠ D ^ k) :
    ∀ c : Fin 3 → ZMod p,
      ((List.finRange 3).map fun k => (![D, X, Z] : Fin 3 → G) k ^ (c k).val).prod = 1 →
        c = 0 := by
  intro c hc
  have hc' : D ^ (c 0).val * (X ^ (c 1).val * Z ^ (c 2).val) = 1 := by
    simpa [List.finRange_succ] using hc
  have hTinv : T⁻¹ = T := inv_eq_of_mul_eq_one_right hTT
  let σ : G →* G := (MulAut.conj T).toMonoidHom
  have hσ : ∀ g, σ g = T * g * T := fun g => by simp [σ, hTinv]
  have hσD : σ D = D := by rw [hσ]; exact hTD
  have hσX : σ X = X := by rw [hσ]; exact hTX
  have hσZ : σ Z = Z⁻¹ := by rw [hσ]; exact hTZ
  set u := D ^ (c 0).val * X ^ (c 1).val with hu
  set w := Z ^ (c 2).val with hw
  have hσu : σ u = u := by rw [hu, map_mul, map_pow, map_pow, hσD, hσX]
  have hσw : σ w = w⁻¹ := by rw [hw, map_pow, hσZ, inv_pow]
  have hwp : w ^ p = 1 := by rw [hw, ← pow_mul, mul_comm, pow_mul, hZ, one_pow]
  have hc'' : u * w = 1 := by rw [hu, hw]; simpa [mul_assoc] using hc'
  have hconj : u * w⁻¹ = 1 := by
    have := congrArg σ hc''
    rwa [map_mul, map_one, hσu, hσw] at this
  have e1 : u = w⁻¹ := eq_inv_of_mul_eq_one_left hc''
  have e2 : u = w := mul_inv_eq_one.mp hconj
  have hww : w = w⁻¹ := e2.symm.trans e1
  have hq : w * w = 1 := by
    have : w * w⁻¹ = 1 := mul_inv_cancel w
    rwa [← hww] at this
  have hw1 : w = 1 := eq_one_of_sq_eq_one_of_pow_eq_one hp2 hwp hq
  have hc2 : c 2 = 0 := (pow_val_eq_one_iff hZ hZ1 (c 2)).mp (by rw [← hw]; exact hw1)
  have hu1 : u = 1 := by rw [e2, hw1]
  have h2 := indep_two_of_not_pow D X hD hX hD1 hne ![c 0, c 1]
    (by simpa [List.finRange_succ, hu] using hu1)
  funext i
  fin_cases i
  · simpa using congrFun h2 0
  · simpa using congrFun h2 1
  · simpa using hc2

theorem indep_three_of_heisenberg (D Y Z E : G) (k : ℕ) (hk : ¬ p ∣ k)
    (hYZ : Y * Z = Z * Y) (hZ : Z ^ p = 1) (hZ1 : Z ≠ 1) (hEY : E * Y = Y * Z ^ k * E)
    (hEZ : E * Z = Z * E) (hED : E * D = D * E)
    (hDZind : ∀ c : Fin 2 → ZMod p,
      ((List.finRange 2).map fun j => (![D, Z] : Fin 2 → G) j ^ (c j).val).prod = 1 → c = 0) :
    ∀ c : Fin 3 → ZMod p,
      ((List.finRange 3).map fun j => (![D, Y, Z] : Fin 3 → G) j ^ (c j).val).prod = 1 →
        c = 0 := by
  intro c hc
  have hc' : D ^ (c 0).val * (Y ^ (c 1).val * Z ^ (c 2).val) = 1 := by
    simpa [List.finRange_succ] using hc
  let σ : G →* G := (MulAut.conj E).toMonoidHom
  have hσ : ∀ g, σ g = E * g * E⁻¹ := fun g => by simp [σ]
  have hσD : σ D = D := by rw [hσ, hED]; group
  have hσZ : σ Z = Z := by rw [hσ, hEZ]; group
  have hσY : σ Y = Y * Z ^ k := by
    rw [hσ, mul_inv_eq_iff_eq_mul]; exact hEY
  have hYZk : Commute Y (Z ^ k) := Commute.pow_right (show Commute Y Z from hYZ) _
  have hσYb : σ (Y ^ (c 1).val) = Y ^ (c 1).val * Z ^ (k * (c 1).val) := by
    rw [map_pow, hσY, hYZk.mul_pow, ← pow_mul]
  have h2 := congrArg σ hc'
  rw [map_mul, map_mul, hσYb, map_pow, map_pow, hσD, hσZ, map_one] at h2
  set A := D ^ (c 0).val
  set B := Y ^ (c 1).val
  set C := Z ^ (c 2).val
  have hZZ : Z ^ (k * (c 1).val) * C = C * Z ^ (k * (c 1).val) :=
    (Commute.pow_pow_self Z (k * (c 1).val) (c 2).val).eq
  have h3 : Z ^ (k * (c 1).val) = 1 := by
    have : A * (B * C) * Z ^ (k * (c 1).val) = 1 := by
      calc A * (B * C) * Z ^ (k * (c 1).val)
          = A * (B * (C * Z ^ (k * (c 1).val))) := by simp [mul_assoc]
        _ = A * (B * (Z ^ (k * (c 1).val) * C)) := by rw [hZZ]
        _ = A * (B * Z ^ (k * (c 1).val) * C) := by simp [mul_assoc]
        _ = 1 := h2
    rwa [hc', one_mul] at this
  have hdvd : p ∣ k * (c 1).val := (pow_eq_one_iff_dvd hZ hZ1 _).mp h3
  have hdvd1 : p ∣ (c 1).val := (hp.out.dvd_mul.mp hdvd).resolve_left hk
  have hc1 : c 1 = 0 := by
    rw [← ZMod.natCast_zmod_val (c 1)]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd1
  have hB : B = 1 := by
    have : (c 1).val = 0 := by rw [hc1]; simp
    simp [B, this]
  have hAC : D ^ (c 0).val * Z ^ (c 2).val = 1 := by
    rw [hB, one_mul] at hc'; exact hc'
  have h4 := hDZind ![c 0, c 2] (by simpa [List.finRange_succ] using hAC)
  funext i
  fin_cases i
  · simpa using congrFun h4 0
  · simpa using hc1
  · simpa using congrFun h4 1

end Indep

end CFSG.AGLEmbedding.Norton.MON5_7
