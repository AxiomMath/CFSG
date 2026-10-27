module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.QuasithinUnique

namespace C56

section Omega

variable {F : Type*} [Field F]

@[expose] def omega (v w : Fin 2 → F) : F := v 0 * w 1 - v 1 * w 0

theorem omega_mulVec (g : Matrix (Fin 2) (Fin 2) F) (v w : Fin 2 → F) :
    omega (g.mulVec v) (g.mulVec w) = g.det * omega v w := by
  simp only [omega, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem omega_map (σ : F ≃+* F) (v w : Fin 2 → F) :
    omega (fun i => σ (v i)) (fun i => σ (w i)) = σ (omega v w) := by
  simp [omega, map_sub, map_mul]

@[expose] def colMat (f : (Fin 2 → F) →+ (Fin 2 → F)) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => f (Pi.single j 1) i

theorem colMat_mulVec (f : (Fin 2 → F) →+ (Fin 2 → F)) (σ : F ≃+* F)
    (hf : ∀ (c : F) (v : Fin 2 → F), f (c • v) = σ c • f v) (v : Fin 2 → F) :
    f v = (colMat f).mulVec (fun i => σ (v i)) := by
  have hsplit : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) := by
    ext i; fin_cases i <;> simp
  have e0 : f (Pi.single 0 (v 0)) = σ (v 0) • f (Pi.single 0 1) := by
    have : (Pi.single 0 (v 0) : Fin 2 → F) = v 0 • Pi.single 0 1 := by
      ext i; fin_cases i <;> simp
    rw [this, hf]
  have e1 : f (Pi.single 1 (v 1)) = σ (v 1) • f (Pi.single 1 1) := by
    have : (Pi.single 1 (v 1) : Fin 2 → F) = v 1 • Pi.single 1 1 := by
      ext i; fin_cases i <;> simp
    rw [this, hf]
  conv_lhs => rw [hsplit]
  rw [map_add, e0, e1]
  ext i
  simp [colMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem det_colMat (f : (Fin 2 → F) →+ (Fin 2 → F)) :
    (colMat f).det = omega (f (Pi.single 0 1)) (f (Pi.single 1 1)) := by
  simp only [colMat, Matrix.det_fin_two, omega, Matrix.of_apply]
  ring

theorem omega_semilinear (f : (Fin 2 → F) →+ (Fin 2 → F)) (σ : F ≃+* F)
    (hf : ∀ (c : F) (v : Fin 2 → F), f (c • v) = σ c • f v) (v w : Fin 2 → F) :
    omega (f v) (f w) = omega (f (Pi.single 0 1)) (f (Pi.single 1 1)) * σ (omega v w) := by
  rw [colMat_mulVec f σ hf v, colMat_mulVec f σ hf w, omega_mulVec, omega_map, det_colMat]

theorem omega_basis : omega (Pi.single 0 1 : Fin 2 → F) (Pi.single 1 1) = 1 := by
  simp [omega]

end Omega

section Average

variable {F : Type*} [Field F]

theorem exists_coboundary [Fintype F] [CharP F 2] (hF : 2 < Fintype.card F) {P : Type*} [Group P]
    [Fintype P] (hP : IsPGroup 2 P) (Φ : P →* (F ≃+* F)) (e : P → F) (he0 : ∀ p, e p ≠ 0)
    (hcocycle : ∀ p q, e (p * q) = e p * Φ p (e q)) :
    ∃ M : F, M ≠ 0 ∧ ∀ p, e p * Φ p M = M := by
  classical
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  have hN : Fintype.card P = 2 ^ a := by rw [← Nat.card_eq_fintype_card]; exact ha
  set D : F := ∏ r : P, e r with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun r _ => he0 r
  have key : ∀ s : P, e s ^ (2 ^ a) * Φ s D = D := by
    intro s
    have h1 : Φ s D = ∏ r : P, Φ s (e r) := map_prod (Φ s) e Finset.univ
    have h2 : ∏ r : P, (e s * Φ s (e r)) = D := by
      rw [hD]
      refine Fintype.prod_equiv (Equiv.mulLeft s) _ _ fun r => ?_
      exact (hcocycle s r).symm
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hN, ← h1] at h2
    exact h2
  have hc : Odd (Fintype.card F - 1) := by
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    have hev : Even (Fintype.card F) := by
      rw [hn]; exact (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
    rw [Nat.odd_iff]
    have := Nat.even_iff.mp hev
    omega
  have hcop : Nat.Coprime (2 ^ a) (Fintype.card F - 1) :=
    (Nat.coprime_two_left.mpr hc).pow_left a
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hpow : ∀ x : F, x ≠ 0 → x ^ (2 ^ a * m) = x := by
    intro x hx
    have h1 := FiniteField.pow_card_sub_one_eq_one x hx
    calc x ^ (2 ^ a * m)
        = x ^ ((Fintype.card F - 1) * (2 ^ a * m / (Fintype.card F - 1)) +
            2 ^ a * m % (Fintype.card F - 1)) := by rw [Nat.div_add_mod]
      _ = x := by rw [pow_add, pow_mul, h1, one_pow, one_mul, hm, pow_one]
  refine ⟨D ^ m, pow_ne_zero m hD0, fun s => ?_⟩
  have h3 := congrArg (fun y => y ^ m) (key s)
  simp only [mul_pow, ← pow_mul] at h3
  rw [hpow (e s) (he0 s)] at h3
  rw [map_pow]
  exact h3

end Average

end C56

end CFSG.QuasithinUnique
