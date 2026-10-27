module

public import CFSG.LieType.SeitzGeneration.OutdiagBasic

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix Module

variable {F : Type*} [Field F] {n : ℕ}

theorem mul_pow_three_of_quasi {x y w : GL (Fin n) F} (hw : ∀ g, Commute w g) (hw3 : w ^ 3 = 1)
    (hyx : y * x = w * (x * y)) (b : ℕ) : (x * y ^ b) ^ 3 = x ^ 3 * (y ^ b) ^ 3 := by
  have hb : y ^ b * x = w ^ b * (x * y ^ b) := pow_mul_eq_of_quasi_commute hw hyx b
  refine mul_pow_prime_eq Nat.prime_three (by norm_num) (fun g => (hw g).pow_left b) hb ?_
  rw [← pow_mul, mul_comm, pow_mul, hw3, one_pow]

theorem coe_mul_of_smul_one {a b : GL (Fin n) F} {α β : F}
    (ha : (a : Matrix (Fin n) (Fin n) F) = α • 1) (hb : (b : Matrix (Fin n) (Fin n) F) = β • 1) :
    ((a * b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (α * β) • 1 := by
  rw [Units.val_mul, ha, hb, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]

theorem coe_pow_of_smul_one {a : GL (Fin n) F} {α : F}
    (ha : (a : Matrix (Fin n) (Fin n) F) = α • 1) (k : ℕ) :
    ((a ^ k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (α ^ k) • 1 := by
  rw [Units.val_pow_eq_pow_val, ha, smul_pow, one_pow]

section Lines

variable [Finite F]

theorem exists_cube_line (hF3 : 3 ∣ Nat.card F - 1) {x y w : GL (Fin n) F}
    (hw : ∀ g, Commute w g) (hw3 : w ^ 3 = 1) (hyx : y * x = w * (x * y)) {α β : F}
    (hα : α ≠ 0) (hβ : β ≠ 0) (hx3 : ((x ^ 3 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = α • 1)
    (hy3 : ((y ^ 3 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = β • 1) :
    ∃ (a b : ℕ) (s : F), s ≠ 0 ∧
      ((a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) ∧
      (((x ^ a * y ^ b) ^ 3 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (s ^ 3) • 1 := by
  set d := (Nat.card F - 1) / 3 with hd
  have hκ : ∀ t : F, t ≠ 0 → (t ^ d) ^ 3 = 1 := fun t ht => by
    rw [← pow_mul, mul_comm, hd, Nat.mul_div_cancel' hF3]
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one t ht
  have hxy : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
    simpa using mul_pow_three_of_quasi hw hw3 hyx 1
  have hxy2 : (x * y ^ 2) ^ 3 = x ^ 3 * (y ^ 3) ^ 2 := by
    rw [mul_pow_three_of_quasi hw hw3 hyx 2, ← pow_mul, ← pow_mul, mul_comm 2 3]
  rcases cube_roots_cases (hκ α hα) (hκ β hβ) with h | h | h | h
  · obtain ⟨s, hs0, hs⟩ := exists_pow_eq_of_pow_div_eq_one hF3 hα h
    refine ⟨1, 0, s, hs0, Or.inl ⟨rfl, rfl⟩, ?_⟩
    simpa [hs] using hx3
  · obtain ⟨s, hs0, hs⟩ := exists_pow_eq_of_pow_div_eq_one hF3 hβ h
    refine ⟨0, 1, s, hs0, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
    simpa [hs] using hy3
  · obtain ⟨s, hs0, hs⟩ := exists_pow_eq_of_pow_div_eq_one hF3 (mul_ne_zero hα hβ)
      (by rw [mul_pow, h])
    refine ⟨1, 1, s, hs0, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
    rw [pow_one, pow_one, hxy, coe_mul_of_smul_one hx3 hy3, hs]
  · obtain ⟨s, hs0, hs⟩ := exists_pow_eq_of_pow_div_eq_one hF3
      (mul_ne_zero hα (pow_ne_zero 2 hβ)) (by rw [mul_pow, pow_right_comm β 2 d]; exact h)
    refine ⟨1, 2, s, hs0, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_⟩
    rw [pow_one, hxy2, coe_mul_of_smul_one hx3 (coe_pow_of_smul_one hy3 2), hs]

end Lines

theorem exists_eigenvector_of_finrank_one {h : Matrix (Fin 3) (Fin 3) F}
    {L : Submodule F (Fin 3 → F)} (hL : finrank F L = 1) (hstab : ∀ u ∈ L, h.mulVec u ∈ L) :
    ∃ (c : F) (w : Fin 3 → F), w ≠ 0 ∧ h.mulVec w = c • w := by
  obtain ⟨v, hv0, hspan⟩ := finrank_eq_one_iff'.1 hL
  obtain ⟨c, hc⟩ := hspan ⟨h.mulVec (v : Fin 3 → F), hstab _ v.2⟩
  refine ⟨c, v, fun h0 => hv0 (Subtype.ext h0), ?_⟩
  have := congrArg Subtype.val hc
  exact this.symm

theorem pow_mulVec_of_mulVec_eq_smul {h : Matrix (Fin n) (Fin n) F} {c : F} {w : Fin n → F}
    (hw : h.mulVec w = c • w) (k : ℕ) : (h ^ k).mulVec w = (c ^ k) • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hw, smul_smul, pow_succ]

theorem exists_cube_of_commute (hF : ∃ ζ : F, IsPrimitiveRoot ζ 3) {x h : Matrix (Fin 3) (Fin 3) F}
    {lam : F} (hx3 : x ^ 3 = 1) (hxs : ∀ c : F, x ≠ c • (1 : Matrix (Fin 3) (Fin 3) F))
    (hcomm : x * h = h * x) (hh3 : h ^ 3 = lam • (1 : Matrix (Fin 3) (Fin 3) F)) :
    ∃ μ : F, μ ^ 3 = lam := by
  obtain ⟨ξ, v, -, hv0, hxv⟩ := exists_eigenvector_of_pow_eq_one (p := 3) (by norm_num) hF
    (by norm_num) hx3
  set T : Matrix (Fin 3) (Fin 3) F := x - ξ • 1 with hT
  have hTv : T.mulVec v = 0 := by
    rw [hT, Matrix.sub_mulVec, hxv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hTh : T * h = h * T := by
    rw [hT, Matrix.sub_mul, Matrix.mul_sub, hcomm, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  set Tl : (Fin 3 → F) →ₗ[F] (Fin 3 → F) := Matrix.toLin' T with hTl
  have hK : v ∈ LinearMap.ker Tl := by
    rw [LinearMap.mem_ker, hTl, Matrix.toLin'_apply]; exact hTv
  have hKne : 1 ≤ finrank F (LinearMap.ker Tl) :=
    Submodule.one_le_finrank_iff.2 (fun h0 => hv0 (by
      have : v ∈ (⊥ : Submodule F (Fin 3 → F)) := h0 ▸ hK
      simpa using this))
  have hRne : 1 ≤ finrank F (LinearMap.range Tl) := by
    refine Submodule.one_le_finrank_iff.2 (fun h0 => ?_)
    rw [LinearMap.range_eq_bot] at h0
    apply hxs ξ
    have : T = 0 := by
      have := congrArg Matrix.toLin'.symm h0
      simpa [hTl] using this
    rw [hT, sub_eq_zero] at this
    exact this
  have hrn := LinearMap.finrank_range_add_finrank_ker Tl
  rw [Module.finrank_fin_fun] at hrn
  have hstabK : ∀ u ∈ LinearMap.ker Tl, h.mulVec u ∈ LinearMap.ker Tl := by
    intro u hu
    rw [LinearMap.mem_ker, hTl, Matrix.toLin'_apply] at hu ⊢
    rw [Matrix.mulVec_mulVec, hTh, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
  have hstabR : ∀ u ∈ LinearMap.range Tl, h.mulVec u ∈ LinearMap.range Tl := by
    rintro u ⟨z, rfl⟩
    refine ⟨h.mulVec z, ?_⟩
    rw [hTl, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hTh]
  have hone : finrank F (LinearMap.ker Tl) = 1 ∨ finrank F (LinearMap.range Tl) = 1 := by omega
  obtain ⟨c, w, hw0, hhw⟩ : ∃ (c : F) (w : Fin 3 → F), w ≠ 0 ∧ h.mulVec w = c • w := by
    rcases hone with h1 | h1
    · exact exists_eigenvector_of_finrank_one h1 hstabK
    · exact exists_eigenvector_of_finrank_one h1 hstabR
  refine ⟨c, ?_⟩
  have h3 := pow_mulVec_of_mulVec_eq_smul hhw 3
  rw [hh3, Matrix.smul_mulVec, Matrix.one_mulVec] at h3
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw0
  have := congrFun h3 i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact (mul_right_cancel₀ hi this).symm

end CFSG.LieType.SeitzGeneration
