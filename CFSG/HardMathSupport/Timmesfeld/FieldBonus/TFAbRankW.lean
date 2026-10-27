module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TFAbRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open Matrix CFSG.Open
open CFSG.SectionRank.ClassicalEven (torusDiag torusDiag_mem_SL torusDiag_mem_SU coe_torusDiag
  torusDiag_injective)

variable {K : Type} [Field K] [Finite K]

theorem exists_cuberoot_of_dvd (h3 : 3 ∣ Nat.card K - 1) : ∃ ω : Kˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [Nat.card_units]; exact h3)

omit [Finite K] in
theorem neg_one_units_ne_one (hK : (-1 : K) ≠ 1) : (-1 : Kˣ) ≠ 1 := fun h =>
  hK (by simpa using congrArg (fun u : Kˣ => (u : K)) h)

omit [Finite K] in
theorem torusDiag_signs_ne_one (hK : (-1 : K) ≠ 1) :
    torusDiag (K := K) ![-1, -1, 1] ≠ 1 := by
  intro h
  have := congrFun (torusDiag_injective (h.trans (map_one (torusDiag (ι := Fin 3) (K := K))).symm)) 0
  exact neg_one_units_ne_one hK (by simpa using this)

omit [Finite K] in
theorem torusDiag_signs_sq : torusDiag (K := K) ![-1, -1, 1] ^ 2 = 1 := by
  rw [← map_pow, ← map_one (torusDiag (ι := Fin 3) (K := K))]
  congr 1
  funext i
  fin_cases i <;> simp

theorem wGeTwoSL3Odd (hK : (-1 : K) ≠ 1) (h3 : 3 ∣ Nat.card K - 1) :
    2 ≤ CFSG.Open.GLATwoLocalRank 3 ↥(StatedSL 3 K) := by
  obtain ⟨ω, hω⟩ := exists_cuberoot_of_dvd h3
  exact two_le_glaTwoLocalRank_of_involution hω
    (torusDiag_mem_SL (by simp [Fin.prod_univ_three])) (torusDiag_mem_SL (by simp [Fin.prod_univ_three]))
    (d := ![-1, -1, 1]) (torusDiag_mem_SL (by simp [Fin.prod_univ_three]))
    (torusDiag_signs_ne_one hK) torusDiag_signs_sq

theorem neg_one_ne_one_of_card_sq {q : ℕ} (hq : Odd q) (hK : Nat.card K = q ^ 2) :
    (-1 : K) ≠ 1 := by
  have := Fintype.ofFinite K
  refine Ring.neg_one_ne_one_of_char_ne_two fun h2 => ?_
  have h := FiniteField.even_card_iff_char_two.1 h2
  rw [← Nat.card_eq_fintype_card, hK] at h
  exact (Nat.not_even_iff_odd.2 hq.pow) (Nat.even_iff.2 h)

theorem wGeTwoSU3Odd {q : ℕ} (hq : Odd q) (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) :
    2 ≤ CFSG.Open.GLATwoLocalRank 3 ↥(StatedSU 3 q K) := by
  have hq0 : q ≠ 0 := by rintro rfl; exact absurd hq (by decide)
  have hK1 := neg_one_ne_one_of_card_sq hq hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKu : Nat.card Kˣ = (q + 1) * (q - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by
    rw [hKu]; exact h3.mul_right _)
  have hωq : ω ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hω]; exact h3)
  have hev : Even (q + 1) := hq.add_one
  refine two_le_glaTwoLocalRank_of_involution hω
    (torusDiag_mem_SU hq0 (by simp [Fin.prod_univ_three]) ?_)
    (torusDiag_mem_SU hq0 (by simp [Fin.prod_univ_three]) ?_)
    (d := ![-1, -1, 1]) (torusDiag_mem_SU hq0 (by simp [Fin.prod_univ_three]) ?_)
    (torusDiag_signs_ne_one hK1) torusDiag_signs_sq
  · funext i
    fin_cases i <;> simp [hωq, inv_pow]
  · funext i
    fin_cases i <;> simp [hωq, inv_pow]
  · funext i
    fin_cases i <;> simp [hev.neg_one_pow]

end CFSG.HardMathSupport.Timmesfeld.FieldBonus

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open Matrix CFSG.Open
open CFSG.SectionRank.ClassicalEven (torusDiag torusDiag_mem_SL torusDiag_mem_SU coe_torusDiag
  torusDiag_injective)

section CharTwo

variable {K : Type} [Field K]

@[expose] def mU3 (x : K) : Matrix (Fin 3) (Fin 3) K := !![1, x, 0; 0, 1, 0; 0, 0, 1]

theorem mU3_mul (x y : K) : mU3 x * mU3 y = mU3 (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mU3, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem mU3_zero : mU3 (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mU3]

@[expose] def glU3 (x : K) : GL (Fin 3) K :=
  ⟨mU3 x, mU3 (-x), by rw [mU3_mul, add_neg_cancel, mU3_zero],
    by rw [mU3_mul, neg_add_cancel, mU3_zero]⟩

theorem det_mU3 (x : K) : (mU3 x).det = 1 := by simp [mU3, det_fin_three]

theorem glU3_mem (x : K) : glU3 x ∈ StatedSL 3 K := Subgroup.subset_closure (det_mU3 x)

@[expose] def uHom3 (K : Type) [Field K] : Multiplicative K →* GL (Fin 3) K where
  toFun x := glU3 (Multiplicative.toAdd x)
  map_one' := Units.ext (by simp [glU3, mU3_zero])
  map_mul' x y := Units.ext (by
    simp only [toAdd_mul, glU3, Units.val_mul, mU3_mul])

theorem uHom3_apply (x : Multiplicative K) : uHom3 K x = glU3 (Multiplicative.toAdd x) := rfl

theorem glU3_conj (d : Fin 3 → Kˣ) (t : K) :
    torusDiag d * glU3 t * (torusDiag d)⁻¹ = glU3 ((d 0 : K) * (d 1 : K)⁻¹ * t) := by
  refine Units.ext ?_
  rw [← map_inv, Units.val_mul, Units.val_mul, coe_torusDiag, coe_torusDiag]
  show _ * mU3 t * _ = mU3 _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mU3, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm, mul_left_comm] <;>
      (left; ring)

theorem wGeTwoSL3Even [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1) :
    2 ≤ CFSG.Open.GLATwoLocalRank 3 ↥(StatedSL 3 K) := by
  obtain ⟨ω, hω⟩ := exists_cuberoot_of_dvd h3
  have hconj : ∀ (d : Fin 3 → Kˣ) (g : GL (Fin 3) K), g ∈ (uHom3 K).range →
      torusDiag d * g * (torusDiag d)⁻¹ ∈ (uHom3 K).range := by
    rintro d _ ⟨x, rfl⟩
    exact ⟨Multiplicative.ofAdd ((d 0 : K) * (d 1 : K)⁻¹ * Multiplicative.toAdd x),
      by simp only [uHom3_apply, glU3_conj, toAdd_ofAdd]⟩
  have hnorm : ∀ d : Fin 3 → Kˣ,
      torusDiag d ∈ Subgroup.normalizer (((uHom3 K).range : Subgroup (GL (Fin 3) K)) : Set _) := by
    intro d
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj d h hh, fun hh => ?_⟩
    have := hconj d⁻¹ _ hh
    rwa [map_inv, inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, ← mul_assoc,
      inv_mul_cancel, one_mul] at this
  refine two_le_glaTwoLocalRank_of_torus hω
    (torusDiag_mem_SL (by simp [Fin.prod_univ_three])) (torusDiag_mem_SL (by simp [Fin.prod_univ_three]))
    (T := (uHom3 K).range) ?_ ?_ ?_ (hnorm _) (hnorm _)
  · rintro _ ⟨x, rfl⟩
    rw [uHom3_apply]
    exact glU3_mem _
  · intro h
    have h1 : uHom3 K (Multiplicative.ofAdd 1) = 1 :=
      (Subgroup.eq_bot_iff_forall _).1 h _ ⟨_, rfl⟩
    have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1) h1
    simp [uHom3_apply, glU3, mU3] at this
  · rintro ⟨_, x, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (uHom3 K x) ^ (2 ^ 1) = 1
    have hx : x ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      simp [two_smul, CharTwo.add_self_eq_zero]
    rw [pow_one, ← map_pow, hx, map_one]

end CharTwo

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
