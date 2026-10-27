module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Algebra.Polynomial.SpecificDegree

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG.LieType.Chevalley Polynomial

theorem pow_apply_of_apply_one_zero_eq_zero {R : Type*} [CommRing R]
    {M : Matrix (Fin 2) (Fin 2) R} (hM : M 1 0 = 0) (n : ℕ) :
    (M ^ n) 1 0 = 0 ∧ (M ^ n) 0 0 = M 0 0 ^ n ∧ (M ^ n) 1 1 = M 1 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, hM]
    exact ⟨by ring, by ring, by ring⟩

theorem sq_eq_trace_smul_sub_one {F : Type*} [Field F] (A : SL2 F) :
    ((A ^ 2 : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) • (A : Matrix (Fin 2) (Fin 2) F) - 1 := by
  have hdet := det_SL2 A
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-1 : F) * hdet
  · ring
  · ring
  · linear_combination (-1 : F) * hdet

variable {K : Type*} [Field K]

theorem two_dvd_natCard_of_charP_two [Finite K] [CharP K 2] : 2 ∣ Nat.card K := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact (CharP.cast_eq_zero_iff K 2 _).1 (FiniteField.cast_card_eq_zero K)

theorem three_le_natCard_add_one [Finite K] : 3 ≤ Nat.card K + 1 := by
  have := Finite.one_lt_card (α := K)
  omega

theorem apply_one_zero_ne_zero_of_orderOf_eq [Finite K] [CharP K 2] {A : SL2 K}
    (hA : orderOf A = Nat.card K + 1) : (A : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
  intro hc
  have hdet := det_SL2 A
  rw [hc, mul_zero, sub_zero] at hdet
  have hunit : ∀ x : K, x ≠ 0 → x ^ (Nat.card K - 1) = 1 := fun x hx => by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one x hx
  obtain ⟨h1, h2, h3⟩ := pow_apply_of_apply_one_zero_eq_zero hc (Nat.card K - 1)
  rw [hunit _ (left_ne_zero_of_mul_eq_one hdet)] at h2
  rw [hunit _ (right_ne_zero_of_mul_eq_one hdet)] at h3
  rw [← Matrix.SpecialLinearGroup.coe_pow] at h1 h2 h3
  have hB : (A ^ (Nat.card K - 1)) ^ 2 = 1 := by
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp only [sq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h1, h2,
        h3, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, Matrix.one_apply_ne,
        ne_eq, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true,
        mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, CharTwo.add_self_eq_zero]
  rw [← pow_mul] at hB
  have hdvd := orderOf_dvd_of_pow_eq_one hB
  rw [hA] at hdvd
  have h2q := two_dvd_natCard_of_charP_two (K := K)
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have h4 : Nat.card K + 1 ∣ 4 := by
    have h5 := Nat.dvd_sub (dvd_mul_left (Nat.card K + 1) 2) hdvd
    rwa [show 2 * (Nat.card K + 1) - (Nat.card K - 1) * 2 = 4 by omega] at h5
  have h4' := Nat.le_of_dvd (by norm_num) h4
  obtain ⟨k, hk⟩ := h2q
  have hk1 : k = 1 := by omega
  rw [hk, hk1] at h4
  exact absurd h4 (by decide)

theorem diag_matrix_identity {F : Type*} [Field F] {a b c d L M : F} (hc : c ≠ 0)
    (hdet : a * d - b * c = 1) (hl : L ^ 2 - (a + d) * L + 1 = 0) (hLM : L * M = 1)
    (hδ : L - M ≠ 0) :
    !![a, b; c, d] * !![(L - d) / (c * (L - M)), M - d; 1 / (L - M), c] =
      !![(L - d) / (c * (L - M)), M - d; 1 / (L - M), c] * !![L, 0; 0, M] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
    linear_combination (-1 : F) * hl - hdet
  · linear_combination (-M ^ 2) * hl - hdet + (L * M + 1 - a * M - d * M) * hLM
  · field_simp
    ring
  · ring

theorem exists_inv_mul_mul_eq_HSL {F : Type*} [Field F] (A : SL2 F)
    (hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) (l : Fˣ)
    (hl : (l : F) ^ 2 - Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) * l + 1 = 0)
    (hll : (l : F) ≠ ((l⁻¹ : Fˣ) : F)) : ∃ P : SL2 F, P⁻¹ * A * P = HSL l := by
  have hLM : (l : F) * ((l⁻¹ : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hδ : (l : F) - ((l⁻¹ : Fˣ) : F) ≠ 0 := sub_ne_zero.2 hll
  have hdet := det_SL2 A
  rw [Matrix.trace_fin_two] at hl
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1
  set L := (l : F)
  set M := ((l⁻¹ : Fˣ) : F)
  have hPdet : (!![(L - d) / (c * (L - M)), M - d; 1 / (L - M), c] :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring
  set P : SL2 F := ⟨_, hPdet⟩ with hPdef
  have hPcoe : (P : Matrix (Fin 2) (Fin 2) F) =
      !![(L - d) / (c * (L - M)), M - d; 1 / (L - M), c] := rfl
  refine ⟨P, ?_⟩
  have hAP : A * P = P * HSL l := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_HSL, hPcoe,
      Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) F)]
    exact diag_matrix_identity hc hdet hl hLM hδ
  rw [mul_assoc, hAP, inv_mul_cancel_left]

theorem HSL_pow {F : Type*} [Field F] (l : Fˣ) (n : ℕ) : (HSL l : SL2 F) ^ n = HSL (l ^ n) := by
  induction n with
  | zero =>
    refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_HSL]
  | succ n ih =>
    rw [pow_succ, ih]
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two,
        pow_succ, mul_comm]

section Extension

variable [Finite K] [CharP K 2]

instance charP_extension_two : CharP (FiniteField.Extension K 2 2) 2 :=
  charP_of_injective_algebraMap (algebraMap K (FiniteField.Extension K 2 2)).injective 2

theorem exists_sq_sub_mul_add_one_eq_zero (t : K) :
    ∃ l : FiniteField.Extension K 2 2,
      l ^ 2 - algebraMap K (FiniteField.Extension K 2 2) t * l + 1 = 0 := by
  classical
  set f : K[X] := C 1 * X ^ 2 + C (-t) * X + C 1 with hf
  have hdeg : f.natDegree = 2 := natDegree_quadratic one_ne_zero
  have heval : ∀ x : FiniteField.Extension K 2 2,
      eval x (f.map (algebraMap K (FiniteField.Extension K 2 2))) =
        x ^ 2 - algebraMap K (FiniteField.Extension K 2 2) t * x + 1 := by
    intro x
    simp [hf]
    ring
  by_cases hroot : ∃ x : K, f.IsRoot x
  · obtain ⟨x, hx⟩ := hroot
    have hx' : x ^ 2 - t * x + 1 = 0 := by
      have h := hx.eq_zero
      simp only [hf, eval_add, eval_mul, eval_C, eval_pow, eval_X] at h
      linear_combination h
    refine ⟨algebraMap K _ x, ?_⟩
    rw [← map_pow, ← map_mul, ← map_sub, ← map_one (algebraMap K (FiniteField.Extension K 2 2)),
      ← map_add, hx', map_zero]
  · push Not at hroot
    have hirr : Irreducible f :=
      irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hroot
    have hdvd : f ∣ X ^ Nat.card K ^ 2 - X :=
      (hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).1 (by rw [hdeg])
    have hne : (X ^ Nat.card K ^ 2 - X : K[X]) ≠ 0 :=
      FiniteField.X_pow_card_pow_sub_X_ne_zero K two_ne_zero Finite.one_lt_card
    have hsplit : (f.map (algebraMap K (FiniteField.Extension K 2 2))).Splits :=
      Splits.of_dvd (IsSplittingField.splits (FiniteField.Extension K 2 2) _)
        (Polynomial.map_ne_zero hne) (Polynomial.map_dvd _ hdvd)
    have hf0 : f ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; exact absurd hdeg (by decide)
    have hdeg' : (f.map (algebraMap K (FiniteField.Extension K 2 2))).degree ≠ 0 := by
      rw [degree_map, degree_eq_natDegree hf0, hdeg]
      decide
    obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero hdeg'
    exact ⟨x, by rw [← heval]; exact hx⟩

theorem frob_eq_self_iff (x : FiniteField.Extension K 2 2) :
    FiniteField.Extension.frob K 2 2 x = x ↔
      x ∈ Set.range (algebraMap K (FiniteField.Extension K 2 2)) := by
  constructor
  · intro hx
    rw [← IntermediateField.mem_bot, IsGalois.mem_bot_iff_fixed]
    intro g
    obtain ⟨i, -, rfl⟩ := FiniteField.Extension.exists_frob_pow_eq K 2 2 g
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
  · rintro ⟨a, rfl⟩
    exact (FiniteField.Extension.frob K 2 2).commutes a

end Extension

theorem exists_map_eq_of_map_eq {K₀ : Type*} [Field K₀] (ι : K₀ →+* K) (σ : K →+* K)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) (B : SL2 K)
    (hB : Matrix.SpecialLinearGroup.map σ B = B) :
    ∃ B₀ : SL2 K₀, Matrix.SpecialLinearGroup.map ι B₀ = B := by
  have hent : ∀ i j, ∃ b : K₀, ι b = (B : Matrix (Fin 2) (Fin 2) K) i j := fun i j => by
    refine (hfix _).1 ?_
    have h := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) i j) hB
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using h
  choose b hb using hent
  have hmap : ι.mapMatrix (Matrix.of b) = (B : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    simp [hb]
  have hdet : (Matrix.of b).det = 1 := by
    apply ι.injective
    rw [RingHom.map_det, hmap, map_one]
    exact B.2
  set B₀ : SL2 K₀ := ⟨Matrix.of b, hdet⟩ with hB₀
  have hB₀coe : (B₀ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.of b := rfl
  refine ⟨B₀, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
  rw [Matrix.SpecialLinearGroup.map_apply_coe, hB₀coe, hmap]

section Torus

variable [Finite K] [CharP K 2]

theorem eq_one_of_sq_eq_one_of_charTwo {F : Type*} [Field F] [CharP F 2] {x : F}
    (h : x ^ 2 = 1) : x = 1 :=
  CharTwo.sq_injective (show x ^ 2 = 1 ^ 2 by rw [h, one_pow])

theorem exists_inv_mul_map_mul_eq_HSL {A : SL2 K} (hA : orderOf A = Nat.card K + 1) :
    ∃ l : (FiniteField.Extension K 2 2)ˣ, ∃ P : SL2 (FiniteField.Extension K 2 2),
      (l : FiniteField.Extension K 2 2) ^ 2 -
          algebraMap K _ (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) * l + 1 = 0 ∧
      l ≠ 1 ∧ l ^ (Nat.card K + 1) = 1 ∧
      P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K (FiniteField.Extension K 2 2)) A * P =
        HSL l := by
  have hc := apply_one_zero_ne_zero_of_orderOf_eq hA
  obtain ⟨x, hx⟩ :=
    exists_sq_sub_mul_add_one_eq_zero (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K))
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hx1 : x ≠ 1 := by
    rintro rfl
    have ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) = 0 := by
      apply (algebraMap K (FiniteField.Extension K 2 2)).injective
      rw [map_zero]
      linear_combination (-1 : FiniteField.Extension K 2 2) * hx +
        (CharTwo.two_eq_zero : (2 : FiniteField.Extension K 2 2) = 0)
    have hA2 : A ^ 2 = 1 := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [sq_eq_trace_smul_sub_one, ht, zero_smul, zero_sub, Matrix.neg_apply, CharTwo.neg_eq,
        Matrix.SpecialLinearGroup.coe_one]
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) hA2
    have h3 := three_le_natCard_add_one (K := K)
    omega
  set l : (FiniteField.Extension K 2 2)ˣ := Units.mk0 x hx0 with hldef
  have hlx : (l : FiniteField.Extension K 2 2) = x := rfl
  have hll : (l : FiniteField.Extension K 2 2) ≠ ((l⁻¹ : (FiniteField.Extension K 2 2)ˣ) :
      FiniteField.Extension K 2 2) := by
    intro h
    have h2 : (l : FiniteField.Extension K 2 2) * l = 1 := by
      conv_lhs => rhs; rw [h]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact hx1 (eq_one_of_sq_eq_one_of_charTwo (by rw [sq, ← hlx, h2]))
  have hc' : ((Matrix.SpecialLinearGroup.map (algebraMap K (FiniteField.Extension K 2 2)) A :
      SL2 (FiniteField.Extension K 2 2)) :
        Matrix (Fin 2) (Fin 2) (FiniteField.Extension K 2 2)) 1 0 ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (_root_.map_ne_zero _).2 hc
  have htr : Matrix.trace ((Matrix.SpecialLinearGroup.map
      (algebraMap K (FiniteField.Extension K 2 2)) A : SL2 (FiniteField.Extension K 2 2)) :
        Matrix (Fin 2) (Fin 2) (FiniteField.Extension K 2 2)) =
      algebraMap K _ (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.trace_fin_two,
      Matrix.trace_fin_two, Matrix.map_apply, Matrix.map_apply, map_add]
  obtain ⟨P, hP⟩ := exists_inv_mul_mul_eq_HSL _ hc' l (by rw [htr, hlx]; exact hx) hll
  refine ⟨l, P, hx, fun h => hx1 (by rw [← hlx, h, Units.val_one]), ?_, hP⟩
  have hpow : HSL l ^ (Nat.card K + 1) = 1 := by
    rw [← hP, show P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K _) A * P =
      P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K _) A * P⁻¹⁻¹ by rw [inv_inv], conj_pow,
      ← map_pow, ← hA, pow_orderOf_eq_one, map_one, mul_one, mul_inv_cancel]
  rw [HSL_pow] at hpow
  have h00 := congrArg (fun g : SL2 (FiniteField.Extension K 2 2) =>
    (g : Matrix (Fin 2) (Fin 2) (FiniteField.Extension K 2 2)) 0 0) hpow
  simp only [coe_HSL, Matrix.SpecialLinearGroup.coe_one] at h00
  exact Units.ext (by simpa using h00)

theorem centralizer_eq_zpowers_of_orderOf_eq {A : SL2 K} (hA : orderOf A = Nat.card K + 1) :
    Subgroup.centralizer {A} = Subgroup.zpowers A := by
  classical
  have hc := apply_one_zero_ne_zero_of_orderOf_eq hA
  obtain ⟨l, -, hl, hl1, hlq, -⟩ := exists_inv_mul_map_mul_eq_HSL hA
  set ι := algebraMap K (FiniteField.Extension K 2 2) with hι
  set x : FiniteField.Extension K 2 2 := Units.val l with hxl
  have hx0 : x ≠ 0 := l.ne_zero
  have hpowK : ∀ a : K, a ^ Nat.card K = a := fun a => by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  have hxq : x ^ Nat.card K * x = 1 := by
    rw [← pow_succ, hxl, ← Units.val_pow_eq_pow_val, hlq, Units.val_one]
  have hxinv : x ^ Nat.card K = x⁻¹ := eq_inv_of_mul_eq_one_left hxq
  have hxrange : x ∉ Set.range ι := by
    rintro ⟨a, ha⟩
    have hxx : x ^ Nat.card K = x := by rw [← ha, ← map_pow, hpowK]
    rw [hxx] at hxq
    exact hl1 (Units.ext (eq_one_of_sq_eq_one_of_charTwo (by rw [sq]; exact hxq)))
  have hsum : x + x⁻¹ = ι (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) := by
    field_simp
    linear_combination hl
  have hfrob : ∀ z : FiniteField.Extension K 2 2, ∀ α β : K,
      (ι α + ι β * z) ^ Nat.card K = ι α + ι β * z ^ Nat.card K := by
    intro z α β
    rw [← FiniteField.Extension.frob_apply, ← FiniteField.Extension.frob_apply, map_add, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes]
  set a := (A : Matrix (Fin 2) (Fin 2) K) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) K) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) K) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) K) 1 1
  have htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) = a + d := Matrix.trace_fin_two _
  have hdetA : a * d - b * c = 1 := det_SL2 A
  have hcomm : ∀ B ∈ Subgroup.centralizer ({A} : Set (SL2 K)),
      (B : Matrix (Fin 2) (Fin 2) K) 0 1 * c = b * (B : Matrix (Fin 2) (Fin 2) K) 1 0 ∧
      (B : Matrix (Fin 2) (Fin 2) K) 1 1 * c = (B : Matrix (Fin 2) (Fin 2) K) 0 0 * c +
        (B : Matrix (Fin 2) (Fin 2) K) 1 0 * (d - a) := by
    intro B hB
    rw [Subgroup.mem_centralizer_singleton_iff] at hB
    have h00 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hB
    have h10 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 1 0) hB
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h00 h10
    constructor
    · linear_combination h00
    · linear_combination h10
  set μ : SL2 K → FiniteField.Extension K 2 2 := fun B =>
    ι ((B : Matrix (Fin 2) (Fin 2) K) 0 0 - (B : Matrix (Fin 2) (Fin 2) K) 1 0 / c * a) +
      ι ((B : Matrix (Fin 2) (Fin 2) K) 1 0 / c) * x with hμ
  have hμq : ∀ B ∈ Subgroup.centralizer ({A} : Set (SL2 K)), μ B ^ (Nat.card K + 1) = 1 := by
    intro B hB
    obtain ⟨h1, h2⟩ := hcomm B hB
    have hdetB := det_SL2 B
    set e := (B : Matrix (Fin 2) (Fin 2) K) 0 0
    set f := (B : Matrix (Fin 2) (Fin 2) K) 0 1
    set g := (B : Matrix (Fin 2) (Fin 2) K) 1 0
    set h := (B : Matrix (Fin 2) (Fin 2) K) 1 1
    have hK : (e - g / c * a) ^ 2 + (e - g / c * a) * (g / c) * (a + d) + (g / c) ^ 2 = 1 := by
      field_simp
      linear_combination (c ^ 2) * hdetB + (c * g) * h1 - (c * e) * h2 - (g ^ 2) * hdetA
    rw [pow_succ, hμ, hfrob, hxinv]
    simp only
    have hx' : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    calc (ι (e - g / c * a) + ι (g / c) * x⁻¹) * (ι (e - g / c * a) + ι (g / c) * x) =
        ι (e - g / c * a) ^ 2 + ι (e - g / c * a) * ι (g / c) * (x + x⁻¹) +
          ι (g / c) ^ 2 * (x * x⁻¹) := by ring
      _ = 1 := by
        rw [hsum, hx', htr, mul_one, ← map_pow, ← map_mul, ← map_mul, ← map_pow, ← map_add,
          ← map_add, hK, map_one]
  have hinj : ∀ B ∈ Subgroup.centralizer ({A} : Set (SL2 K)),
      ∀ B' ∈ Subgroup.centralizer ({A} : Set (SL2 K)), μ B = μ B' → B = B' := by
    intro B hB B' hB' hBB
    obtain ⟨h1, h2⟩ := hcomm B hB
    obtain ⟨h1', h2'⟩ := hcomm B' hB'
    simp only [hμ] at hBB
    set β := (B : Matrix (Fin 2) (Fin 2) K) 1 0 / c with hβ
    set β' := (B' : Matrix (Fin 2) (Fin 2) K) 1 0 / c with hβ'
    set α := (B : Matrix (Fin 2) (Fin 2) K) 0 0 - β * a with hα
    set α' := (B' : Matrix (Fin 2) (Fin 2) K) 0 0 - β' * a with hα'
    have hg : β = β' := by
      by_contra hne
      apply hxrange
      have hne' : ι (β - β') ≠ 0 := (_root_.map_ne_zero ι).2 (sub_ne_zero.2 hne)
      have key : ι (α' - α) = ι (β - β') * x := by
        rw [map_sub ι α' α, map_sub ι β β']
        linear_combination -hBB
      exact ⟨(α' - α) / (β - β'), by rw [map_div₀, key, mul_div_cancel_left₀ _ hne']⟩
    have hg' : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = (B' : Matrix (Fin 2) (Fin 2) K) 1 0 := by
      rw [hβ, hβ'] at hg
      field_simp at hg
      exact hg
    have he : (B : Matrix (Fin 2) (Fin 2) K) 0 0 = (B' : Matrix (Fin 2) (Fin 2) K) 0 0 := by
      rw [hg] at hBB
      have h := ι.injective (add_right_cancel hBB)
      rw [hα, hα', hg] at h
      linear_combination h
    refine SL2_ext he ?_ hg' ?_
    · apply mul_right_cancel₀ hc
      rw [h1, h1', hg']
    · apply mul_right_cancel₀ hc
      rw [h2, h2', he, hg']
  have hcard : Nat.card (Subgroup.centralizer ({A} : Set (SL2 K))) ≤ Nat.card K + 1 := by
    let F : Subgroup.centralizer ({A} : Set (SL2 K)) →
        (nthRootsFinset (Nat.card K + 1) (1 : FiniteField.Extension K 2 2)) := fun B =>
      ⟨μ B, (mem_nthRootsFinset (by omega) 1).2 (hμq B B.2)⟩
    have hF : Function.Injective F := fun B B' h =>
      Subtype.ext (hinj B B.2 B' B'.2 (congrArg Subtype.val h))
    calc Nat.card (Subgroup.centralizer ({A} : Set (SL2 K))) ≤
        Nat.card (nthRootsFinset (Nat.card K + 1) (1 : FiniteField.Extension K 2 2)) :=
          Nat.card_le_card_of_injective F hF
      _ = (nthRootsFinset (Nat.card K + 1) (1 : FiniteField.Extension K 2 2)).card :=
          Nat.card_eq_finsetCard _
      _ ≤ Nat.card K + 1 := by
          rw [nthRootsFinset_def]
          exact (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)
  have hle : Subgroup.zpowers A ≤ Subgroup.centralizer {A} := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, hA]
  exact hcard

theorem SL2_map_injective {F M : Type*} [Field F] [Field M] (ι : F →+* M) :
    Function.Injective (Matrix.SpecialLinearGroup.map ι : SL2 F →* SL2 M) := fun A B h =>
  Matrix.SpecialLinearGroup.ext _ _ fun i j => ι.injective (by
    have h' := congrArg (fun g : SL2 M => (g : Matrix (Fin 2) (Fin 2) M) i j) h
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using h')

theorem orderOf_HSL {F : Type*} [Field F] (l : Fˣ) : orderOf (HSL l : SL2 F) = orderOf l := by
  refine orderOf_eq_orderOf_iff.2 fun n => ?_
  rw [HSL_pow]
  constructor
  · intro h
    have h00 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [coe_HSL, Matrix.SpecialLinearGroup.coe_one] at h00
    exact Units.ext (by simpa using h00)
  · intro h
    rw [h]
    refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_HSL]

theorem exists_orderOf_eq_natCard_add_one : ∃ A : SL2 K, orderOf A = Nat.card K + 1 := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hK₂ : Nat.card (FiniteField.Extension K 2 2) = Nat.card K ^ 2 :=
    FiniteField.natCard_extension K 2 2
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (FiniteField.Extension K 2 2)ˣ)
  rw [Nat.card_units, hK₂] at hg
  have hfac : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    ring_nf
    omega
  set l := g ^ (Nat.card K - 1) with hldef
  have hl : orderOf l = Nat.card K + 1 := by
    rw [hldef, orderOf_pow_of_dvd (by omega) (by rw [hg, hfac]; exact dvd_mul_right _ _), hg,
      hfac, Nat.mul_div_cancel_left _ (by omega)]
  have hlq : (l : FiniteField.Extension K 2 2) ^ Nat.card K * l = 1 := by
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, ← hl, pow_orderOf_eq_one, Units.val_one]
  have hpow2 : ∀ z : FiniteField.Extension K 2 2, z ^ Nat.card K ^ 2 = z := fun z => by
    have := Fintype.ofFinite (FiniteField.Extension K 2 2)
    rw [← hK₂, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card z
  have ht : (l : FiniteField.Extension K 2 2) + (l : FiniteField.Extension K 2 2) ^ Nat.card K ∈
      Set.range (algebraMap K (FiniteField.Extension K 2 2)) := by
    rw [← frob_eq_self_iff, map_add, FiniteField.Extension.frob_apply,
      FiniteField.Extension.frob_apply, ← pow_mul, ← sq (Nat.card K), hpow2, add_comm]
  obtain ⟨t, ht⟩ := ht
  have hdetA : (!![0, -1; 1, t] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    ring
  set A : SL2 K := ⟨!![0, -1; 1, t], hdetA⟩ with hAdef
  have hAcoe : (A : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, t] := rfl
  have hc : ((Matrix.SpecialLinearGroup.map (algebraMap K (FiniteField.Extension K 2 2)) A :
      SL2 (FiniteField.Extension K 2 2)) :
        Matrix (Fin 2) (Fin 2) (FiniteField.Extension K 2 2)) 1 0 ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, hAcoe]
    simp
  have htr : Matrix.trace ((Matrix.SpecialLinearGroup.map
      (algebraMap K (FiniteField.Extension K 2 2)) A : SL2 (FiniteField.Extension K 2 2)) :
        Matrix (Fin 2) (Fin 2) (FiniteField.Extension K 2 2)) =
      algebraMap K _ t := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.trace_fin_two,
      Matrix.map_apply, Matrix.map_apply, hAcoe]
    simp
  have hlroot : (l : FiniteField.Extension K 2 2) ^ 2 -
      Matrix.trace ((Matrix.SpecialLinearGroup.map (algebraMap K (FiniteField.Extension K 2 2)) A :
        SL2 (FiniteField.Extension K 2 2)) :
          Matrix (Fin 2) (Fin 2) (FiniteField.Extension K 2 2)) * l + 1 = 0 := by
    rw [htr, ht]
    linear_combination -hlq
  have hll : (l : FiniteField.Extension K 2 2) ≠
      ((l⁻¹ : (FiniteField.Extension K 2 2)ˣ) : FiniteField.Extension K 2 2) := by
    intro h
    have h2 : l ^ 2 = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
      conv_lhs => rhs; rw [h]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h3 := orderOf_le_of_pow_eq_one (by norm_num) h2
    omega
  obtain ⟨P, hP⟩ := exists_inv_mul_mul_eq_HSL _ hc l hlroot hll
  refine ⟨A, ?_⟩
  rw [← orderOf_injective _ (SL2_map_injective (algebraMap K (FiniteField.Extension K 2 2))) A]
  have hA₂ : Matrix.SpecialLinearGroup.map (algebraMap K (FiniteField.Extension K 2 2)) A =
      MulAut.conj P (HSL l) := by
    rw [MulAut.conj_apply, ← hP]
    group
  rw [hA₂, ← MulEquiv.coe_toMonoidHom,
    orderOf_injective _ (MulAut.conj P).injective (HSL l), orderOf_HSL, hl]

end Torus

end CFSG.SeitzReduction.F4Pilot
