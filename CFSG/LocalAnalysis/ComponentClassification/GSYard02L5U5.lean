module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02SD
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Simple

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG CFSG.Open CFSG.Open.StatedAPI Matrix

section Blocks

variable {R : Type} [CommRing R]

private def blk (A B : Matrix (Fin 2) (Fin 2) R) (c : R) : Matrix (Fin 5) (Fin 5) R :=
  Matrix.of ![![A 0 0, A 0 1, 0, 0, 0], ![A 1 0, A 1 1, 0, 0, 0], ![0, 0, B 0 0, B 0 1, 0],
    ![0, 0, B 1 0, B 1 1, 0], ![0, 0, 0, 0, c]]

private theorem blk_mul (A B A' B' : Matrix (Fin 2) (Fin 2) R) (c c' : R) :
    blk A B c * blk A' B' c' = blk (A * A') (B * B') (c * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_two]

private theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

private theorem det_blk (A B : Matrix (Fin 2) (Fin 2) R) (c : R) :
    (blk A B c).det = A.det * B.det * c := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, blk, Fin.succAbove]
  ring

private theorem blk_injective {A B A' B' : Matrix (Fin 2) (Fin 2) R} {c c' : R}
    (h : blk A B c = blk A' B' c') : A = A' ∧ B = B' := by
  have e : ∀ i j : Fin 5, blk A B c i j = blk A' B' c' i j := fun i j => by rw [h]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [blk] using e 0 0
    · simpa [blk] using e 0 1
    · simpa [blk] using e 1 0
    · simpa [blk] using e 1 1
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [blk] using e 2 2
    · simpa [blk] using e 2 3
    · simpa [blk] using e 3 2
    · simpa [blk] using e 3 3

private def sw : Matrix (Fin 5) (Fin 5) R :=
  Matrix.of ![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1]]

private theorem sw_mul_blk (A B : Matrix (Fin 2) (Fin 2) R) (c : R) :
    sw * blk A B c = blk B A c * sw := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sw, blk, Matrix.mul_apply, Fin.sum_univ_five]

private theorem sw_mul_self : (sw : Matrix (Fin 5) (Fin 5) R) * sw = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sw, Matrix.mul_apply, Fin.sum_univ_five]

private theorem det_sw : (sw : Matrix (Fin 5) (Fin 5) R).det = 1 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, sw, Fin.succAbove]

private theorem blk_transpose (A B : Matrix (Fin 2) (Fin 2) R) (c : R) :
    (blk A B c)ᵀ = blk Aᵀ Bᵀ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

private theorem blk_map {S : Type} [CommRing S] (f : R →+* S) (A B : Matrix (Fin 2) (Fin 2) R)
    (c : R) : (blk A B c).map f = blk (A.map f) (B.map f) (f c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

private theorem sw_transpose : (sw : Matrix (Fin 5) (Fin 5) R)ᵀ = sw := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sw]

private theorem sw_map {S : Type} [CommRing S] (f : R →+* S) :
    (sw : Matrix (Fin 5) (Fin 5) R).map f = sw := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sw]

end Blocks

section Embedding

variable (K : Type) [Field K]

private def uu (p : GL (Fin 2) K × GL (Fin 2) K) : Kˣ :=
  (Matrix.GeneralLinearGroup.det p.1 * Matrix.GeneralLinearGroup.det p.2)⁻¹

private theorem uu_mul (p q : GL (Fin 2) K × GL (Fin 2) K) : uu K (p * q) = uu K p * uu K q := by
  simp only [uu, Prod.fst_mul, Prod.snd_mul, map_mul]
  rw [mul_mul_mul_comm, mul_inv]

private theorem uu_swap (p : GL (Fin 2) K × GL (Fin 2) K) : uu K (p.2, p.1) = uu K p := by
  simp only [uu]
  rw [mul_comm]

private def embGL : GL (Fin 2) K × GL (Fin 2) K →* GL (Fin 5) K :=
  MonoidHom.mk' (fun p => ⟨blk (p.1 : Matrix (Fin 2) (Fin 2) K) p.2 ((uu K p : Kˣ) : K),
      blk (((p.1⁻¹ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K)
        (((p.2⁻¹ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) (((uu K p)⁻¹ : Kˣ) : K),
      by rw [blk_mul, Units.mul_inv, Units.mul_inv, Units.mul_inv, blk_one],
      by rw [blk_mul, Units.inv_mul, Units.inv_mul, Units.inv_mul, blk_one]⟩)
    (fun p q => Units.ext (by
      show blk (((p * q).1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          (((p * q).2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ((uu K (p * q) : Kˣ) : K) =
        blk (p.1 : Matrix (Fin 2) (Fin 2) K) p.2 ((uu K p : Kˣ) : K) *
          blk (q.1 : Matrix (Fin 2) (Fin 2) K) q.2 ((uu K q : Kˣ) : K)
      simp only [blk_mul, Prod.fst_mul, Prod.snd_mul, Units.val_mul, uu_mul]))

private theorem coe_embGL (p : GL (Fin 2) K × GL (Fin 2) K) :
    ((embGL K p : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blk (p.1 : Matrix (Fin 2) (Fin 2) K) p.2 ((uu K p : Kˣ) : K) := rfl

private theorem det_embGL (p : GL (Fin 2) K × GL (Fin 2) K) :
    ((embGL K p : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
  rw [coe_embGL, det_blk, ← Matrix.GeneralLinearGroup.val_det_apply,
    ← Matrix.GeneralLinearGroup.val_det_apply, ← Units.val_mul, ← Units.val_mul]
  have h : Matrix.GeneralLinearGroup.det p.1 * Matrix.GeneralLinearGroup.det p.2 * uu K p = 1 :=
    mul_inv_cancel _
  rw [h, Units.val_one]

private theorem embGL_injective : Function.Injective (embGL K) := by
  intro p q h
  have h1 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K)) h
  obtain ⟨hA, hB⟩ := blk_injective h1
  exact Prod.ext (Units.ext hA) (Units.ext hB)

private def swGL : GL (Fin 5) K := ⟨sw, sw, sw_mul_self, sw_mul_self⟩

private theorem swGL_mul_self : swGL K * swGL K = 1 := Units.ext sw_mul_self

private theorem swGL_mul_embGL (p : GL (Fin 2) K × GL (Fin 2) K) :
    swGL K * embGL K p * swGL K = embGL K (p.2, p.1) := by
  refine Units.ext ?_
  show sw * blk (p.1 : Matrix (Fin 2) (Fin 2) K) p.2 ((uu K p : Kˣ) : K) * sw =
    blk (p.2 : Matrix (Fin 2) (Fin 2) K) p.1 ((uu K (p.2, p.1) : Kˣ) : K)
  rw [sw_mul_blk, mul_assoc, sw_mul_self, mul_one, uu_swap]

private theorem embGL_ne_swGL (p : GL (Fin 2) K × GL (Fin 2) K) : embGL K p ≠ swGL K := by
  intro h
  have := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 0 2) h
  simp [coe_embGL, blk, swGL, sw] at this

private theorem embGL_mem_statedSL (p : GL (Fin 2) K × GL (Fin 2) K) :
    embGL K p ∈ StatedSL 5 K := mem_statedSL_of_det (det_embGL K p)

private theorem swGL_mem_statedSL : swGL K ∈ StatedSL 5 K :=
  mem_statedSL_of_det (show (sw : Matrix (Fin 5) (Fin 5) K).det = 1 from det_sw)

end Embedding

section Linear

variable {K : Type} [Field K]

private theorem pow_five_eq_one_of_scalar {z : GL (Fin 5) K} (hz : z ∈ StatedScalars (Fin 5) K)
    (hdet : (z : Matrix (Fin 5) (Fin 5) K).det = 1) : z ^ 5 = 1 := by
  obtain ⟨c, rfl⟩ := hz
  have h1 : (c : K) ^ 5 = 1 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact hdet
  rw [← map_pow]
  have h2 : c ^ 5 = 1 := Units.ext (by simpa using h1)
  rw [h2, map_one]

private theorem hker_statedSL (x : ↥(StatedSL 5 K))
    (hx : QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf (StatedSL 5 K)) x = 1) :
    x ^ 5 = 1 := by
  have h1 : x ∈ (StatedScalars (Fin 5) K).subgroupOf (StatedSL 5 K) :=
    (QuotientGroup.eq_one_iff x).mp hx
  have h2 : (x : GL (Fin 5) K) ∈ StatedScalars (Fin 5) K := h1
  have h3 := pow_five_eq_one_of_scalar h2 (det_of_mem_statedSL x.2)
  exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h3)

private def rGL : GL (Fin 2) K :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private theorem rGL_mul_self : (rGL : GL (Fin 2) K) * rGL = 1 := by
  refine Units.ext ?_
  show (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 0, -1] = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem rGL_ne_one (h2 : (2 : K) ≠ 0) : (rGL : GL (Fin 2) K) ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 1) h
  simp [rGL] at this
  exact h2 (by linear_combination -this)

private theorem rGL_ne_neg_one (h2 : (2 : K) ≠ 0) : (rGL : GL (Fin 2) K) ≠ -1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [rGL] at this
  exact h2 (by linear_combination this)

end Linear

section NumberTheory

private theorem two_adic_factorization {k m : ℕ} (hm : Odd m) :
    (2 ^ k * m).factorization 2 = k := by
  have h1 : (2 ^ k).factorization 2 = k := by
    rw [Nat.Prime.factorization_pow Nat.prime_two]; simp
  have h2 : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat
  rw [Nat.factorization_mul (by positivity) hm.pos.ne', Finsupp.add_apply, h1, h2, add_zero]

private theorem exists_cofactor_linear (e : ℕ) (he : 1 ≤ e) :
    ∃ m : ℕ, Odd m ∧
      (2 * e + 1) ^ 10 * (4 * e * (e + 1)) * (2 * e * (4 * e ^ 2 + 6 * e + 3)) *
          (8 * e * (e + 1) * (2 * e ^ 2 + 2 * e + 1)) *
          (2 * e * (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5)) =
        2 ^ (2 * (8 * e ^ 2 * (e + 1) * (2 * e + 1)).factorization 2 + 1) * m := by
  obtain ⟨s, e', he', hes⟩ := Nat.exists_eq_two_pow_mul_odd (show e ≠ 0 by omega)
  obtain ⟨t, w', hw', hwt⟩ := Nat.exists_eq_two_pow_mul_odd (show e + 1 ≠ 0 by omega)
  have hGL : 8 * e ^ 2 * (e + 1) * (2 * e + 1) =
      2 ^ (3 + 2 * s + t) * (e' ^ 2 * w' * (2 * e + 1)) := by
    calc 8 * e ^ 2 * (e + 1) * (2 * e + 1)
        = 8 * (2 ^ s * e') ^ 2 * (2 ^ t * w') * (2 * e + 1) := by rw [← hes, ← hwt]
      _ = 2 ^ (3 + 2 * s + t) * (e' ^ 2 * w' * (2 * e + 1)) := by ring
  have hodd : Odd (e' ^ 2 * w' * (2 * e + 1)) := (he'.pow.mul hw').mul ⟨e, rfl⟩
  rw [hGL, two_adic_factorization hodd]
  have o1 : Odd (2 * e + 1) := ⟨e, rfl⟩
  have o2 : Odd (4 * e ^ 2 + 6 * e + 3) := ⟨2 * e ^ 2 + 3 * e + 1, by ring⟩
  have o3 : Odd (2 * e ^ 2 + 2 * e + 1) := ⟨e ^ 2 + e, by ring⟩
  have o4 : Odd (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5) :=
    ⟨8 * e ^ 4 + 20 * e ^ 3 + 20 * e ^ 2 + 10 * e + 2, by ring⟩
  refine ⟨e' ^ 4 * w' ^ 2 * ((2 * e + 1) ^ 10 * (4 * e ^ 2 + 6 * e + 3) * (2 * e ^ 2 + 2 * e + 1) *
    (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5)), ?_, ?_⟩
  · exact (he'.pow.mul hw'.pow).mul (((o1.pow.mul o2).mul o3).mul o4)
  · calc (2 * e + 1) ^ 10 * (4 * e * (e + 1)) * (2 * e * (4 * e ^ 2 + 6 * e + 3)) *
          (8 * e * (e + 1) * (2 * e ^ 2 + 2 * e + 1)) *
          (2 * e * (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5))
        = 2 ^ 7 * e ^ 4 * (e + 1) ^ 2 * ((2 * e + 1) ^ 10 * (4 * e ^ 2 + 6 * e + 3) *
          (2 * e ^ 2 + 2 * e + 1) * (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5)) := by
          ring
      _ = 2 ^ 7 * (2 ^ s * e') ^ 4 * (2 ^ t * w') ^ 2 * ((2 * e + 1) ^ 10 *
          (4 * e ^ 2 + 6 * e + 3) * (2 * e ^ 2 + 2 * e + 1) *
          (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5)) := by rw [← hes, ← hwt]
      _ = 2 ^ (2 * (3 + 2 * s + t) + 1) * (e' ^ 4 * w' ^ 2 * ((2 * e + 1) ^ 10 *
          (4 * e ^ 2 + 6 * e + 3) * (2 * e ^ 2 + 2 * e + 1) *
          (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5))) := by ring

end NumberTheory

section LinearCard

variable {K : Type} [Field K] [Finite K]

private theorem card_GL2 :
    Nat.card (GL (Fin 2) K) = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
  let := Fintype.ofFinite K
  rw [Matrix.card_GL_field, Fin.prod_univ_two]
  simp [Nat.card_eq_fintype_card]

private theorem prod_fin5 (q : ℕ) : ∏ i : Fin 5, (q ^ 5 - q ^ (i : ℕ)) =
    (q ^ 5 - 1) * (q ^ 5 - q) * (q ^ 5 - q ^ 2) * (q ^ 5 - q ^ 3) * (q ^ 5 - q ^ 4) := by
  simp [Fin.prod_univ_five]

private theorem card_statedSL_five (e : ℕ) (hq : Nat.card K = 2 * e + 1) (he : 1 ≤ e) :
    Nat.card (StatedSL 5 K) = (2 * e + 1) ^ 10 * (4 * e * (e + 1)) *
      (2 * e * (4 * e ^ 2 + 6 * e + 3)) * (8 * e * (e + 1) * (2 * e ^ 2 + 2 * e + 1)) *
      (2 * e * (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5)) := by
  let := Fintype.ofFinite K
  rw [card_statedSL, Matrix.card_SL_field, prod_fin5]
  simp only [← Nat.card_eq_fintype_card, hq]
  have h5 : (2 * e + 1) ^ 5 - 1 = 2 * e * (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h4 : (2 * e + 1) ^ 5 - (2 * e + 1) =
      (2 * e + 1) * (8 * e * (e + 1) * (2 * e ^ 2 + 2 * e + 1)) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h3 : (2 * e + 1) ^ 5 - (2 * e + 1) ^ 2 =
      (2 * e + 1) ^ 2 * (2 * e * (4 * e ^ 2 + 6 * e + 3)) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h2 : (2 * e + 1) ^ 5 - (2 * e + 1) ^ 3 = (2 * e + 1) ^ 3 * (4 * e * (e + 1)) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h1 : (2 * e + 1) ^ 5 - (2 * e + 1) ^ 4 = (2 * e + 1) ^ 4 * (2 * e) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h0 : 2 * e + 1 - 1 = 2 * e := by omega
  rw [h5, h4, h3, h2, h1, h0]
  rw [show (2 * e * (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5)) *
      ((2 * e + 1) * (8 * e * (e + 1) * (2 * e ^ 2 + 2 * e + 1))) *
      ((2 * e + 1) ^ 2 * (2 * e * (4 * e ^ 2 + 6 * e + 3))) *
      ((2 * e + 1) ^ 3 * (4 * e * (e + 1))) * ((2 * e + 1) ^ 4 * (2 * e)) =
      (2 * e) * ((2 * e + 1) ^ 10 * (4 * e * (e + 1)) * (2 * e * (4 * e ^ 2 + 6 * e + 3)) *
        (8 * e * (e + 1) * (2 * e ^ 2 + 2 * e + 1)) *
        (2 * e * (16 * e ^ 4 + 40 * e ^ 3 + 40 * e ^ 2 + 20 * e + 5))) by ring]
  exact Nat.mul_div_cancel_left _ (by omega)

private theorem card_GL2_eq (e : ℕ) (hq : Nat.card K = 2 * e + 1) :
    Nat.card (GL (Fin 2) K) = 8 * e ^ 2 * (e + 1) * (2 * e + 1) := by
  rw [card_GL2, hq]
  have h1 : (2 * e + 1) ^ 2 - 1 = 4 * e * (e + 1) := Nat.sub_eq_of_eq_add (by ring)
  have h2 : (2 * e + 1) ^ 2 - (2 * e + 1) = 2 * e * (2 * e + 1) := Nat.sub_eq_of_eq_add (by ring)
  rw [h1, h2]
  ring

private theorem exists_odd_card_statedSL_five (hodd : Odd (Nat.card K)) (h3 : 3 ≤ Nat.card K) :
    ∃ m : ℕ, Odd m ∧ Nat.card (StatedSL 5 K) =
      2 ^ (2 * (Nat.card (GL (Fin 2) K)).factorization 2 + 1) * m := by
  obtain ⟨e, he⟩ := hodd
  have he1 : 1 ≤ e := by omega
  obtain ⟨m, hm, hmeq⟩ := exists_cofactor_linear e he1
  refine ⟨m, hm, ?_⟩
  rw [card_GL2_eq e he, card_statedSL_five e he he1]
  exact hmeq

end LinearCard

section LinearMain

variable {K : Type} [Field K] [Finite K]

private theorem ringChar_ne_two_of_odd_card (hodd : Odd (Nat.card K)) : ringChar K ≠ 2 := by
  haveI := Fintype.ofFinite K
  intro h
  have h1 := (FiniteField.even_card_iff_char_two (F := K)).mp h
  rw [← Nat.card_eq_fintype_card] at h1
  have h2 := Nat.odd_iff.mp hodd
  omega

private theorem negOne_ne_one (h2 : (2 : K) ≠ 0) : (-1 : GL (Fin 2) K) ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp at this
  exact h2 (by linear_combination -this)

private theorem sylowFourJoined_statedProj_SL5 (hodd : Odd (Nat.card K)) (h3 : 3 ≤ Nat.card K) :
    SylowFourJoined (StatedProj (StatedSL 5 K)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_card hodd)
  obtain ⟨m, hm, hcard⟩ := exists_odd_card_statedSL_five hodd h3
  have hz2 : (-1 : GL (Fin 2) K) * -1 = 1 := by simp
  have hz1 : (-1 : GL (Fin 2) K) ≠ 1 := negOne_ne_one h2
  obtain ⟨D, hzD, hrD, hD⟩ := exists_sylow_two_containing (z := (-1 : GL (Fin 2) K))
    (r := rGL) hz2 rGL_mul_self hz1 (rGL_ne_one h2) (rGL_ne_neg_one h2).symm
    (Commute.neg_one_left _)
  exact sylowFourJoined_of_wreath_embedding (StatedSL 5 K) (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (m₀ := 5) ⟨2, by norm_num⟩ hker_statedSL (embGL K)
    (embGL_injective K) (embGL_mem_statedSL K) (swGL_mem_statedSL K) (swGL_mul_self K)
    (fun g h => swGL_mul_embGL K (g, h)) (fun g h => embGL_ne_swGL K (g, h)) D hD hm hcard hzD hrD
    hz2 hz1 rGL_mul_self (rGL_ne_one h2) (rGL_ne_neg_one h2)
    (fun d _ => (Commute.neg_one_right d).eq)

end LinearMain

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K]

private def GU2 (h : UnitaryFieldData p f K) : Subgroup (GL (Fin 2) K) where
  carrier := {g | ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * 1 *
    (g : Matrix (Fin 2) (Fin 2) K) = 1}
  mul_mem' {g g'} hg hg' := by
    change (((g * g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * 1 *
      ((g * g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [Units.val_mul, conjTranspose_mul_mul]
    rw [hg]
    exact hg'
  one_mem' := by
    change (((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * 1 *
      ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    simp
  inv_mem' {g} hg := by
    have hgg : (g : Matrix (Fin 2) (Fin 2) K) *
        ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 := conjTranspose_mul_mul h (1 : Matrix (Fin 2) (Fin 2) K)
      (g : Matrix (Fin 2) (Fin 2) K) ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    change ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * 1 *
      (g : Matrix (Fin 2) (Fin 2) K) = 1 at hg
    rw [hg, hgg] at h1
    simp only [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one,
      Matrix.one_mul, Matrix.mul_one] at h1
    show ((((g⁻¹ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * 1 *
      ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [Matrix.mul_one]
    exact h1.symm

private theorem mem_GU2 {h : UnitaryFieldData p f K} {g : GL (Fin 2) K} :
    g ∈ GU2 h ↔
      ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
  show _ * 1 * _ = 1 ↔ _
  rw [Matrix.mul_one]

end Unitary

section UnitaryMain

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K]

private def embU (h : UnitaryFieldData p f K) : GU2 h × GU2 h →* GL (Fin 5) K :=
  (embGL K).comp ((GU2 h).subtype.prodMap (GU2 h).subtype)

private theorem embU_injective (h : UnitaryFieldData p f K) : Function.Injective (embU h) :=
  (embGL_injective K).comp (Subtype.val_injective.prodMap Subtype.val_injective)

private theorem uu_val (q : GL (Fin 2) K × GL (Fin 2) K) :
    ((uu K q : Kˣ) : K) =
      ((q.1 : Matrix (Fin 2) (Fin 2) K).det * (q.2 : Matrix (Fin 2) (Fin 2) K).det)⁻¹ := by
  simp [uu, Matrix.GeneralLinearGroup.val_det_apply]

private theorem bar_det_mul_det (h : UnitaryFieldData p f K) (g : GU2 h) :
    h.bar (g.1 : Matrix (Fin 2) (Fin 2) K).det * (g.1 : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have h1 := congrArg Matrix.det (mem_GU2.mp g.2)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have h2 : ((g.1 : Matrix (Fin 2) (Fin 2) K).map h.bar).det =
      h.bar (g.1 : Matrix (Fin 2) (Fin 2) K).det := by
    rw [RingHom.map_det]
    rfl
  rwa [h2] at h1

private theorem embU_mem (h : UnitaryFieldData p f K) (x : GU2 h × GU2 h) :
    embU h x ∈ StatedSU 5 (p ^ f) K := by
  refine (mem_unitarySU_iff h).mpr ⟨det_embGL K _, ?_⟩
  have hA := mem_GU2.mp x.1.2
  have hB := mem_GU2.mp x.2.2
  have hc : h.bar ((uu K (x.1.1, x.2.1) : Kˣ) : K) * ((uu K (x.1.1, x.2.1) : Kˣ) : K) = 1 := by
    rw [uu_val, map_inv₀, map_mul, ← mul_inv, mul_mul_mul_comm, bar_det_mul_det h x.1,
      bar_det_mul_det h x.2, mul_one, inv_one]
  show ((blk (x.1.1 : Matrix (Fin 2) (Fin 2) K) (x.2.1 : Matrix (Fin 2) (Fin 2) K)
      ((uu K (x.1.1, x.2.1) : Kˣ) : K)).map h.bar)ᵀ *
    blk (x.1.1 : Matrix (Fin 2) (Fin 2) K) (x.2.1 : Matrix (Fin 2) (Fin 2) K)
      ((uu K (x.1.1, x.2.1) : Kˣ) : K) = 1
  rw [blk_map, blk_transpose, blk_mul, hA, hB, hc, blk_one]

private theorem swGL_mem_statedSU (h : UnitaryFieldData p f K) :
    swGL K ∈ StatedSU 5 (p ^ f) K := by
  refine (mem_unitarySU_iff h).mpr ⟨show (sw : Matrix (Fin 5) (Fin 5) K).det = 1 from det_sw, ?_⟩
  show ((sw : Matrix (Fin 5) (Fin 5) K).map h.bar)ᵀ * sw = 1
  rw [sw_map, sw_transpose, sw_mul_self]

private theorem hker_statedSU (N : ℕ) (x : ↥(StatedSU 5 N K))
    (hx : QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 N K)) x = 1) :
    x ^ 5 = 1 := by
  have h1 : x ∈ (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 N K) :=
    (QuotientGroup.eq_one_iff x).mp hx
  have h2 : (x : GL (Fin 5) K) ∈ StatedScalars (Fin 5) K := h1
  have h3 := pow_five_eq_one_of_scalar h2 (det_of_mem_statedSU x.2)
  exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h3)

private theorem negOne_mem_GU2 (h : UnitaryFieldData p f K) : (-1 : GL (Fin 2) K) ∈ GU2 h := by
  rw [mem_GU2, Units.val_neg, Units.val_one, Matrix.map_neg _ (map_neg _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_neg, Matrix.transpose_one,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.one_mul]

private theorem rGL_mem_GU2 (h : UnitaryFieldData p f K) : (rGL : GL (Fin 2) K) ∈ GU2 h := by
  rw [mem_GU2]
  show ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * !![1, 0; 0, -1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end UnitaryMain

section UnitaryCard

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K]

private theorem toLin_mem_iff (h : UnitaryFieldData p f K) (g : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.toLin g ∈
        sesqUnitaryGroup (gramForm h (1 : Matrix (Fin 2) (Fin 2) K)) ↔ g ∈ GU2 h := by
  rw [mem_sesqUnitaryGroup]
  show _ ↔ ((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * 1 * (g : Matrix (Fin 2) (Fin 2) K) = 1
  rw [← gramForm_isometry_iff]
  simp only [Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply', Matrix.toLin'_apply]

private theorem card_GU2 (h : UnitaryFieldData p f K) :
    (Nat.card (GU2 h) : ℤ) = ((p ^ f : ℕ) : ℤ) *
      ((((p ^ f : ℕ) : ℤ) + 1) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1)) := by
  have hU := (unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin 2) (Fin 2) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun _) (by norm_num)).1
  have hcard : Nat.card (GU2 h) =
      Nat.card (sesqUnitaryGroup (gramForm h (1 : Matrix (Fin 2) (Fin 2) K))) :=
    Nat.card_congr (Matrix.GeneralLinearGroup.toLin.toEquiv.subtypeEquiv fun g =>
      (toLin_mem_iff h g).symm)
  rw [hcard, hU, Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]
  norm_num <;> ring

private theorem card_SU5 (h : UnitaryFieldData p f K) :
    (Nat.card (StatedSU 5 (p ^ f) K) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ 10 *
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) *
        (((p ^ f : ℕ) : ℤ) ^ 4 - 1) * (((p ^ f : ℕ) : ℤ) ^ 5 + 1) := by
  have hU := (unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin 5) (Fin 5) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun _) (by norm_num)).2.1
  have hcard : Nat.card (StatedSU 5 (p ^ f) K) =
      Nat.card (sesqSpecialUnitaryGroup (gramForm h (1 : Matrix (Fin 5) (Fin 5) K))) := by
    show Nat.card (unitarySU p f K 5) = _
    rw [unitarySU_eq_gramSU h, card_gramSU]
  rw [hcard, hU, Finset.prod_Icc_succ_top (by norm_num), Finset.prod_Icc_succ_top (by norm_num),
    Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]
  norm_num <;> ring

private theorem card_GU2_nat (h : UnitaryFieldData p f K) (e : ℕ) (hq : p ^ f = 2 * e + 1) :
    Nat.card (GU2 h) = 8 * e * (e + 1) ^ 2 * (2 * e + 1) := by
  have h1 := card_GU2 h
  have hq' : ((p ^ f : ℕ) : ℤ) = 2 * (e : ℤ) + 1 := by rw [hq]; push_cast; ring
  rw [hq'] at h1
  have h2 : (Nat.card (GU2 h) : ℤ) = ((8 * e * (e + 1) ^ 2 * (2 * e + 1) : ℕ) : ℤ) := by
    rw [h1]
    push_cast
    ring
  exact_mod_cast h2

private theorem card_SU5_nat (h : UnitaryFieldData p f K) (e : ℕ) (hq : p ^ f = 2 * e + 1) :
    Nat.card (StatedSU 5 (p ^ f) K) = (2 * e + 1) ^ 10 * (4 * e * (e + 1)) *
      (2 * (e + 1) * (4 * e ^ 2 + 2 * e + 1)) * (8 * e * (e + 1) * (2 * e ^ 2 + 2 * e + 1)) *
      (2 * (e + 1) * (16 * e ^ 4 + 24 * e ^ 3 + 16 * e ^ 2 + 4 * e + 1)) := by
  have h1 := card_SU5 h
  have hq' : ((p ^ f : ℕ) : ℤ) = 2 * (e : ℤ) + 1 := by rw [hq]; push_cast; ring
  rw [hq'] at h1
  have h2 : (Nat.card (StatedSU 5 (p ^ f) K) : ℤ) = (((2 * e + 1) ^ 10 * (4 * e * (e + 1)) *
      (2 * (e + 1) * (4 * e ^ 2 + 2 * e + 1)) * (8 * e * (e + 1) * (2 * e ^ 2 + 2 * e + 1)) *
      (2 * (e + 1) * (16 * e ^ 4 + 24 * e ^ 3 + 16 * e ^ 2 + 4 * e + 1)) : ℕ) : ℤ) := by
    rw [h1]
    push_cast
    ring
  exact_mod_cast h2

end UnitaryCard

section UnitaryNumber

private theorem exists_cofactor_unitary (e : ℕ) (he : 1 ≤ e) :
    ∃ m : ℕ, Odd m ∧
      (2 * e + 1) ^ 10 * (4 * e * (e + 1)) * (2 * (e + 1) * (4 * e ^ 2 + 2 * e + 1)) *
          (8 * e * (e + 1) * (2 * e ^ 2 + 2 * e + 1)) *
          (2 * (e + 1) * (16 * e ^ 4 + 24 * e ^ 3 + 16 * e ^ 2 + 4 * e + 1)) =
        2 ^ (2 * (8 * e * (e + 1) ^ 2 * (2 * e + 1)).factorization 2 + 1) * m := by
  obtain ⟨s, e', he', hes⟩ := Nat.exists_eq_two_pow_mul_odd (show e ≠ 0 by omega)
  obtain ⟨t, w', hw', hwt⟩ := Nat.exists_eq_two_pow_mul_odd (show e + 1 ≠ 0 by omega)
  have hGU : 8 * e * (e + 1) ^ 2 * (2 * e + 1) =
      2 ^ (3 + s + 2 * t) * (e' * w' ^ 2 * (2 * e + 1)) := by
    calc 8 * e * (e + 1) ^ 2 * (2 * e + 1)
        = 8 * (2 ^ s * e') * (2 ^ t * w') ^ 2 * (2 * e + 1) := by rw [← hes, ← hwt]
      _ = 2 ^ (3 + s + 2 * t) * (e' * w' ^ 2 * (2 * e + 1)) := by ring
  have hodd : Odd (e' * w' ^ 2 * (2 * e + 1)) := (he'.mul hw'.pow).mul ⟨e, rfl⟩
  rw [hGU, two_adic_factorization hodd]
  have o1 : Odd (2 * e + 1) := ⟨e, rfl⟩
  have o2 : Odd (4 * e ^ 2 + 2 * e + 1) := ⟨2 * e ^ 2 + e, by ring⟩
  have o3 : Odd (2 * e ^ 2 + 2 * e + 1) := ⟨e ^ 2 + e, by ring⟩
  have o4 : Odd (16 * e ^ 4 + 24 * e ^ 3 + 16 * e ^ 2 + 4 * e + 1) :=
    ⟨8 * e ^ 4 + 12 * e ^ 3 + 8 * e ^ 2 + 2 * e, by ring⟩
  refine ⟨e' ^ 2 * w' ^ 4 * ((2 * e + 1) ^ 10 * (4 * e ^ 2 + 2 * e + 1) * (2 * e ^ 2 + 2 * e + 1) *
    (16 * e ^ 4 + 24 * e ^ 3 + 16 * e ^ 2 + 4 * e + 1)), ?_, ?_⟩
  · exact (he'.pow.mul hw'.pow).mul (((o1.pow.mul o2).mul o3).mul o4)
  · calc (2 * e + 1) ^ 10 * (4 * e * (e + 1)) * (2 * (e + 1) * (4 * e ^ 2 + 2 * e + 1)) *
          (8 * e * (e + 1) * (2 * e ^ 2 + 2 * e + 1)) *
          (2 * (e + 1) * (16 * e ^ 4 + 24 * e ^ 3 + 16 * e ^ 2 + 4 * e + 1))
        = 2 ^ 7 * e ^ 2 * (e + 1) ^ 4 * ((2 * e + 1) ^ 10 * (4 * e ^ 2 + 2 * e + 1) *
          (2 * e ^ 2 + 2 * e + 1) * (16 * e ^ 4 + 24 * e ^ 3 + 16 * e ^ 2 + 4 * e + 1)) := by
          ring
      _ = 2 ^ 7 * (2 ^ s * e') ^ 2 * (2 ^ t * w') ^ 4 * ((2 * e + 1) ^ 10 *
          (4 * e ^ 2 + 2 * e + 1) * (2 * e ^ 2 + 2 * e + 1) *
          (16 * e ^ 4 + 24 * e ^ 3 + 16 * e ^ 2 + 4 * e + 1)) := by rw [← hes, ← hwt]
      _ = 2 ^ (2 * (3 + s + 2 * t) + 1) * (e' ^ 2 * w' ^ 4 * ((2 * e + 1) ^ 10 *
          (4 * e ^ 2 + 2 * e + 1) * (2 * e ^ 2 + 2 * e + 1) *
          (16 * e ^ 4 + 24 * e ^ 3 + 16 * e ^ 2 + 4 * e + 1))) := by ring

end UnitaryNumber

section UnitaryFinal

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K]

private theorem sylowFourJoined_statedProj_SU5 (h : UnitaryFieldData p f K)
    (hodd : Odd (p ^ f)) (h3 : 3 ≤ p ^ f) :
    SylowFourJoined (StatedProj (StatedSU 5 (p ^ f) K)) := by
  haveI : Finite K := h.finite
  obtain ⟨e, he⟩ := id hodd
  have he1 : 1 ≤ e := by omega
  have hoddK : Odd (Nat.card K) := by
    rw [h.card, pow_mul']
    exact Odd.pow hodd
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_card hoddK)
  obtain ⟨m, hm, hmeq⟩ := exists_cofactor_unitary e he1
  have hcard : Nat.card (StatedSU 5 (p ^ f) K) =
      2 ^ (2 * (Nat.card (GU2 h)).factorization 2 + 1) * m := by
    rw [card_GU2_nat h e he, card_SU5_nat h e he]
    exact hmeq
  let zU : GU2 h := ⟨-1, negOne_mem_GU2 h⟩
  let rU : GU2 h := ⟨rGL, rGL_mem_GU2 h⟩
  have hz2 : zU * zU = 1 := Subtype.ext (by show (-1 : GL (Fin 2) K) * -1 = 1; simp)
  have hz1 : zU ≠ 1 := fun hh => negOne_ne_one h2 (congrArg Subtype.val hh)
  have hr2 : rU * rU = 1 := Subtype.ext rGL_mul_self
  have hr1 : rU ≠ 1 := fun hh => rGL_ne_one h2 (congrArg Subtype.val hh)
  have hzr : zU ≠ rU := fun hh => rGL_ne_neg_one h2 (congrArg Subtype.val hh).symm
  have hzrc : Commute zU rU := Subtype.ext (Commute.neg_one_left (rGL : GL (Fin 2) K)).eq
  obtain ⟨D, hzD, hrD, hD⟩ := exists_sylow_two_containing hz2 hr2 hz1 hr1 hzr hzrc
  exact sylowFourJoined_of_wreath_embedding (StatedSU 5 (p ^ f) K) (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (m₀ := 5) ⟨2, by norm_num⟩ (hker_statedSU (p ^ f))
    (embU h) (embU_injective h) (embU_mem h) (swGL_mem_statedSU h) (swGL_mul_self K)
    (fun g g' => swGL_mul_embGL K ((g : GL (Fin 2) K), (g' : GL (Fin 2) K)))
    (fun g g' => embGL_ne_swGL K ((g : GL (Fin 2) K), (g' : GL (Fin 2) K))) D hD hm hcard hzD hrD
    hz2 hz1 hr2 hr1 hzr.symm
    (fun d _ => Subtype.ext (Commute.neg_one_right (d : GL (Fin 2) K)).eq)

end UnitaryFinal

theorem leafL5_holds : LeafL5 := by
  intro X _ _ _ _ p f hp hf hq hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel_of_ne_zero (by norm_num)
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact Nat.odd_iff.mpr (by omega)
  have h3 : 3 ≤ Nat.card K := by
    rw [hK]
    omega
  exact SylowFourJoined.of_mulEquiv e.symm (sylowFourJoined_statedProj_SL5 hodd h3)

theorem leafU5_holds : LeafU5 := by
  intro X _ _ _ _ p f hp hf hq hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel_of_ne_zero (by norm_num)
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hpf : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have hodd : Odd (p ^ f) := Nat.odd_iff.mpr (by omega)
  have h3 : 3 ≤ p ^ f := by omega
  exact SylowFourJoined.of_mulEquiv e.symm (sylowFourJoined_statedProj_SU5 h hodd h3)

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
