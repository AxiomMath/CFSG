module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Par

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG Matrix
open scoped MatrixGroups

section Conj

variable {F : Type} [Field F]

@[expose] def conjSL (g : GL (Fin 2) F) : SL(2, F) →* SL(2, F) where
  toFun A := ⟨(g : Matrix (Fin 2) (Fin 2) F) * A *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
    by
      rw [det_mul, det_mul, A.2, mul_one, ← det_mul]
      simp⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' A B := by
    apply Subtype.ext
    have h : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) =
        1 := by simp
    show (g : Matrix (Fin 2) (Fin 2) F) * ((A * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g : Matrix (Fin 2) (Fin 2) F) * A * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        ((g : Matrix (Fin 2) (Fin 2) F) * B * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    rw [Matrix.SpecialLinearGroup.coe_mul]
    calc (g : Matrix (Fin 2) (Fin 2) F) * ((A : Matrix (Fin 2) (Fin 2) F) * B) *
          ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (g : Matrix (Fin 2) (Fin 2) F) * A *
          (((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) *
          B * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          rw [h, mul_one]
          simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]

theorem coe_conjSL (g : GL (Fin 2) F) (A : SL(2, F)) :
    ((conjSL g A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * A * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem conjSL_conjSL (g h : GL (Fin 2) F) (A : SL(2, F)) :
    conjSL g (conjSL h A) = conjSL (g * h) A := by
  apply Subtype.ext
  simp only [coe_conjSL, _root_.mul_inv_rev, Units.val_mul]
  simp only [mul_assoc]

theorem conjSL_one (A : SL(2, F)) : conjSL 1 A = A := by
  apply Subtype.ext
  simp [coe_conjSL]

theorem conjSL_inv_conjSL (g : GL (Fin 2) F) (A : SL(2, F)) : conjSL g⁻¹ (conjSL g A) = A := by
  rw [conjSL_conjSL, inv_mul_cancel, conjSL_one]

theorem conjSL_conjSL_inv (g : GL (Fin 2) F) (A : SL(2, F)) : conjSL g (conjSL g⁻¹ A) = A := by
  rw [conjSL_conjSL, mul_inv_cancel, conjSL_one]

end Conj

section Elementary

variable {R : Type*} [CommRing R]

@[expose] def slU : SL(2, R) := ⟨!![1, 1; 0, 1], by simp [det_fin_two_of]⟩

@[expose] def slL : SL(2, R) := ⟨!![1, 0; 1, 1], by simp [det_fin_two_of]⟩

end Elementary

section NormalForm

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem sl2_sub_one_sq_eq_zero (X : SL(2, F)) (hXp : X ^ p = 1) :
    ((X : Matrix (Fin 2) (Fin 2) F) - 1) * ((X : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
  set M : Matrix (Fin 2) (Fin 2) F := (X : Matrix (Fin 2) (Fin 2) F) with hM
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← det_fin_two]
    exact X.2
  have hNN : (M - 1) * (M - 1) = (M.trace - 2) • M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.one_apply] <;>
      first | ring1 | linear_combination (-1 : F) * hd
  have hNp : (M - 1) ^ p = 0 := by
    have h1 : (M - 1) ^ p = M ^ p - 1 ^ p := sub_pow_char_of_commute p (Commute.one_right M)
    have h2 : M ^ p = 1 := by
      have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hXp
      simpa [Matrix.SpecialLinearGroup.coe_pow] using this
    rw [h1, h2, one_pow, sub_self]
  have hdet0 : (M - 1).det = 0 := by
    have : (M - 1).det ^ p = 0 := by
      rw [← det_pow, hNp, det_zero]
    exact pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp this
  have hc : M.trace - 2 = 0 := by
    have h1 : ((M - 1) * (M - 1)).det = 0 := by rw [det_mul, hdet0, zero_mul]
    rw [hNN, det_smul] at h1
    have h2 : M.det = 1 := X.2
    rw [h2, mul_one] at h1
    simpa using h1
  rw [hNN, hc, zero_smul]

theorem exists_conj_upper (X : SL(2, F)) (hX1 : X ≠ 1) (hXp : X ^ p = 1) :
    ∃ g : GL (Fin 2) F, conjSL g X = slU := by
  set M : Matrix (Fin 2) (Fin 2) F := (X : Matrix (Fin 2) (Fin 2) F) with hM
  set N : Matrix (Fin 2) (Fin 2) F := M - 1 with hN
  have hNN : N * N = 0 := sl2_sub_one_sq_eq_zero X hXp
  have hN0 : N ≠ 0 := by
    intro h
    apply hX1
    apply Subtype.ext
    rw [hN, sub_eq_zero] at h
    simpa using h
  obtain ⟨v, hv⟩ : ∃ v : Fin 2 → F, N *ᵥ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hN0
    ext i j
    have := congrFun (hcon (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  set w : Fin 2 → F := N *ᵥ v with hw
  have hww : N *ᵥ w = 0 := by rw [hw, Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  have hMw : M *ᵥ w = w := by
    have : M = N + 1 := by rw [hN]; abel
    rw [this, Matrix.add_mulVec, hww, Matrix.one_mulVec, zero_add]
  have hMv : M *ᵥ v = w + v := by
    have : M = N + 1 := by rw [hN]; abel
    rw [this, Matrix.add_mulVec, Matrix.one_mulVec]
  set P : Matrix (Fin 2) (Fin 2) F := !![w 0, v 0; w 1, v 1] with hP
  have hPa : ∀ a : Fin 2 → F, P *ᵥ a = a 0 • w + a 1 • v := by
    intro a
    ext i
    fin_cases i <;> simp [hP, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
    ring
  have hPinj : Function.Injective P.mulVec := by
    rw [← Matrix.coe_mulVecLin, injective_iff_map_eq_zero]
    intro a ha
    have h1 : N *ᵥ (P *ᵥ a) = a 1 • w := by
      rw [hPa, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hww, ← hw]
      simp
    have ha' : P *ᵥ a = 0 := ha
    rw [ha', Matrix.mulVec_zero] at h1
    have hw0 : w ≠ 0 := hv
    have ha1 : a 1 = 0 := by
      rcases smul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hw0
    have ha0 : a 0 = 0 := by
      rw [hPa, ha1, zero_smul, add_zero] at ha'
      rcases smul_eq_zero.mp ha' with h | h
      · exact h
      · exact absurd h hw0
    ext i
    fin_cases i
    · exact ha0
    · exact ha1
  have hPunit : IsUnit P := Matrix.mulVec_injective_iff_isUnit.mp hPinj
  set gP : GL (Fin 2) F := hPunit.unit with hgP
  have hgPval : (gP : Matrix (Fin 2) (Fin 2) F) = P := rfl
  have hw0 : M 0 0 * w 0 + M 0 1 * w 1 = w 0 := by
    have := congrFun hMw 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hw1 : M 1 0 * w 0 + M 1 1 * w 1 = w 1 := by
    have := congrFun hMw 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hv0 : M 0 0 * v 0 + M 0 1 * v 1 = w 0 + v 0 := by
    have := congrFun hMv 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hv1 : M 1 0 * v 0 + M 1 1 * v 1 = w 1 + v 1 := by
    have := congrFun hMv 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hMP : M * P = P * !![1, 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hw0 | linear_combination hw1 | linear_combination hv0 |
        linear_combination hv1
  refine ⟨gP⁻¹, Subtype.ext ?_⟩
  rw [coe_conjSL, inv_inv, hgPval]
  have hinv : ((gP⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * P = 1 := by
    rw [← hgPval]
    exact Units.inv_mul gP
  calc ((gP⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * M * P
      = ((gP⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (M * P) := by rw [mul_assoc]
    _ = ((gP⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (P * !![1, 1; 0, 1]) := by rw [hMP]
    _ = (((gP⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * P) * !![1, 1; 0, 1] := by
        rw [mul_assoc]
    _ = !![1, 1; 0, 1] := by rw [hinv, one_mul]

end NormalForm

section Generic

variable {R : Type*} [CommRing R]

@[expose] def slV : SL(2, R) := ⟨!![0, 1; -1, 2], by simp [det_fin_two_of]⟩

theorem slL_mul_slU : (slL * slU : SL(2, R)) = slV * slL := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slL, slU, slV, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem slV_eq : (slV : SL(2, R)) = slL * slU * slL⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, slL_mul_slU]

theorem slV_coe : ((slV : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![0, 1; -1, 2] := rfl

theorem slU_mul_slV_cube :
    (((slU * slV : SL(2, R)) ^ 3 : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = -1 := by
  have h1 : ((slU * slV : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = !![-1, 3; -1, 2] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, slV_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slU, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  rw [pow_succ, pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end Generic

section Proper

theorem false_of_pow_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type*} [Group G] {w : G}
    (h6 : w ^ 6 = 1) (h3 : w ^ 3 ≠ 1) {k : ℕ} (hk : w ^ p ^ k = 1) : False := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk)
  have h6' : orderOf w ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  rcases Nat.eq_zero_or_pos j with h0 | hj0
  · apply h3
    rw [h0, pow_zero, orderOf_eq_one_iff] at hj
    rw [hj, one_pow]
  · have hpd : p ∣ 6 := (dvd_pow_self p hj0.ne').trans (hj ▸ h6')
    have hp3 : p = 3 := by
      have : p ∣ 2 * 3 := hpd
      rcases (Nat.Prime.dvd_mul hp).mp this with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    subst hp3
    have hj1 : j = 1 := by
      by_contra hne
      have h9 : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 (by omega : 2 ≤ j)
      have : 9 ∣ 6 := h9.trans (hj ▸ h6')
      omega
    apply h3
    rw [hj1, pow_one] at hj
    rw [← hj]
    exact pow_orderOf_eq_one w

theorem slW_pow_six {R : Type*} [CommRing R] : (slU * slV : SL(2, R)) ^ 6 = 1 := by
  apply Subtype.ext
  have : (slU * slV : SL(2, R)) ^ 6 = ((slU * slV : SL(2, R)) ^ 3) ^ 2 := by rw [← pow_mul]
  rw [this, Matrix.SpecialLinearGroup.coe_pow, slU_mul_slV_cube]
  simp

theorem slW_pow_three_ne_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) :
    (slU * slV : SL(2, F)) ^ 3 ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h
  simp only [slU_mul_slV_cube, Matrix.SpecialLinearGroup.coe_one] at h1
  have h3 := congrFun (congrFun h1 0) 0
  simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h3
  exact h2 (by linear_combination -h3)

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

@[expose] def slPrime (F : Type) [Field F] : Subgroup (SL(2, F)) where
  carrier := {A | ∀ i j, (A : Matrix (Fin 2) (Fin 2) F) i j ∈ (Int.castRingHom F).range}
  one_mem' := fun i j => by
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  mul_mem' := fun {A B} hA hB i j => by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)
  inv_mem' := fun {A} hA i j => by
    simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply] <;>
      first | exact Subring.neg_mem _ (hA _ _) | exact hA _ _

omit [Finite F] in
theorem slU_mem_slPrime : (slU : SL(2, F)) ∈ slPrime F := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [slU]

omit [Finite F] in
theorem slV_mem_slPrime : (slV : SL(2, F)) ∈ slPrime F := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [slV]

omit [Finite F] in
theorem exists_not_mem_slPrime {n : ℕ} (hF : Nat.card F = p ^ n) (hn : 2 ≤ n) :
    ∃ A : SL(2, F), A ∉ slPrime F := by
  have hc : ∃ c : F, c ∉ (Int.castRingHom F).range := by
    by_contra h
    push Not at h
    have hsurj : Function.Surjective (ZMod.castHom (dvd_refl p) F) := by
      intro c
      obtain ⟨k, hk⟩ := h c
      exact ⟨(k : ZMod p), by simpa using hk⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [hF, Nat.card_zmod] at h1
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
    nlinarith
  obtain ⟨c, hc⟩ := hc
  refine ⟨⟨!![1, c; 0, 1], by simp [det_fin_two_of]⟩, fun h => hc ?_⟩
  simpa using h 0 1

omit [Finite F] in
theorem exists_proper_pair_sl2_generic {n : ℕ} (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hn : 2 ≤ n) {G : Type} [Group G] (e : G ≃* SL(2, F)) {x : G} (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) :
    ∃ z : G, closure ({x, z * x * z⁻¹} : Set G) ≠ ⊤ ∧
      ¬ IsPGroup p ↥(closure ({x, z * x * z⁻¹} : Set G)) := by
  classical
  obtain ⟨g₀, hg₀⟩ := exists_conj_upper (p := p) (e x)
    (fun h => hx1 (e.injective (by simpa using h))) (by rw [← map_pow, hxp, map_one])
  have hX : e x = conjSL g₀⁻¹ slU := by rw [← hg₀, conjSL_inv_conjSL]
  refine ⟨e.symm (conjSL g₀⁻¹ slL), ?_, ?_⟩
  all_goals
    have hY : e (e.symm (conjSL g₀⁻¹ slL) * x * (e.symm (conjSL g₀⁻¹ slL))⁻¹) =
        conjSL g₀⁻¹ slV := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hX, slV_eq, map_mul, map_mul,
        map_inv]
  · set y := e.symm (conjSL g₀⁻¹ slL) * x * (e.symm (conjSL g₀⁻¹ slL))⁻¹ with hy
    intro htop
    have h1 : closure ({conjSL g₀⁻¹ slU, conjSL g₀⁻¹ slV} : Set SL(2, F)) = ⊤ := by
      have := congrArg (Subgroup.map e.toMonoidHom) htop
      rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top_of_surjective _ e.surjective]
        at this
      simpa [hX, hY] using this
    have h2 : closure ({slU, slV} : Set SL(2, F)) = ⊤ := by
      have := congrArg (Subgroup.map (conjSL g₀)) h1
      rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top_of_surjective]
        at this
      · simpa [conjSL_conjSL_inv] using this
      · exact fun A => ⟨conjSL g₀⁻¹ A, conjSL_conjSL_inv g₀ A⟩
    obtain ⟨A, hA⟩ := exists_not_mem_slPrime (p := p) hF hn
    apply hA
    have : closure ({slU, slV} : Set SL(2, F)) ≤ slPrime F := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact slU_mem_slPrime
      · exact slV_mem_slPrime
    rw [h2] at this
    exact this (Subgroup.mem_top A)
  · set y := e.symm (conjSL g₀⁻¹ slL) * x * (e.symm (conjSL g₀⁻¹ slL))⁻¹ with hy
    intro hP
    have hxy : e (x * y) = conjSL g₀⁻¹ (slU * slV) := by
      rw [map_mul, hX, hY, map_mul]
    have h2F : (2 : F) ≠ 0 := by
      intro h
      have := (CharP.cast_eq_zero_iff F p 2).mp (by simpa using h)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)
    have hne : (slU * slV : SL(2, F)) ^ 3 ≠ 1 := slW_pow_three_ne_one h2F
    have h6 : (slU * slV : SL(2, F)) ^ 6 = 1 := slW_pow_six
    have hw6 : (x * y) ^ 6 = 1 := by
      apply e.injective
      rw [map_pow, hxy, ← map_pow, h6, map_one, map_one]
    have hw3 : (x * y) ^ 3 ≠ 1 := by
      intro h
      apply hne
      have := congrArg e h
      rw [map_pow, hxy, ← map_pow, map_one] at this
      have h4 := congrArg (conjSL g₀) this
      rwa [conjSL_conjSL_inv, map_one] at h4
    have hmem : x * y ∈ closure ({x, y} : Set G) :=
      Subgroup.mul_mem _ (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    obtain ⟨k, hk⟩ := hP ⟨x * y, hmem⟩
    have hk' : (x * y) ^ p ^ k = 1 := congrArg Subtype.val hk
    exact false_of_pow_six (Fact.out : p.Prime) hp2 hw6 hw3 hk'

end Proper

section Exceptional

abbrev SL5 : Type := SL(2, ZMod 5)

@[expose] def q8 : Finset (Matrix (Fin 2) (Fin 2) (ZMod 5)) :=
  {!![1, 0; 0, 1], !![4, 0; 0, 4], !![2, 0; 0, 3], !![3, 0; 0, 2], !![0, 1; 4, 0], !![0, 4; 1, 0],
    !![0, 2; 2, 0], !![0, 3; 3, 0]}

@[expose] def conjMat (g : SL5) (q : Matrix (Fin 2) (Fin 2) (ZMod 5)) :
    Matrix (Fin 2) (Fin 2) (ZMod 5) :=
  (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) * q * ((g⁻¹ : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5))

@[expose] def normQ (g : SL5) : Prop := q8.image (conjMat g) = q8

instance (g : SL5) : Decidable (normQ g) := inferInstanceAs (Decidable (_ = _))

theorem conjMat_mul (g h : SL5) : conjMat (g * h) = conjMat g ∘ conjMat h := by
  funext q
  simp only [conjMat, Function.comp, Matrix.SpecialLinearGroup.coe_mul, _root_.mul_inv_rev]
  simp only [mul_assoc]

theorem conjMat_one : conjMat (1 : SL5) = id := by
  funext q
  simp [conjMat]

theorem normQ_one : normQ (1 : SL5) := by
  simp [normQ, conjMat_one]

theorem normQ_mul {g h : SL5} (hg : normQ g) (hh : normQ h) : normQ (g * h) := by
  unfold normQ at *
  rw [conjMat_mul, ← Finset.image_image, hh, hg]

theorem normQ_inv {g : SL5} (hg : normQ g) : normQ g⁻¹ := by
  unfold normQ at *
  have h1 : q8.image (conjMat g⁻¹) = (q8.image (conjMat g)).image (conjMat g⁻¹) := by rw [hg]
  rw [h1, Finset.image_image, ← conjMat_mul, inv_mul_cancel, conjMat_one, Finset.image_id]

@[expose] def nQ8 : Subgroup SL5 where
  carrier := {g | normQ g}
  one_mem' := normQ_one
  mul_mem' := normQ_mul
  inv_mem' := normQ_inv

theorem sl5_notall : ∃ g : SL5, ¬ normQ g := by decide +kernel

theorem sl5_main : ∀ X : SL5, X ^ 3 = 1 → X ≠ 1 → ∃ w Z : SL5, normQ (w⁻¹ * X * w) ∧
    normQ (w⁻¹ * Z * w) ∧ Z * X * Z⁻¹ ≠ X ∧ Z * X * Z⁻¹ ≠ X ^ 2 ∧
    ((X * (Z * X * Z⁻¹)) ^ 3 ≠ 1 ∨ (X * (Z * X * Z⁻¹)⁻¹) ^ 3 ≠ 1) := by decide +kernel

theorem sl5_card : Fintype.card SL5 = 120 := by decide +kernel

theorem sl5_not_three_power {A : SL5} (h : A ^ 3 ≠ 1) {k : ℕ} (hk : A ^ 3 ^ k = 1) : False := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have h120 : orderOf A ∣ 120 := by
    rw [← sl5_card]
    exact orderOf_dvd_card
  have hj1 : j ≤ 1 := by
    by_contra hne
    have h9 : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 (by omega : 2 ≤ j)
    have : 9 ∣ 120 := h9.trans (hj ▸ h120)
    omega
  apply h
  have : orderOf A ∣ 3 := by
    rw [hj]
    calc 3 ^ j ∣ 3 ^ 1 := pow_dvd_pow 3 hj1
      _ = 3 := pow_one 3
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem exists_proper_pair_sl5 {G : Type} [Group G] (e : G ≃* SL5) {x : G} (hx1 : x ≠ 1)
    (hx3 : x ^ 3 = 1) :
    ∃ z : G, closure ({x, z * x * z⁻¹} : Set G) ≠ ⊤ ∧
      ¬ IsPGroup 3 ↥(closure ({x, z * x * z⁻¹} : Set G)) := by
  obtain ⟨w, Z, hXw, hZw, hZX1, hZX2, hW⟩ := sl5_main (e x) (by rw [← map_pow, hx3, map_one])
    (fun h => hx1 (e.injective (by simpa using h)))
  obtain ⟨g, hg⟩ := sl5_notall
  refine ⟨e.symm Z, ?_, ?_⟩
  all_goals
    have hey : e (e.symm Z * x * (e.symm Z)⁻¹) = Z * e x * Z⁻¹ := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · set y := e.symm Z * x * (e.symm Z)⁻¹ with hy
    let T : Subgroup SL5 := nQ8.comap (MulAut.conj w⁻¹).toMonoidHom
    have hmemT : ∀ A : SL5, A ∈ T ↔ normQ (w⁻¹ * A * w) := fun A => by
      simp [T, nQ8]
    have hT : T ≠ ⊤ := by
      intro h
      apply hg
      have := (hmemT (w * g * w⁻¹)).mp (h ▸ Subgroup.mem_top _)
      simpa [mul_assoc] using this
    intro htop
    have h1 : Subgroup.closure ({e x, e y} : Set SL5) = ⊤ := by
      have := congrArg (Subgroup.map e.toMonoidHom) htop
      rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top_of_surjective _ e.surjective]
        at this
      exact this
    have h2 : Subgroup.closure ({e x, e y} : Set SL5) ≤ T := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact (hmemT _).mpr hXw
      · rw [hey]
        exact T.mul_mem (T.mul_mem ((hmemT _).mpr hZw) ((hmemT _).mpr hXw))
          (T.inv_mem ((hmemT _).mpr hZw))
    rw [h1] at h2
    exact hT (top_le_iff.mp h2)
  · set y := e.symm Z * x * (e.symm Z)⁻¹ with hy
    intro hP
    have hxy : ∀ u : G, u ∈ closure ({x, y} : Set G) → (e u) ^ 3 ≠ 1 → False := by
      intro u hu h3
      obtain ⟨k, hk⟩ := hP ⟨u, hu⟩
      have hk' : u ^ 3 ^ k = 1 := congrArg Subtype.val hk
      exact sl5_not_three_power h3 (by rw [← map_pow, hk', map_one])
    have hxm : x ∈ closure ({x, y} : Set G) := subset_closure (Set.mem_insert _ _)
    have hym : y ∈ closure ({x, y} : Set G) :=
      subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rcases hW with h | h
    · exact hxy (x * y) (Subgroup.mul_mem _ hxm hym) (by rw [map_mul, hey]; exact h)
    · exact hxy (x * y⁻¹) (Subgroup.mul_mem _ hxm (Subgroup.inv_mem _ hym))
        (by rw [map_mul, map_inv, hey]; exact h)

end Exceptional

section Combined

@[expose] def slEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S] (f : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map f.toRingHom)
    (Matrix.SpecialLinearGroup.map f.symm.toRingHom)
    (MonoidHom.ext fun A => Subtype.ext (Matrix.ext fun i j => by
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]))
    (MonoidHom.ext fun A => Subtype.ext (Matrix.ext fun i j => by
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]))

theorem exists_proper_pair_sl2 {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : (∃ n : ℕ, 2 ≤ n ∧ Nat.card F = p ^ n) ∨ (p = 3 ∧ Nat.card F = 5))
    {G : Type} [Group G] (e : G ≃* SL(2, F)) {x : G} (hx1 : x ≠ 1) (hxp : x ^ p = 1) :
    ∃ z : G, Subgroup.closure ({x, z * x * z⁻¹} : Set G) ≠ ⊤ ∧
      ¬ IsPGroup p ↥(Subgroup.closure ({x, z * x * z⁻¹} : Set G)) := by
  rcases hF with ⟨n, hn, hF⟩ | ⟨rfl, hF⟩
  · have : Fact p.Prime := ⟨hp⟩
    have : CharP F p := charP_of_card_eq_pow hp (by omega) hF
    exact exists_proper_pair_sl2_generic hp2 hF hn e hx1 hxp
  · have : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = Fintype.card (ZMod 5) := by
      rw [← Nat.card_eq_fintype_card, hF, ZMod.card]
    let f : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq hc
    exact exists_proper_pair_sl5 (e.trans (slEquivOfRingEquiv f)) hx1 hxp

end Combined

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
