module

public import CFSG.ClassicalInvolution.RouteD.SCRSp4Norm

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSp4

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Steinberg.Sp TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

variable {F : Type} [Field F]

section Levi

variable (a b e : F)

@[expose] def Smat : Matrix (Fin 2) (Fin 2) F := !![a, b; -(b * e), a]

@[expose] def Tmat : Matrix (Fin 2) (Fin 2) F := !![a, b * e; -b, a]

theorem Smat_T_mul (hab : a * a + e * (b * b) = 1) : (Smat a b e)ᵀ * Tmat a b e = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Smat, Tmat, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination hab

theorem Tmat_S_mul (hab : a * a + e * (b * b) = 1) : (Tmat a b e)ᵀ * Smat a b e = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Smat, Tmat, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination hab

theorem levi_symplectic (hab : a * a + e * (b * b) = 1) :
    (fromBlocks (Smat a b e) 0 0 (Tmat a b e))ᵀ * gram F 2 *
      fromBlocks (Smat a b e) 0 0 (Tmat a b e) = gram F 2 := by
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Smat_T_mul a b e hab, Tmat_S_mul a b e hab]


variable {a b e}

@[expose] noncomputable def gLevi (hab : a * a + e * (b * b) = 1) : StatedSp 2 F :=
  ofSymplecticMat (fromBlocks (Smat a b e) 0 0 (Tmat a b e)) (levi_symplectic a b e hab)

theorem mat_gLevi (hab : a * a + e * (b * b) = 1) :
    mat 2 F (gLevi hab) = fromBlocks (Smat a b e) 0 0 (Tmat a b e) :=
  mat_ofSymplecticMat _ _

theorem mat_ut_Ad (d d' : F) (hd : d ≠ 0) (hd' : d' ≠ 0) :
    mat 2 F (ut (Ad d hd) (Ad d' hd')) =
      fromBlocks 0 (-Matrix.diagonal ![d, d']) (Matrix.diagonal ![d⁻¹, d'⁻¹]) 0 := by
  rw [mat_ut, coe_Ad, coe_Ad]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp

theorem gLevi_comm_ut (hab : a * a + e * (b * b) = 1) (d d' : F) (hd : d ≠ 0) (hd' : d' ≠ 0)
    (hde : d' = d * e) :
    gLevi hab * ut (Ad d hd) (Ad d' hd') = ut (Ad d hd) (Ad d' hd') * gLevi hab := by
  apply mat_injective
  rw [map_mul, map_mul, mat_gLevi, mat_ut_Ad, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  have he : e ≠ 0 := by
    rintro rfl
    exact hd' (by simpa using hde)
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Smat, Tmat, Matrix.mul_apply, Fin.sum_univ_two, hde,
      Matrix.vecMul_diagonal]
    all_goals ring1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Smat, Tmat, Matrix.mul_apply, Fin.sum_univ_two, hde,
      Matrix.vecMul_diagonal]
    all_goals first | ring1 | field_simp
  · simp


theorem gLevi_mul_elt (hab : a * a + e * (b * b) = 1) (t : F) :
    gLevi hab * elt (.positiveLong 0) t =
      (elt (.positiveLong 0) (a * a * t) * elt (.positiveLong 1) (b * b * (e * e) * t) *
        elt (.positiveSum 0 1 (by decide)) (-(a * b * e * t))) * gLevi hab := by
  apply mat_injective
  simp only [map_mul, mat_gLevi, mat_posLong, mat_posSum, upperM, Matrix.fromBlocks_multiply]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Smat, Tmat, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.single_apply, Matrix.vecMul, dotProduct]
    all_goals first
      | ring1
      | linear_combination (-(a * t)) * hab
      | linear_combination (b * e * t) * hab
  · simp
  · simp

end Levi


noncomputable abbrev wl (F : Type) [Field F] (k : Fin 2) : StatedSp 2 F := longBlock F 2 k (Wl F)

theorem wl1_mul_posSum (c : F) :
    wl F 1 * elt (.positiveSum 0 1 (by decide)) c =
      elt (.difference 0 1 (by decide)) (-c) * wl F 1 := by
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, mat_elt, mat_longBlock]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [E, blockMat, coe_Wl, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, mul_add]

theorem wl0_mul_posSum (c : F) :
    wl F 0 * elt (.positiveSum 0 1 (by decide)) c =
      elt (.difference 1 0 (by decide)) (-c) * wl F 0 := by
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, mat_elt, mat_longBlock]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [E, blockMat, coe_Wl, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, mul_add]

theorem wl0_mul_diff (c : F) :
    wl F 0 * elt (.difference 0 1 (by decide)) c =
      elt (.negativeSum 0 1 (by decide)) c * wl F 0 := by
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, mat_elt, mat_longBlock]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [E, blockMat, coe_Wl, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, mul_add]


theorem exists_ab [Finite F] (h2 : (2 : F) ≠ 0) (e : F) (hcard : 6 ≤ Nat.card F) :
    ∃ a b : F, a * a + e * (b * b) = 1 ∧ a ≠ 0 ∧ b ≠ 0 := by
  have hP0 : (Polynomial.X - Polynomial.C (e ^ 2) * Polynomial.X ^ 5 : Polynomial F) ≠ 0 := by
    intro h
    have := congrArg (fun p : Polynomial F => p.coeff 1) h
    rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C_mul_X_pow] at this
    simp at this
  have hdeg : (Polynomial.X - Polynomial.C (e ^ 2) * Polynomial.X ^ 5 : Polynomial F).natDegree ≤
      5 := by
    compute_degree
  have hlt : (Polynomial.X - Polynomial.C (e ^ 2) * Polynomial.X ^ 5 : Polynomial F).natDegree <
      Cardinal.mk F := by
    have := Fintype.ofFinite F
    rw [Cardinal.mk_fintype]
    have h6 : 6 ≤ Fintype.card F := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    exact_mod_cast lt_of_le_of_lt hdeg (by omega)
  obtain ⟨s, hs⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _ hP0 hlt
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow] at hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hf : (1 + e * s ^ 2) * (1 - e * s ^ 2) ≠ 0 := by
    intro h
    apply hs
    have : s * ((1 + e * s ^ 2) * (1 - e * s ^ 2)) = 0 := by rw [h, mul_zero]
    linear_combination this
  have h1 : 1 + e * s ^ 2 ≠ 0 := left_ne_zero_of_mul hf
  have h3 : 1 - e * s ^ 2 ≠ 0 := right_ne_zero_of_mul hf
  refine ⟨(1 - e * s ^ 2) / (1 + e * s ^ 2), 2 * s / (1 + e * s ^ 2), ?_, ?_, ?_⟩
  · field_simp
    ring
  · exact div_ne_zero h3 h1
  · exact div_ne_zero (mul_ne_zero h2 hs0) h1


theorem levi_sup_eq_top [Finite F] (h2 : (2 : F) ≠ 0) (hcard : 6 ≤ Nat.card F) (d d' : F)
    (hd : d ≠ 0) (hd' : d' ≠ 0) :
    Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({ut (Ad d hd) (Ad d' hd')} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({x0 F * ut (Ad d hd) (Ad d' hd')} : Set (StatedSp 2 F)) = ⊤ := by
  set e : F := d' / d with he
  have hde : d' = d * e := by rw [he]; field_simp
  obtain ⟨a, b, hab, ha, hb⟩ := exists_ab h2 e hcard
  set H := Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({ut (Ad d hd) (Ad d' hd')} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({x0 F * ut (Ad d hd) (Ad d' hd')} : Set (StatedSp 2 F)) with hH
  have hM : ∀ m : SL(2, F) × SL(2, F), phi4 F m ∈ H := fun m =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (phi4_mem_centralizer_x0 m))
  have hg : gLevi hab ∈ H := by
    refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact gLevi_comm_ut hab d d' hd hd' hde
  have hpl0 : ∀ c, elt (.positiveLong 0) c ∈ H := fun c => by
    have := hM (sl2Upper c, 1)
    rwa [phi4_apply, map_one, mul_one, longBlock_sl2Upper] at this
  have hpl1 : ∀ c, elt (.positiveLong 1) c ∈ H := fun c => by
    have := hM (1, sl2Upper c)
    rwa [phi4_apply, map_one, one_mul, longBlock_sl2Upper] at this
  have hnl0 : ∀ c, elt (.negativeLong 0) c ∈ H := fun c => by
    have := hM (sl2Lower c, 1)
    rwa [phi4_apply, map_one, mul_one, longBlock_sl2Lower] at this
  have hnl1 : ∀ c, elt (.negativeLong 1) c ∈ H := fun c => by
    have := hM (1, sl2Lower c)
    rwa [phi4_apply, map_one, one_mul, longBlock_sl2Lower] at this
  have he0 : e ≠ 0 := by
    rintro h0
    rw [h0] at hde
    exact hd' (by simpa using hde)
  have hsum : ∀ c, elt (.positiveSum 0 1 (by decide)) c ∈ H := by
    intro c
    have hae : a * b * e ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) he0
    set t : F := -c / (a * b * e) with ht
    have hct : -(a * b * e * t) = c := by rw [ht]; field_simp
    have key := gLevi_mul_elt hab t
    rw [hct] at key
    have hY : elt (.positiveLong 0) (a * a * t) * elt (.positiveLong 1) (b * b * (e * e) * t) *
        elt (.positiveSum 0 1 (by decide)) c = gLevi hab * elt (.positiveLong 0) t *
          (gLevi hab)⁻¹ := by
      rw [key, mul_inv_cancel_right]
    have hQ := eq_inv_mul_of_mul_eq hY
    rw [hQ]
    exact H.mul_mem (H.inv_mem (H.mul_mem (hpl0 _) (hpl1 _)))
      (H.mul_mem (H.mul_mem hg (hpl0 t)) (H.inv_mem hg))
  have hw0 : wl F 0 ∈ H := by
    have := hM (Wl F, 1)
    rwa [phi4_apply, map_one, mul_one] at this
  have hw1 : wl F 1 ∈ H := by
    have := hM (1, Wl F)
    rwa [phi4_apply, map_one, one_mul] at this
  have hd01 : ∀ c, elt (.difference 0 1 (by decide)) c ∈ H := by
    intro c
    have key := wl1_mul_posSum (F := F) (-c)
    rw [neg_neg] at key
    have : elt (.difference 0 1 (by decide)) c = wl F 1 * elt (.positiveSum 0 1 (by decide)) (-c) *
        (wl F 1)⁻¹ := by
      rw [key, mul_inv_cancel_right]
    rw [this]
    exact H.mul_mem (H.mul_mem hw1 (hsum _)) (H.inv_mem hw1)
  have hd10 : ∀ c, elt (.difference 1 0 (by decide)) c ∈ H := by
    intro c
    have key := wl0_mul_posSum (F := F) (-c)
    rw [neg_neg] at key
    have : elt (.difference 1 0 (by decide)) c = wl F 0 * elt (.positiveSum 0 1 (by decide)) (-c) *
        (wl F 0)⁻¹ := by
      rw [key, mul_inv_cancel_right]
    rw [this]
    exact H.mul_mem (H.mul_mem hw0 (hsum _)) (H.inv_mem hw0)
  have hneg : ∀ c, elt (.negativeSum 0 1 (by decide)) c ∈ H := by
    intro c
    have key := wl0_mul_diff (F := F) c
    have : elt (.negativeSum 0 1 (by decide)) c = wl F 0 * elt (.difference 0 1 (by decide)) c *
        (wl F 0)⁻¹ := by
      rw [key, mul_inv_cancel_right]
    rw [this]
    exact H.mul_mem (H.mul_mem hw0 (hd01 _)) (H.inv_mem hw0)
  apply eq_top_of_elt_mem
  intro r c
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · fin_cases i
    · exact hpl0 c
    · exact hpl1 c
  · fin_cases i
    · exact hnl0 c
    · exact hnl1 c
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hd01 c
    · exact hd10 c
    · exact absurd rfl hij
  · fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · exact hsum c
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
  · fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · exact hneg c
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)

end CFSG.ClassicalInvolution.RouteD.SCRSp4
