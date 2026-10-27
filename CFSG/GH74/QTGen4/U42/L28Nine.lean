module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.GH74.QTGen4.U42.L28Nine

open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Field8

variable {K : Type} [Field K]

def fibT (t : K) : ℕ → K
  | 0 => 0
  | 1 => 1
  | (n + 2) => t * fibT t (n + 1) + fibT t n

def comp (t : K) : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, t]

lemma comp_mul_self (t : K) : comp t * comp t = t • comp t + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [comp, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma comp_pow (t : K) (n : ℕ) :
    comp t ^ (n + 1) = fibT t (n + 1) • comp t + fibT t n • (1 : Matrix (Fin 2) (Fin 2) K) := by
  induction n with
  | zero => simp [fibT]
  | succ n ih =>
    rw [pow_succ, ih]
    have key : (fibT t (n + 1) • comp t + fibT t n • (1 : Matrix (Fin 2) (Fin 2) K)) * comp t
        = fibT t (n + 1) • (comp t * comp t) + fibT t n • comp t := by
      rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
    rw [key, comp_mul_self, show fibT t (n + 1 + 1) = t * fibT t (n + 1) + fibT t n from rfl]
    module

lemma comp_det (t : K) (h2 : (2 : K) = 0) : (comp t).det = 1 := by
  rw [comp, Matrix.det_fin_two_of]
  linear_combination (-1 : K) * h2

lemma fibT_two (t : K) : fibT t 2 = t := by
  simp only [fibT]; ring

lemma fibT_three (t : K) : fibT t 3 = t ^ 2 + 1 := by
  simp only [fibT, fibT_two]; ring

lemma fibT_eight (t : K) : fibT t 8 = t ^ 7 + 6 * t ^ 5 + 10 * t ^ 3 + 4 * t := by
  simp only [fibT, fibT_two, fibT_three]; ring

lemma fibT_nine (t : K) : fibT t 9 = t ^ 8 + 7 * t ^ 6 + 15 * t ^ 4 + 10 * t ^ 2 + 1 := by
  simp only [fibT, fibT_two, fibT_three, fibT_eight]; ring

lemma fibT_nine_zero (t : K) (ht : t ^ 3 = t + 1) (h2 : (2 : K) = 0) : fibT t 9 = 0 := by
  rw [fibT_nine]
  linear_combination (t ^ 5 + 2 * t ^ 3 + t ^ 2 + 3 * t + 3) * ht
    + (2 * t ^ 2 + 3 * t + 2 + 3 * t ^ 6 + 7 * t ^ 4 + 5 * t ^ 2) * h2

lemma fibT_eight_one (t : K) (ht : t ^ 3 = t + 1) (h2 : (2 : K) = 0) : fibT t 8 = 1 := by
  rw [fibT_eight]
  linear_combination (t ^ 4 + t ^ 2 + t + 1) * ht
    + (t ^ 2 + t + 3 * t ^ 5 + 5 * t ^ 3 + 2 * t) * h2

lemma comp_pow_nine (t : K) (ht : t ^ 3 = t + 1) (h2 : (2 : K) = 0) : comp t ^ 9 = 1 := by
  have h : comp t ^ 9 = fibT t 9 • comp t + fibT t 8 • (1 : Matrix (Fin 2) (Fin 2) K) :=
    comp_pow t 8
  rw [h, fibT_nine_zero t ht h2, fibT_eight_one t ht h2, zero_smul, one_smul, zero_add]

lemma comp_pow3_01 (t : K) : (comp t ^ 3) 0 1 = t ^ 2 + 1 := by
  have h : comp t ^ 3 = fibT t 3 • comp t + fibT t 2 • (1 : Matrix (Fin 2) (Fin 2) K) :=
    comp_pow t 2
  rw [h, fibT_three, fibT_two]
  simp [comp]

lemma sq_add_one_ne_zero (t : K) (ht : t ^ 3 = t + 1) (h2 : (2 : K) = 0) : t ^ 2 + 1 ≠ 0 := by
  intro hq
  have h1 : (1 : K) = 0 := by linear_combination t * hq - ht - t * h2
  exact one_ne_zero h1

def gSL (t : K) (h2 : (2 : K) = 0) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨comp t, comp_det t h2⟩

lemma gSL_pow_nine (t : K) (ht : t ^ 3 = t + 1) (h2 : (2 : K) = 0) : gSL t h2 ^ 9 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  exact comp_pow_nine t ht h2

end Field8

lemma orderOf_mk_nine {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : G)
    (h9 : g ^ 9 = 1) (h3 : g ^ 3 ∉ N) : orderOf (g : G ⧸ N) = 9 := by
  have hnot : ¬ (g : G ⧸ N) ^ 3 ^ 1 = 1 := by
    intro h
    rw [show (3 : ℕ) ^ 1 = 3 from rfl, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
    exact h3 h
  have hfin : (g : G ⧸ N) ^ 3 ^ (1 + 1) = 1 := by
    rw [show (3 : ℕ) ^ (1 + 1) = 9 from rfl, ← QuotientGroup.mk_pow, h9]
    simp
  have := orderOf_eq_prime_pow hnot hfin
  rw [this]
  norm_num

section Field8'

variable {K : Type} [Field K]

theorem two_eq_zero_of_card (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = 8) :
    (2 : K) = 0 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  rw [hK] at hn
  have hd : ringChar K ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, hn]
    exact dvd_pow_self _ (PNat.ne_zero n)
  have hd2 : ringChar K ∣ 2 := hp.dvd_of_dvd_pow hd
  have hp2 : ringChar K = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd2
  have hc : ((ringChar K : ℕ) : K) = 0 := CharP.cast_eq_zero K (ringChar K)
  rw [hp2] at hc
  exact_mod_cast hc

theorem exists_cube_root (K : Type) [Field K] [Fintype K] (h2 : (2 : K) = 0)
    (hK : Fintype.card K = 8) : ∃ t : K, t ^ 3 = t + 1 := by
  classical
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset K)) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_two (by rw [Finset.card_univ, hK]; norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  obtain ⟨ha0, ha1⟩ := ha
  have ha7 : a ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one a ha0
    rw [hK] at this
    exact this
  have hfac : (a - 1) * ((a ^ 3 + a + 1) * (a ^ 3 + a ^ 2 + 1)) = 0 := by
    linear_combination ha7 + (a ^ 4 - a ^ 3) * h2
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) ha1
  rcases mul_eq_zero.mp h with h' | h'
  · exact ⟨a, by linear_combination h' + (-(a + 1)) * h2⟩
  · exact ⟨a ^ 6, by
      linear_combination (a ^ 4 * (a ^ 7 + 1)) * ha7 - (a ^ 3 - a ^ 2 - 1) * h'
        + (-(a ^ 2 + 1)) * h2⟩

lemma gSL_pow3_not_central (t : K) (ht : t ^ 3 = t + 1) (h2 : (2 : K) = 0) :
    gSL t h2 ^ 3 ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro hc
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have key := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hr
  have e1 : ((gSL t h2 ^ 3 : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1
      = t ^ 2 + 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact comp_pow3_01 t
  rw [e1] at key
  simp [Matrix.scalar_apply, Matrix.diagonal_apply] at key
  exact sq_add_one_ne_zero t ht h2 (by first | exact key | exact key.symm)

theorem exists_nine_psl (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = 8) :
    ∃ y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, orderOf y = 9 := by
  have h2 := two_eq_zero_of_card K hK
  obtain ⟨t, ht⟩ := exists_cube_root K h2 hK
  exact ⟨((gSL t h2 : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K),
    orderOf_mk_nine _ _ (gSL_pow_nine t ht h2) (gSL_pow3_not_central t ht h2)⟩

lemma toGL_gSL_mem (t : K) (h2 : (2 : K) = 0) :
    Matrix.SpecialLinearGroup.toGL (gSL t h2 : Matrix.SpecialLinearGroup (Fin 2) K) ∈
      StatedSL 2 K := by
  apply Subgroup.subset_closure
  exact (gSL t h2).2

def stateElt (t : K) (h2 : (2 : K) = 0) : ↥(StatedSL 2 K) :=
  ⟨Matrix.SpecialLinearGroup.toGL (gSL t h2 : Matrix.SpecialLinearGroup (Fin 2) K),
    toGL_gSL_mem t h2⟩

lemma stateElt_pow_nine (t : K) (ht : t ^ 3 = t + 1) (h2 : (2 : K) = 0) :
    stateElt t h2 ^ 9 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  show Matrix.SpecialLinearGroup.toGL (gSL t h2 : Matrix.SpecialLinearGroup (Fin 2) K) ^ 9 = 1
  rw [← map_pow, gSL_pow_nine t ht h2, map_one]

lemma toGL_pow3_not_scalar (t : K) (ht : t ^ 3 = t + 1) (h2 : (2 : K) = 0) :
    Matrix.SpecialLinearGroup.toGL (gSL t h2 : Matrix.SpecialLinearGroup (Fin 2) K) ^ 3 ∉
      StatedScalars (Fin 2) K := by
  intro hc
  have hc' : Matrix.SpecialLinearGroup.toGL (gSL t h2 : Matrix.SpecialLinearGroup (Fin 2) K) ^ 3 ∈
      (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := hc
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hc'
  have key := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 0 1) hu
  have e1 : ((Matrix.SpecialLinearGroup.toGL (gSL t h2 : Matrix.SpecialLinearGroup (Fin 2) K) ^ 3 :
      Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = t ^ 2 + 1 := by
    rw [Units.val_pow_eq_pow_val]
    have hc0 : ((Matrix.SpecialLinearGroup.toGL (gSL t h2 : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = comp t := rfl
    rw [hc0]
    exact comp_pow3_01 t
  rw [e1] at key
  simp [Matrix.GeneralLinearGroup.scalar, Units.coe_map, Matrix.scalar_apply,
    Matrix.diagonal_apply] at key
  exact sq_add_one_ne_zero t ht h2 (by first | exact key | exact key.symm)

lemma stateElt_pow_three_not_scalar (t : K) (ht : t ^ 3 = t + 1) (h2 : (2 : K) = 0) :
    ¬ (((stateElt t h2 ^ 3 : ↥(StatedSL 2 K)) : Matrix.GeneralLinearGroup (Fin 2) K) ∈
      StatedScalars (Fin 2) K) := by
  rw [Subgroup.coe_pow]
  exact toGL_pow3_not_scalar t ht h2

theorem exists_nine_statedProj (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = 8) :
    ∃ y : StatedProj (StatedSL 2 K), orderOf y = 9 := by
  have h2 := two_eq_zero_of_card K hK
  obtain ⟨t, ht⟩ := exists_cube_root K h2 hK
  have h3 : stateElt t h2 ^ 3 ∉ (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) := by
    rw [Subgroup.mem_subgroupOf]
    exact stateElt_pow_three_not_scalar t ht h2
  exact ⟨((stateElt t h2 : ↥(StatedSL 2 K)) : StatedProj (StatedSL 2 K)),
    orderOf_mk_nine _ _ (stateElt_pow_nine t ht h2) h3⟩

end Field8'

theorem exists_orderOf_nine_of_lieModel_psl2_three {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSL 2 2 3) : ∃ x : X, orderOf x = 9 := by
  rcases h with ⟨-, hc⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hc
    have hK8 : Nat.card K = 8 := by simpa using hcard
    letI := Fintype.ofFinite K
    have hK : Fintype.card K = 8 := by rw [← Nat.card_eq_fintype_card]; exact hK8
    obtain ⟨y, hy⟩ := exists_nine_statedProj K hK
    exact ⟨e.symm y, (e.symm.orderOf_eq y).trans hy⟩
  · exact absurd hn (by norm_num)
  · exact absurd hn (by norm_num)
  · exact absurd hn (by norm_num)

theorem isL2Quot_three_exists_orderOf_nine {X : Type*} [Group X]
    (h : CFSG.Quasithin.IsL2Quot 3 X) : ∃ x : X, orderOf x = 9 := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  have hK8 : Nat.card (GaloisField 2 3) = 8 := by simpa using hcard
  letI := Fintype.ofFinite (GaloisField 2 3)
  have hK : Fintype.card (GaloisField 2 3) = 8 := by rw [← Nat.card_eq_fintype_card]; exact hK8
  obtain ⟨y, hy⟩ := exists_nine_psl (GaloisField 2 3) hK
  exact ⟨e.symm y, (e.symm.orderOf_eq y).trans hy⟩

end CFSG.GH74.QTGen4.U42.L28Nine
