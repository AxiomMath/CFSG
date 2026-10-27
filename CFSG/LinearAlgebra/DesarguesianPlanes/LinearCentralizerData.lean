module

public import CFSG.LinearAlgebra.DesarguesianPlanes.RootModule
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.DesarguesianPlanes

open Matrix
open scoped commutatorElement

variable {G : Type*} [Group G] {F : Type} [Field F]

@[expose] noncomputable def swapGL : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [det_fin_two])

theorem swapGL_mul_self : (swapGL : GL (Fin 2) F) * swapGL = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapGL_mul_upperGL (c : F) : (swapGL : GL (Fin 2) F) * upperGL c = lowerGL c * swapGL := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapGL, upperGL, lowerGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapGL_mul_diagGL (a b : Fˣ) :
    (swapGL : GL (Fin 2) F) * diagGL a b = diagGL b a * swapGL := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapGL, diagGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem neg_one_eq_diagGL : (-1 : GL (Fin 2) F) = diagGL (-1) (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL]

theorem diagGL_one_one : (diagGL 1 1 : GL (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL]

theorem diagGL_pow (a b : Fˣ) (n : ℕ) :
    (diagGL a b : GL (Fin 2) F) ^ n = diagGL (a ^ n) (b ^ n) := by
  induction n with
  | zero => simp [diagGL_one_one]
  | succ n ih => rw [pow_succ, ih, diagGL_mul, pow_succ, pow_succ]

theorem upperGL_nsmul (c : F) (n : ℕ) : (upperGL c : GL (Fin 2) F) ^ n = upperGL (n * c) := by
  induction n with
  | zero => simp [upperGL_zero]
  | succ n ih => rw [pow_succ, ih, upperGL_add]; push_cast; ring_nf

theorem lowerGL_nsmul (c : F) (n : ℕ) : (lowerGL c : GL (Fin 2) F) ^ n = lowerGL (n * c) := by
  induction n with
  | zero => simp [lowerGL_zero]
  | succ n ih => rw [pow_succ, ih, lowerGL_add]; push_cast; ring_nf

theorem exists_diagGL_of_commute (h2 : (2 : F) ≠ 0) (A : GL (Fin 2) F)
    (hA : A * diagGL 1 (-1) = diagGL 1 (-1) * A) : ∃ a b : Fˣ, A = diagGL a b := by
  have h01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) hA
    simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two] at this
    have h : 2 * (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination -this
    exact (mul_eq_zero.mp h).resolve_left h2
  have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 1 0) hA
    simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two] at this
    have h : 2 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination this
    exact (mul_eq_zero.mp h).resolve_left h2
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have := A.isUnit.map Matrix.detMonoidHom
    exact this.ne_zero
  rw [det_fin_two, h01, h10, mul_zero, sub_zero] at hdet
  have h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨Units.mk0 _ h00, Units.mk0 _ h11, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL, h01, h10]

theorem eq_one_of_mem_odd_of_det (h2 : (2 : F) ≠ 0) {Z : Subgroup (GL (Fin 2) F)}
    (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
    {A : GL (Fin 2) F} (hA : A ∈ Z)
    (hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1) : A = 1 := by
  obtain ⟨μ, hμ⟩ := hZ hA
  have hμ2 : (μ : F) ^ 2 = 1 := by
    rw [← hμ] at hdet
    simpa [Matrix.det_fin_two, sq] using hdet
  have hμ' : (μ : F) = 1 ∨ (μ : F) = -1 := by
    have : ((μ : F) - 1) * ((μ : F) + 1) = 0 := by linear_combination hμ2
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hμ' with h1 | hm1
  · rw [← hμ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1]
  · exfalso
    have hneg : (-1 : GL (Fin 2) F) ∈ Z := by
      have : A = -1 := by
        rw [← hμ]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hm1]
      rwa [← this]
    have hne : (-1 : GL (Fin 2) F) ≠ 1 := by
      intro h
      have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simp at this
      exact h2 (by linear_combination -this)
    have hord : orderOf (⟨-1, hneg⟩ : Z) = 2 := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        simp
      · intro h
        apply hne
        exact congrArg Subtype.val h
    have hdvd := orderOf_dvd_natCard (⟨-1, hneg⟩ : Z)
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr hdvd)


theorem upperGL_mem_scalars_iff (c : F) :
    upperGL c ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F ↔ c = 0 := by
  constructor
  · rintro ⟨μ, hμ⟩
    have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) hμ
    simpa [upperGL] using this.symm
  · rintro rfl
    rw [upperGL_zero]
    exact Subgroup.one_mem _

theorem lowerGL_mem_scalars_iff (c : F) :
    lowerGL c ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F ↔ c = 0 := by
  constructor
  · rintro ⟨μ, hμ⟩
    have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 1 0) hμ
    simpa [lowerGL] using this.symm
  · rintro rfl
    rw [lowerGL_zero]
    exact Subgroup.one_mem _

section Centralizer

variable {Z : Subgroup (GL (Fin 2) F)} [Z.Normal] {J : G}
  (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)

@[expose] noncomputable def linearCentralizerHom : GL (Fin 2) F →* G :=
  (Subgroup.centralizer ({J} : Set G)).subtype.comp (φ.symm.toMonoidHom.comp (QuotientGroup.mk' Z))

theorem linearCentralizerHom_apply (A : GL (Fin 2) F) :
    linearCentralizerHom φ A = (φ.symm (QuotientGroup.mk A) : G) := rfl

theorem linearCentralizerHom_eq_one_iff (A : GL (Fin 2) F) :
    linearCentralizerHom φ A = 1 ↔ A ∈ Z := by
  rw [linearCentralizerHom_apply, ← (Subgroup.centralizer ({J} : Set G)).coe_one,
    Subtype.ext_iff.symm.eq,
    show (1 : Subgroup.centralizer ({J} : Set G)) = φ.symm 1 from (map_one _).symm]
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff A).mp (φ.symm.injective h)
  · intro h
    rw [(QuotientGroup.eq_one_iff A).mpr h]

theorem linearCentralizerHom_commute (A : GL (Fin 2) F) :
    J * linearCentralizerHom φ A = linearCentralizerHom φ A * J := by
  have h := (φ.symm (QuotientGroup.mk A)).2
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  exact h.symm

theorem exists_linearCentralizerHom_eq {g : G} (hg : J * g = g * J) :
    ∃ A : GL (Fin 2) F, linearCentralizerHom φ A = g := by
  have hmem : g ∈ Subgroup.centralizer ({J} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hg.symm
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective (φ ⟨g, hmem⟩)
  refine ⟨A, ?_⟩
  rw [linearCentralizerHom_apply, hA, MulEquiv.symm_apply_apply]

theorem linearCentralizerHom_eq_iff (A B : GL (Fin 2) F) :
    linearCentralizerHom φ A = linearCentralizerHom φ B ↔ A * B⁻¹ ∈ Z := by
  rw [← linearCentralizerHom_eq_one_iff φ, map_mul, map_inv, mul_inv_eq_one]

noncomputable abbrev rootUp (c : F) : G := linearCentralizerHom φ (upperGL c)

noncomputable abbrev rootLow (c : F) : G := linearCentralizerHom φ (lowerGL c)

variable (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
include hZ

theorem rootUp_injective : Function.Injective (rootUp φ) := by
  intro c d h
  rw [rootUp, rootUp, linearCentralizerHom_eq_iff] at h
  have h' := hZ h
  rw [show upperGL c * (upperGL d)⁻¹ = upperGL (c - d) by
    rw [mul_inv_eq_iff_eq_mul, upperGL_add, sub_add_cancel]] at h'
  exact sub_eq_zero.mp ((upperGL_mem_scalars_iff (c - d)).mp h')

theorem rootLow_injective : Function.Injective (rootLow φ) := by
  intro c d h
  rw [rootLow, rootLow, linearCentralizerHom_eq_iff] at h
  have h' := hZ h
  rw [show lowerGL c * (lowerGL d)⁻¹ = lowerGL (c - d) by
    rw [mul_inv_eq_iff_eq_mul, lowerGL_add, sub_add_cancel]] at h'
  exact sub_eq_zero.mp ((lowerGL_mem_scalars_iff (c - d)).mp h')


variable (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0)
include hZodd h2

theorem exists_diag_of_commute {g : G} (hgJ : J * g = g * J)
    (hg₁ : linearCentralizerHom φ (diagGL 1 (-1)) * g =
      g * linearCentralizerHom φ (diagGL 1 (-1))) :
    ∃ a b : Fˣ, g = linearCentralizerHom φ (diagGL a b) := by
  obtain ⟨A, rfl⟩ := exists_linearCentralizerHom_eq φ hgJ
  have hmem : A * diagGL 1 (-1) * (diagGL 1 (-1) * A)⁻¹ ∈ Z :=
    (linearCentralizerHom_eq_iff φ _ _).mp (by rw [map_mul, map_mul, hg₁])
  have hdet : ((A * diagGL 1 (-1) * (diagGL 1 (-1) * A)⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have hA : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (A.isUnit.map Matrix.detMonoidHom).ne_zero
    have hD : ((diagGL 1 (-1) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
      ((diagGL 1 (-1) : GL (Fin 2) F).isUnit.map Matrix.detMonoidHom).ne_zero
    simp only [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_inv,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [mul_comm (((diagGL 1 (-1) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det)]
    exact mul_inv_cancel₀ (mul_ne_zero hA hD)
  have h1 := eq_one_of_mem_odd_of_det h2 hZ hZodd hmem hdet
  rw [mul_inv_eq_one] at h1
  exact (exists_diagGL_of_commute h2 A h1).imp fun a ⟨b, hb⟩ => ⟨b, by rw [hb]⟩


theorem commute_of_linearCentralizerHom_commute {A B : GL (Fin 2) F}
    (h : linearCentralizerHom φ A * linearCentralizerHom φ B =
      linearCentralizerHom φ B * linearCentralizerHom φ A) : A * B = B * A := by
  have hmem : A * B * (B * A)⁻¹ ∈ Z :=
    (linearCentralizerHom_eq_iff φ _ _).mp (by rw [map_mul, map_mul, h])
  have hdet : ((A * B * (B * A)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have hA : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (A.isUnit.map Matrix.detMonoidHom).ne_zero
    have hB : (B : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (B.isUnit.map Matrix.detMonoidHom).ne_zero
    simp only [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_inv,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [mul_comm (B : Matrix (Fin 2) (Fin 2) F).det]
    exact mul_inv_cancel₀ (mul_ne_zero hA hB)
  exact mul_inv_eq_one.mp (eq_one_of_mem_odd_of_det h2 hZ hZodd hmem hdet)

theorem linearCentralizerHom_neg_one (hJ : orderOf J = 2) : linearCentralizerHom φ (-1) = J := by
  obtain ⟨A₀, hA₀⟩ := exists_linearCentralizerHom_eq φ (g := J) rfl
  have hcomm : ∀ B, A₀ * B = B * A₀ := fun B =>
    commute_of_linearCentralizerHom_commute φ hZ hZodd h2
      (by rw [hA₀]; exact linearCentralizerHom_commute φ B)
  have hcenter : A₀ ∈ Subgroup.center (GL (Fin 2) F) :=
    Subgroup.mem_center_iff.mpr fun B => (hcomm B).symm
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨a, rfl⟩ := hcenter
  have hJ1 : J ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hJ
    exact absurd hJ (by norm_num)
  have hJ2 : J ^ 2 = 1 := by rw [← hJ]; exact pow_orderOf_eq_one J
  have ha2 : Matrix.GeneralLinearGroup.scalar (Fin 2) (a ^ 2) ∈ Z := by
    rw [← linearCentralizerHom_eq_one_iff φ, map_pow, map_pow, hA₀, hJ2]
  have ha : Matrix.GeneralLinearGroup.scalar (Fin 2) a ∉ Z := by
    rw [← linearCentralizerHom_eq_one_iff φ, hA₀]
    exact hJ1
  set k := (Nat.card Z + 1) / 2 with hk
  have hk2 : 2 * k = Nat.card Z + 1 := by
    obtain ⟨m, hm⟩ := hZodd
    omega
  set y : Z := ⟨_, ha2⟩ ^ k with hy
  have hy2 : (y : GL (Fin 2) F) ^ 2 = Matrix.GeneralLinearGroup.scalar (Fin 2) (a ^ 2) := by
    have : y ^ 2 = ⟨_, ha2⟩ := by
      rw [hy, ← pow_mul, mul_comm, hk2, pow_succ, pow_card_eq_one', one_mul]
    rw [← Subgroup.coe_pow, this]
  obtain ⟨b, hb⟩ := hZ y.2
  rw [← hb, ← map_pow] at hy2
  have hb2 : b ^ 2 = a ^ 2 := by
    have hinj : Function.Injective
        (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) := by
      intro u v huv
      have := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) huv
      exact Units.ext (by simpa using this)
    exact hinj hy2
  have hbF : (b : F) = a ∨ (b : F) = -a := by
    have h := congrArg (fun u : Fˣ => (u : F)) hb2
    simp only [Units.val_pow_eq_pow_val] at h
    have : ((b : F) - a) * ((b : F) + a) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · left; linear_combination h'
    · right; linear_combination h'
  rcases hbF with h | h
  · exfalso
    apply ha
    have hba : b = a := Units.ext h
    rw [← hba, hb]
    exact y.2
  · have hba : b = -a := Units.ext (by rw [h, Units.val_neg])
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 2) (-a) ∈ Z := by
      rw [← hba, hb]
      exact y.2
    refine Eq.trans ?_ hA₀
    rw [linearCentralizerHom_eq_iff]
    have hneg : (-1 : GL (Fin 2) F) = Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have : (-1 : GL (Fin 2) F) * (Matrix.GeneralLinearGroup.scalar (Fin 2) a)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (-a) *
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (a ^ 2))⁻¹ := by
      rw [hneg, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Units.ext
      have ha0 : (a : F) ≠ 0 := a.ne_zero
      simp only [Units.val_mul, Units.val_neg, Units.val_one, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val]
      field_simp
    rw [this]
    exact Z.mul_mem hmem (Z.inv_mem ha2)


omit hZ hZodd h2 in
theorem rootUp_pow (c : F) (n : ℕ) : rootUp φ c ^ n = rootUp φ (n * c) := by
  rw [rootUp, rootUp, ← map_pow, upperGL_nsmul]

omit hZ hZodd h2 in
theorem rootLow_pow (c : F) (n : ℕ) : rootLow φ c ^ n = rootLow φ (n * c) := by
  rw [rootLow, rootLow, ← map_pow, lowerGL_nsmul]

omit hZ hZodd h2 in
theorem rootUp_pow_ringChar (c : F) : rootUp φ c ^ ringChar F = 1 := by
  rw [rootUp_pow, ringChar.Nat.cast_ringChar, zero_mul, rootUp, upperGL_zero, map_one]

omit hZ hZodd h2 in
theorem rootLow_pow_ringChar (c : F) : rootLow φ c ^ ringChar F = 1 := by
  rw [rootLow_pow, ringChar.Nat.cast_ringChar, zero_mul, rootLow, lowerGL_zero, map_one]

omit hZ hZodd h2 in
theorem diag_pow_card_sub_one [Fintype F] (a b : Fˣ) :
    linearCentralizerHom φ (diagGL a b) ^ (Fintype.card F - 1) = 1 := by
  rw [← map_pow, diagGL_pow]
  have h : ∀ u : Fˣ, u ^ (Fintype.card F - 1) = 1 := fun u =>
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one,
      FiniteField.pow_card_sub_one_eq_one _ u.ne_zero])
  rw [h, h, diagGL_one_one, map_one]

omit [Z.Normal] hZ hZodd h2 in
theorem eq_one_of_pow_ringChar_of_pow_card_sub_one [Fintype F] {g : G}
    (hp : g ^ ringChar F = 1) (hq : g ^ (Fintype.card F - 1) = 1) : g = 1 := by
  have hprime : (ringChar F).Prime := CharP.char_is_prime F _
  have hcop : Nat.Coprime (ringChar F) (Fintype.card F - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hprime]
    intro hdvd
    have hcard : ringChar F ∣ Fintype.card F := ringChar.dvd (FiniteField.cast_card_eq_zero F)
    have hpos : 0 < Fintype.card F := Fintype.card_pos
    have : ringChar F ∣ Fintype.card F - (Fintype.card F - 1) := Nat.dvd_sub hcard hdvd
    rw [Nat.sub_sub_self hpos] at this
    exact hprime.one_lt.ne' (Nat.dvd_one.mp this)
  have := pow_gcd_eq_one.mpr ⟨hp, hq⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

end Centralizer

end CFSG.DesarguesianPlanes
