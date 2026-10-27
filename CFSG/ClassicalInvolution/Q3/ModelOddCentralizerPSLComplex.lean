module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareLinear
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

section Model

variable (F : Type) [Field F]

abbrev GaussField : Type := QuadraticAlgebra F (-1 : F) 0

theorem card_gaussField [Finite F] : Nat.card (GaussField F) = Nat.card F ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-1 : F) 0), Nat.card_prod, sq]

@[expose] def gaussRho : GaussField F →+* Matrix (Fin 2) (Fin 2) F where
  toFun z := !![z.re, -z.im; z.im, z.re]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' z w := by
    ext i j
    fin_cases i <;> fin_cases j <;> first | (simp; done) | (simp; ring)

theorem gaussRho_injective : Function.Injective (gaussRho F) := by
  intro z w h
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp [gaussRho] at h00 h10
  exact QuadraticAlgebra.ext h00 h10

variable {F}

@[expose] noncomputable def gaussIota (m : ℕ) :
    Matrix (Fin m) (Fin m) (GaussField F) →+* Matrix (Fin m × Fin 2) (Fin m × Fin 2) F :=
  (Matrix.compRingEquiv (Fin m) (Fin 2) F).toRingHom.comp (gaussRho F).mapMatrix

theorem gaussIota_apply (m : ℕ) (A : Matrix (Fin m) (Fin m) (GaussField F)) (k l : Fin m)
    (p q : Fin 2) : gaussIota m A (k, p) (l, q) = gaussRho F (A k l) p q := rfl

theorem gaussIota_injective (m : ℕ) : Function.Injective (gaussIota (F := F) m) :=
  (Matrix.compRingEquiv (Fin m) (Fin 2) F).injective.comp
    (Matrix.map_injective (gaussRho_injective F))

theorem gaussIota_scalar_algebraMap (m : ℕ) (c : F) :
    gaussIota m (Matrix.scalar (Fin m) (algebraMap F (GaussField F) c)) =
      Matrix.scalar (Fin m × Fin 2) c := by
  ext ⟨k, p⟩ ⟨l, q⟩
  rw [gaussIota_apply]
  by_cases hkl : k = l
  · subst hkl
    fin_cases p <;> fin_cases q <;> simp [Matrix.scalar_apply, gaussRho]
  · simp [Matrix.scalar_apply, hkl]

theorem gaussIota_omega_apply (m : ℕ) (j l : Fin m) (r q : Fin 2) :
    gaussIota (F := F) m (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F))
        (j, r) (l, q) = if j = l then (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) r q else 0 := by
  rw [gaussIota_apply]
  by_cases hjl : j = l
  · subst hjl
    fin_cases r <;> fin_cases q <;> simp [Matrix.scalar_apply, gaussRho]
  · simp [Matrix.scalar_apply, hjl]

theorem exists_gaussIota_of_commute (m : ℕ) {X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) F}
    (hX : X * gaussIota m (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F)) =
      gaussIota m (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F)) * X) :
    ∃ A : Matrix (Fin m) (Fin m) (GaussField F), gaussIota m A = X := by
  have h1 : ∀ k l, X (k, 0) (l, 1) = - X (k, 1) (l, 0) := by
    intro k l
    have h := congrFun (congrFun hX (k, 0)) (l, 0)
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      gaussIota_omega_apply] at h
    simpa [Finset.sum_ite_eq] using h
  have h2 : ∀ k l, X (k, 1) (l, 1) = X (k, 0) (l, 0) := by
    intro k l
    have h := congrFun (congrFun hX (k, 0)) (l, 1)
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      gaussIota_omega_apply] at h
    simpa [Finset.sum_ite_eq] using h.symm
  refine ⟨Matrix.of fun k l => (⟨X (k, 0) (l, 0), X (k, 1) (l, 0)⟩ : GaussField F), ?_⟩
  ext ⟨k, p⟩ ⟨l, q⟩
  rw [gaussIota_apply]
  fin_cases p <;> fin_cases q <;> simp [gaussRho, h1, h2]

end Model

section Facts

variable {F : Type} [Field F] [Finite F] [Fact (¬ IsSquare (-1 : F))]

instance gaussField_finite : Finite (GaussField F) :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd (-1 : F) 0).symm

omit [Fact ¬IsSquare (-1 : F)] in
theorem card_gaussField_eq_nine (hF : Nat.card F = 3) : Nat.card (GaussField F) = 9 := by
  rw [card_gaussField, hF]
  norm_num

theorem isPerfect_specialLinear_gauss (hF : Nat.card F = 3) {m : ℕ} (hm : 2 ≤ m) :
    Group.IsPerfect (SpecialLinearGroup (Fin m) (GaussField F)) := by
  have : Fintype (GaussField F) := Fintype.ofFinite _
  refine CFSG.LinearGroups.special_linear_isPerfect hm (Or.inr ?_)
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (GaussField F))) (n := 4) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_gaussField_eq_nine hF]
      norm_num)
  exact ⟨t, ht⟩

@[expose] noncomputable def gaussDet (m : ℕ) :
    SpecialLinearGroup (Fin m) (GaussField F) →* F where
  toFun A := (gaussIota m (A : Matrix (Fin m) (Fin m) (GaussField F))).det
  map_one' := by simp
  map_mul' A B := by simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.det_mul]

theorem gaussDet_eq_one (hF : Nat.card F = 3) {m : ℕ} (hm : 2 ≤ m)
    (A : SpecialLinearGroup (Fin m) (GaussField F)) : gaussDet m A = 1 := by
  have hperf := isPerfect_specialLinear_gauss hF hm
  have hker : commutator (SpecialLinearGroup (Fin m) (GaussField F)) ≤
      ((gaussDet (F := F) m).toHomUnits).ker := Abelianization.commutator_subset_ker _
  rw [hperf.commutator_eq_top] at hker
  have h1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top A))
  have h2 : (((gaussDet (F := F) m).toHomUnits A : Fˣ) : F) = 1 := by rw [h1]; rfl
  simpa using h2

@[expose] noncomputable def gaussTheta (hF : Nat.card F = 3) {m : ℕ} (hm : 2 ≤ m) :
    SpecialLinearGroup (Fin m) (GaussField F) →* SpecialLinearGroup (Fin m × Fin 2) F where
  toFun A := ⟨gaussIota m (A : Matrix (Fin m) (Fin m) (GaussField F)), gaussDet_eq_one hF hm A⟩
  map_one' := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    show gaussIota m ((A * B : SpecialLinearGroup (Fin m) (GaussField F)) :
      Matrix (Fin m) (Fin m) (GaussField F)) = gaussIota m (A : Matrix (Fin m) (Fin m)
        (GaussField F)) * gaussIota m (B : Matrix (Fin m) (Fin m) (GaussField F))
    rw [Matrix.SpecialLinearGroup.coe_mul, map_mul])

theorem coe_gaussTheta (hF : Nat.card F = 3) {m : ℕ} (hm : 2 ≤ m)
    (A : SpecialLinearGroup (Fin m) (GaussField F)) :
    ((gaussTheta hF hm A : SpecialLinearGroup (Fin m × Fin 2) F) :
      Matrix (Fin m × Fin 2) (Fin m × Fin 2) F) =
      gaussIota m (A : Matrix (Fin m) (Fin m) (GaussField F)) := rfl

theorem gaussTheta_injective (hF : Nat.card F = 3) {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (gaussTheta hF hm) := by
  intro A B h
  apply Subtype.ext
  exact gaussIota_injective m (congrArg (fun x : SpecialLinearGroup (Fin m × Fin 2) F =>
    (x : Matrix (Fin m × Fin 2) (Fin m × Fin 2) F)) h)

end Facts

section Main

variable {F : Type} [Field F] [Finite F] [Fact (¬ IsSquare (-1 : F))]

theorem isQuasisimple_specialLinear_gauss (hF : Nat.card F = 3) {k : ℕ} (hk : 2 ≤ k) :
    CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin k) (GaussField F)) := by
  rcases Nat.lt_or_ge k 3 with h | h
  · obtain rfl : k = 2 := by omega
    exact CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two
      (by rw [card_gaussField_eq_nine hF]; norm_num)
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple m (GaussField F) (by omega))

theorem oddCoreIn_centralizer_eq_bot_of_gaussOmega (hF : Nat.card F = 3) {m : ℕ} (hm : 2 ≤ m)
    (hZ : IsPGroup 2 (Subgroup.center (SpecialLinearGroup (Fin m × Fin 2) F)))
    (g : SpecialLinearGroup (Fin m × Fin 2) F)
    (hg : (g : Matrix (Fin m × Fin 2) (Fin m × Fin 2) F) =
      gaussIota m (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F))) :
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk g : SpecialLinearGroup (Fin m × Fin 2) F ⧸
        Subgroup.center (SpecialLinearGroup (Fin m × Fin 2) F))} :
        Set (SpecialLinearGroup (Fin m × Fin 2) F ⧸
          Subgroup.center (SpecialLinearGroup (Fin m × Fin 2) F)))) = ⊥ := by
  set ω : GaussField F := QuadraticAlgebra.omega with hω
  set Θ := gaussTheta hF hm with hΘ
  have hcomm : ∀ x : SpecialLinearGroup (Fin m × Fin 2) F,
      x ∈ Subgroup.centralizer ({g} : Set (SpecialLinearGroup (Fin m × Fin 2) F)) ↔
        (x : Matrix (Fin m × Fin 2) (Fin m × Fin 2) F) * gaussIota m (Matrix.scalar (Fin m) ω) =
          gaussIota m (Matrix.scalar (Fin m) ω) * x := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' := congrArg (fun y : SpecialLinearGroup (Fin m × Fin 2) F =>
        (y : Matrix (Fin m × Fin 2) (Fin m × Fin 2) F)) h
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hg] using h'
    · intro h
      ext i j
      have h' := congrFun (congrFun h i) j
      simpa only [Matrix.SpecialLinearGroup.coe_mul, hg] using h'
  have hscal : ∀ A : Matrix (Fin m) (Fin m) (GaussField F),
      A * Matrix.scalar (Fin m) ω = Matrix.scalar (Fin m) ω * A := fun A =>
    (Matrix.scalar_commute ω (fun r => Commute.all ω r) A).eq.symm
  refine oddCoreIn_centralizer_eq_bot_of_blocks hZ g (ι := Unit) (fun _ => Θ.range)
    ?_ ?_ ?_ ?_
  · rintro - x ⟨S, rfl⟩
    rw [hcomm, hΘ, coe_gaussTheta, ← map_mul, ← map_mul, hscal]
  · rintro - b hb x ⟨S, rfl⟩
    have hb1 := (hcomm b).mp hb
    have hb2 := (hcomm b⁻¹).mp (inv_mem hb)
    obtain ⟨A, hA⟩ := exists_gaussIota_of_commute m hb1
    obtain ⟨A', hA'⟩ := exists_gaussIota_of_commute m hb2
    have hAA : A * A' = 1 := by
      apply gaussIota_injective m
      rw [map_mul, hA, hA', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, map_one]
    have hdet : (A * (S : Matrix (Fin m) (Fin m) (GaussField F)) * A').det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, S.2, mul_one, ← Matrix.det_mul, hAA, Matrix.det_one]
    refine ⟨⟨A * (S : Matrix (Fin m) (Fin m) (GaussField F)) * A', hdet⟩, ?_⟩
    apply Subtype.ext
    show gaussIota m (A * (S : Matrix (Fin m) (Fin m) (GaussField F)) * A') =
      ((b * Θ S * b⁻¹ : SpecialLinearGroup (Fin m × Fin 2) F) :
        Matrix (Fin m × Fin 2) (Fin m × Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, map_mul, map_mul,
      hA, hA', hΘ, coe_gaussTheta]
  · rintro -
    set π := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin m × Fin 2) F)) with hπ
    show oddCoreIn (Θ.range.map π) = ⊥
    rw [← MonoidHom.range_comp]
    refine oddCoreIn_range_eq_bot_of_isQuasisimple (π.comp Θ)
      (isQuasisimple_specialLinear_gauss hF hm)
      (isPGroup_center_specialLinear_of_card (k := 3)
        (by rw [card_gaussField_eq_nine hF]; norm_num) (by omega)) ?_
    intro A hA
    rw [MonoidHom.mem_ker] at hA
    have h1 : Θ A ∈ Subgroup.center (SpecialLinearGroup (Fin m × Fin 2) F) :=
      (QuotientGroup.eq_one_iff _).mp hA
    obtain ⟨r, -, hrΘ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
    have h2 : gaussIota m (A : Matrix (Fin m) (Fin m) (GaussField F)) =
        gaussIota m (Matrix.scalar (Fin m) (algebraMap F (GaussField F) r)) := by
      rw [gaussIota_scalar_algebraMap, hrΘ, hΘ, coe_gaussTheta]
    have h3 : (A : Matrix (Fin m) (Fin m) (GaussField F)) =
        Matrix.scalar (Fin m) (algebraMap F (GaussField F) r) := gaussIota_injective m h2
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨algebraMap F (GaussField F) r, ?_,
      h3.symm⟩
    have hdet := A.2
    rw [h3, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
    simpa using hdet
  · rintro ν hν hL
    have hν1 := (hcomm ν).mp hν
    obtain ⟨A, hA⟩ := exists_gaussIota_of_commute m hν1
    have hAS : ∀ S : SpecialLinearGroup (Fin m) (GaussField F),
        (S : Matrix (Fin m) (Fin m) (GaussField F)) * A = A * S := by
      intro S
      apply gaussIota_injective m
      have h := hL () (Θ S) ⟨S, rfl⟩
      have h' := congrArg (fun y : SpecialLinearGroup (Fin m × Fin 2) F =>
        (y : Matrix (Fin m × Fin 2) (Fin m × Fin 2) F)) h
      simp only [Matrix.SpecialLinearGroup.coe_mul, hΘ, coe_gaussTheta, ← hA] at h'
      rw [map_mul, map_mul]
      exact h'.symm
    have hscalar : A ∈ Set.range (Matrix.scalar (Fin m)) :=
      Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => by
        have h := hAS (Matrix.SpecialLinearGroup.transvection t.hij t.c)
        rw [Matrix.SpecialLinearGroup.transvection_coe] at h
        exact h
    obtain ⟨c, hc⟩ := hscalar
    refine ⟨3, ?_⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hν0 : (ν : Matrix (Fin m × Fin 2) (Fin m × Fin 2) F) = 0 := by
        rw [← hA, ← hc, map_zero, map_zero]
      have hdet := ν.2
      have : Nonempty (Fin m × Fin 2) := ⟨(⟨0, by omega⟩, 0)⟩
      rw [hν0, Matrix.det_zero] at hdet
      exact zero_ne_one hdet
    have hc8 : c ^ 8 = 1 := by
      have : Fintype (GaussField F) := Fintype.ofFinite _
      have h1 := FiniteField.pow_card_sub_one_eq_one c hc0
      rw [← Nat.card_eq_fintype_card, card_gaussField_eq_nine hF] at h1
      simpa using h1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hA, ← hc, ← map_pow, ← map_pow, show 2 ^ 3 = 8 from
      rfl, hc8, map_one, map_one, Matrix.SpecialLinearGroup.coe_one]

end Main

section Basis

variable {F : Type} [Field F]

@[expose] noncomputable def basisConj {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (b : Module.Basis J F (Fin n → F)) :
    Matrix (Fin n) (Fin n) F ≃ₐ[F] Matrix J J F :=
  (Matrix.toLinAlgEquiv' (R := F) (n := Fin n)).trans (LinearMap.toMatrixAlgEquiv b)

theorem det_basisConj {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (b : Module.Basis J F (Fin n → F)) (M : Matrix (Fin n) (Fin n) F) :
    (basisConj b M).det = M.det := by
  have h1 : basisConj b M = LinearMap.toMatrix b b (Matrix.toLin' M) := rfl
  rw [h1, LinearMap.det_toMatrix, LinearMap.det_toLin']

@[expose] noncomputable def specialLinearBasisEquiv {n : ℕ} {J : Type} [Fintype J]
    [DecidableEq J] (b : Module.Basis J F (Fin n → F)) :
    SpecialLinearGroup (Fin n) F ≃* SpecialLinearGroup J F where
  toFun x := ⟨basisConj b x, by rw [det_basisConj]; exact x.2⟩
  invFun y := ⟨(basisConj b).symm y, by
    have := det_basisConj b ((basisConj b).symm y)
    rw [AlgEquiv.apply_symm_apply] at this
    rw [← this]
    exact y.2⟩
  left_inv x := Subtype.ext ((basisConj b).symm_apply_apply _)
  right_inv y := Subtype.ext ((basisConj b).apply_symm_apply _)
  map_mul' x y := Subtype.ext (by
    show basisConj b ((x * y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      basisConj b (x : Matrix (Fin n) (Fin n) F) * basisConj b (y : Matrix (Fin n) (Fin n) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, map_mul])

theorem coe_specialLinearBasisEquiv {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (b : Module.Basis J F (Fin n → F)) (x : SpecialLinearGroup (Fin n) F) :
    ((specialLinearBasisEquiv b x : SpecialLinearGroup J F) : Matrix J J F) =
      LinearMap.toMatrix b b (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)) := rfl

end Basis

section Final

variable {F : Type} [Field F] [Finite F]

theorem not_isSquare_neg_one_of_card_eq_three (hF : Nat.card F = 3) : ¬ IsSquare (-1 : F) := by
  have : Fintype F := Fintype.ofFinite F
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hF]
  omega

theorem oddCoreIn_centralizer_eq_bot_of_sq_eq_neg_one (hF : Nat.card F = 3) {n : ℕ} (hn : 3 ≤ n)
    (g : SL(n, F)) (hg2 : (g : Matrix (Fin n) (Fin n) F) * g = -1) :
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk g : SL(n, F) ⧸ Subgroup.center SL(n, F))} :
        Set (SL(n, F) ⧸ Subgroup.center SL(n, F)))) = ⊥ := by
  have hns := not_isSquare_neg_one_of_card_eq_three hF
  have : Fact (¬ IsSquare (-1 : F)) := ⟨hns⟩
  have hnpos : 0 < n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  set f : Module.End F (Fin n → F) :=
    Matrix.toLinAlgEquiv' (R := F) (n := Fin n) (g : Matrix (Fin n) (Fin n) F) with hf_def
  have hff : f * f = (-1 : F) • (1 : Module.End F (Fin n → F)) := by
    rw [hf_def, ← map_mul, hg2, map_neg, map_one]
    exact (neg_one_smul F _).symm
  have hf : ∀ c : F, f ≠ c • (1 : Module.End F (Fin n → F)) := by
    intro c hc
    apply hns
    refine ⟨c, ?_⟩
    have h1 : (g : Matrix (Fin n) (Fin n) F) = c • 1 := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [← hf_def, hc, map_smul, map_one]
    have h2 := congrFun (congrFun hg2 ⟨0, hnpos⟩) ⟨0, hnpos⟩
    rw [h1] at h2
    simp at h2
    linear_combination -h2
  have hd : ∀ l : F, l ^ 2 ≠ -1 := fun l hl => hns ⟨l, by rw [← hl]; ring⟩
  obtain ⟨m, c, hc⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.exists_pair_basis hf hff hd
  set c' : Module.Basis (Fin m × Fin 2) F (Fin n → F) :=
    c.reindex (Equiv.prodComm (Fin 2) (Fin m)) with hc'
  have hc'_apply : ∀ k p, c' (k, p) = c (p, k) := fun k p => by simp [hc']
  have hf0 : ∀ l, f (c' (l, 0)) = c' (l, 1) := fun l => by
    rw [hc'_apply, hc'_apply]
    exact (hc l).symm
  have hf1 : ∀ l, f (c' (l, 1)) = - c' (l, 0) := fun l => by
    rw [← hf0, ← Module.End.mul_apply, hff]
    simp
  have hnm : n = m * 2 := by
    have h1 := Module.finrank_eq_card_basis c'
    rw [Module.finrank_fin_fun] at h1
    simpa using h1
  have hm : 2 ≤ m := by omega
  have hψg : ((specialLinearBasisEquiv c' g : SpecialLinearGroup (Fin m × Fin 2) F) :
      Matrix (Fin m × Fin 2) (Fin m × Fin 2) F) =
      gaussIota m (Matrix.scalar (Fin m) (QuadraticAlgebra.omega : GaussField F)) := by
    rw [coe_specialLinearBasisEquiv]
    ext ⟨k, p⟩ ⟨l, q⟩
    rw [gaussIota_omega_apply, LinearMap.toMatrix_apply]
    have hfg : Matrix.toLin' (g : Matrix (Fin n) (Fin n) F) = f := rfl
    rw [hfg]
    by_cases hkl : k = l
    · subst hkl
      fin_cases p <;> fin_cases q <;> simp [hf0, hf1]
    · fin_cases p <;> fin_cases q <;> simp [hf0, hf1, hkl]
  have hZ : IsPGroup 2 (Subgroup.center (SpecialLinearGroup (Fin m × Fin 2) F)) :=
    (CenterExp.of_mulEquiv (specialLinearBasisEquiv c').symm
      (centerExp_specialLinear_of_pos (k := 1) (by rw [hF]; norm_num) hnpos)).isPGroup
  exact oddCoreIn_centralizer_eq_bot_of_equiv (specialLinearBasisEquiv c') g
    (oddCoreIn_centralizer_eq_bot_of_gaussOmega hF hm hZ _ hψg)

end Final

end CFSG.ClassicalInvolution.Q3
