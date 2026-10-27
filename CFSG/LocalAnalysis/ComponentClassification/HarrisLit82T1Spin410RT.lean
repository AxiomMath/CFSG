module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RI

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {K : Type} [Field K]

section Vectors

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem ι_mul_ι_mul_ι_eq_neg_smul_reflection (a : V) [Invertible (Q a)] (y : V) :
    ι Q a * ι Q y * ι Q a = -(Q a • ι Q (TauCeti.QuadraticMap.reflection Q a y)) := by
  rw [ι_mul_ι_mul_ι, TauCeti.QuadraticMap.reflection_apply, ← map_smul, ← map_neg]
  congr 1
  rw [smul_sub, smul_smul, mul_invOf_cancel_left, neg_sub]

theorem spinAction_ι_mul_ι {a b : V} (h : Q a * Q b = 1) [Invertible (Q a)] [Invertible (Q b)] :
    spinAction Q ⟨ι Q a * ι Q b, ι_mul_ι_mem_spinGroup Q h⟩ =
      TauCeti.QuadraticMap.reflection Q a * TauCeti.QuadraticMap.reflection Q b := by
  set x : spinGroup Q := ⟨ι Q a * ι Q b, ι_mul_ι_mem_spinGroup Q h⟩ with hx
  have h1 : (ι Q b * ι Q a) * (x : CliffordAlgebra Q) = 1 := by
    show ι Q b * ι Q a * (ι Q a * ι Q b) = 1
    rw [mul_assoc, ← mul_assoc (ι Q a), ι_sq_scalar, Algebra.left_comm, ι_sq_scalar, ← map_mul,
      h, map_one]
  have hinv : ((x⁻¹ : spinGroup Q) : CliffordAlgebra Q) = ι Q b * ι Q a := by
    calc ((x⁻¹ : spinGroup Q) : CliffordAlgebra Q) =
        (ι Q b * ι Q a * x) * ↑x⁻¹ := by rw [h1, one_mul]
      _ = ι Q b * ι Q a := by rw [mul_assoc, coe_mul_coe_inv, mul_one]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply]
  refine (spinAction_apply_eq_iff Q x v _).mpr ?_
  rw [hinv]
  show ι Q a * ι Q b * ι Q v * (ι Q b * ι Q a) = _
  calc ι Q a * ι Q b * ι Q v * (ι Q b * ι Q a) = ι Q a * (ι Q b * ι Q v * ι Q b) * ι Q a := by
        simp only [mul_assoc]
    _ = Q b • -(ι Q a * ι Q (TauCeti.QuadraticMap.reflection Q b v) * ι Q a) := by
        rw [ι_mul_ι_mul_ι_eq_neg_smul_reflection]
        simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, smul_neg]
    _ = ι Q (TauCeti.QuadraticMap.reflection Q a (TauCeti.QuadraticMap.reflection Q b v)) := by
        rw [ι_mul_ι_mul_ι_eq_neg_smul_reflection, neg_neg, smul_smul, mul_comm, h, one_smul]

end Vectors

@[expose] noncomputable def tauA₁ (ν : K) : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  (frame01 K).incl !![1, 0; 0, ν]

@[expose] noncomputable def tauA₂ (K : Type) [Field K] : Fin 3 ⊕ Fin 3 ⊕ Unit → K :=
  (frame01 K).incl !![0, -1; 1, 0]

@[expose] noncomputable def tauW₃ (ν : K) : Fin 1 ⊕ Fin 1 ⊕ Unit → K :=
  Pi.single (.inl 0) 1 + Pi.single (.inr (.inl 0)) ν⁻¹

@[expose] noncomputable def tauW₄ (K : Type) [Field K] : Fin 1 ⊕ Fin 1 ⊕ Unit → K :=
  Pi.single (.inr (.inr ())) 1

theorem quadOdd_tauA₁ (ν : K) : quadOdd 3 K (tauA₁ ν) = ν := by
  rw [tauA₁, Frame.Q_incl, Matrix.det_fin_two_of]
  ring

theorem quadOdd_tauA₂ : quadOdd 3 K (tauA₂ K) = 1 := by
  rw [tauA₂, Frame.Q_incl, Matrix.det_fin_two_of]
  ring

theorem quadOdd_tauW₃ (ν : K) : quadOdd 1 K (tauW₃ ν) = ν⁻¹ := by
  simp [tauW₃, quadOdd_apply, Pi.single_apply]

theorem quadOdd_tauW₄ : quadOdd 1 K (tauW₄ K) = 1 := by
  simp [tauW₄, quadOdd_apply]

theorem polar_incl_perpIncl (X : Matrix (Fin 2) (Fin 2) K) (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) :
    polar (quadOdd 3 K) ((frame01 K).incl X) (perpIncl w) = 0 := by
  rw [polar_comm, polar_perpIncl, perpCoords_incl, QuadraticMap.polar_zero_right]

theorem polar_tauA₁_tauA₂ (ν : K) : polar (quadOdd 3 K) (tauA₁ ν) (tauA₂ K) = 0 := by
  rw [tauA₁, tauA₂, Frame.polar_incl_right, Frame.coords_incl]
  simp

theorem polar_tauW₃_tauW₄ (ν : K) : polar (quadOdd 1 K) (tauW₃ ν) (tauW₄ K) = 0 := by
  simp [tauW₃, tauW₄, polar_quadOdd, Pi.single_apply]

section Tau

variable (ν : K) (hν : ν ≠ 0)
include hν

theorem quadOdd_mul_tauA₁₃ :
    quadOdd 3 K (tauA₁ ν) * quadOdd 3 K (perpIncl (tauW₃ ν)) = 1 := by
  rw [quadOdd_tauA₁, quadOdd_perpIncl, quadOdd_tauW₃, mul_inv_cancel₀ hν]

omit hν in
theorem quadOdd_mul_tauA₂₄ :
    quadOdd 3 K (tauA₂ K) * quadOdd 3 K (perpIncl (tauW₄ K)) = 1 := by
  rw [quadOdd_tauA₂, quadOdd_perpIncl, quadOdd_tauW₄, one_mul]

end Tau

@[expose] noncomputable def tauX (ν : K) (hν : ν ≠ 0) : spinGroup (quadOdd 3 K) :=
  ⟨ι _ (tauA₁ ν) * ι _ (perpIncl (tauW₃ ν)), ι_mul_ι_mem_spinGroup _ (quadOdd_mul_tauA₁₃ ν hν)⟩

@[expose] noncomputable def tauY (K : Type) [Field K] : spinGroup (quadOdd 3 K) :=
  ⟨ι _ (tauA₂ K) * ι _ (perpIncl (tauW₄ K)), ι_mul_ι_mem_spinGroup _ quadOdd_mul_tauA₂₄⟩

@[expose] noncomputable def spinTau (ν : K) (hν : ν ≠ 0) : spinGroup (quadOdd 3 K) :=
  tauX ν hν * tauY K

section Tau'

variable (ν : K) (hν : ν ≠ 0)
include hν


omit hν in
theorem ι_mul_ι_mul_self_of_polar {a b : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hab : polar (quadOdd 3 K) a b = 0) :
    ι (quadOdd 3 K) a * ι _ b * (ι _ a * ι _ b) =
      -algebraMap K _ (quadOdd 3 K a * quadOdd 3 K b) := by
  have hba : ι (quadOdd 3 K) b * ι _ a = -(ι _ a * ι _ b) := by
    rw [eq_neg_iff_add_eq_zero, add_comm, ι_mul_ι_add_swap, hab, map_zero]
  calc ι (quadOdd 3 K) a * ι _ b * (ι _ a * ι _ b) = ι _ a * (ι _ b * ι _ a) * ι _ b := by
        simp only [mul_assoc]
    _ = -(ι (quadOdd 3 K) a * ι _ a * (ι _ b * ι _ b)) := by
        rw [hba]
        simp only [mul_neg, neg_mul, mul_assoc]
    _ = _ := by rw [ι_sq_scalar, ι_sq_scalar, ← map_mul]

theorem spinTau_mul_self : spinTau ν hν * spinTau ν hν = 1 := by
  have hx : (tauX ν hν : CliffordAlgebra (quadOdd 3 K)) * tauX ν hν = -1 := by
    show ι _ (tauA₁ ν) * ι _ (perpIncl (tauW₃ ν)) * (ι _ (tauA₁ ν) * ι _ (perpIncl (tauW₃ ν))) =
      -1
    rw [ι_mul_ι_mul_self_of_polar (a := tauA₁ ν) (b := perpIncl (tauW₃ ν))
      (polar_incl_perpIncl _ _), quadOdd_mul_tauA₁₃ ν hν, map_one]
  have hy : (tauY K : CliffordAlgebra (quadOdd 3 K)) * tauY K = -1 := by
    show ι _ (tauA₂ K) * ι _ (perpIncl (tauW₄ K)) * (ι _ (tauA₂ K) * ι _ (perpIncl (tauW₄ K))) =
      -1
    rw [ι_mul_ι_mul_self_of_polar (a := tauA₂ K) (b := perpIncl (tauW₄ K))
      (polar_incl_perpIncl _ _), quadOdd_mul_tauA₂₄, map_one]
  have hxy : Commute (tauX ν hν : CliffordAlgebra (quadOdd 3 K)) (tauY K) :=
    commute_ι_mul_ι _ (polar_tauA₁_tauA₂ ν) (polar_incl_perpIncl _ _)
      (by rw [polar_comm]; exact polar_incl_perpIncl _ _)
      (by rw [polar_perpIncl, perpCoords_perpIncl]; exact polar_tauW₃_tauW₄ ν)
  apply Subtype.ext
  show (tauX ν hν : CliffordAlgebra (quadOdd 3 K)) * tauY K * (tauX ν hν * tauY K) = 1
  calc (tauX ν hν : CliffordAlgebra (quadOdd 3 K)) * tauY K * (tauX ν hν * tauY K) =
      (tauX ν hν * tauX ν hν : CliffordAlgebra (quadOdd 3 K)) * (tauY K * tauY K) := by
        rw [mul_assoc, ← mul_assoc (tauY K : CliffordAlgebra (quadOdd 3 K)), ← hxy.eq]
        simp only [mul_assoc]
    _ = 1 := by rw [hx, hy, neg_one_mul, neg_neg]

omit hν in
theorem La_neg_one_incl (X : Matrix (Fin 2) (Fin 2) K) :
    (frame01 K).La (-1) ((frame01 K).incl X) = -(frame01 K).incl X := by
  rw [Frame.La_apply_incl, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    neg_one_mul, map_neg]

theorem spinTau_mem_centralizer :
    spinTau ν hν ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) := by
  rw [mem_centralizer_singleton_iff]
  have hconj : ∀ g : spinGroup (quadOdd 3 K), (g : CliffordAlgebra (quadOdd 3 K)) =
      tSeven K * g * ↑((tSeven K)⁻¹) → tSeven K * g = g * tSeven K := by
    intro g hg
    apply Subtype.ext
    rw [Submonoid.coe_mul, Submonoid.coe_mul]
    conv_rhs => rw [hg]
    rw [mul_assoc, coe_inv_mul_coe, mul_one]
  have hx : (tSeven K : CliffordAlgebra (quadOdd 3 K)) * tauX ν hν * ↑((tSeven K)⁻¹) =
      -(tauX ν hν : CliffordAlgebra (quadOdd 3 K)) := by
    rw [show (tauX ν hν : CliffordAlgebra (quadOdd 3 K)) =
      ι _ (tauA₁ ν) * ι _ (perpIncl (tauW₃ ν)) from rfl, coe_mul_ι_mul_ι_mul_coe_inv,
      spinAction_tSeven, tauA₁, La_neg_one_incl, La_neg_one_perpIncl, map_neg, neg_mul]
  have hy : (tSeven K : CliffordAlgebra (quadOdd 3 K)) * tauY K * ↑((tSeven K)⁻¹) =
      -(tauY K : CliffordAlgebra (quadOdd 3 K)) := by
    rw [show (tauY K : CliffordAlgebra (quadOdd 3 K)) =
      ι _ (tauA₂ K) * ι _ (perpIncl (tauW₄ K)) from rfl, coe_mul_ι_mul_ι_mul_coe_inv,
      spinAction_tSeven, tauA₂, La_neg_one_incl, La_neg_one_perpIncl, map_neg, neg_mul]
  have key : (tSeven K : CliffordAlgebra (quadOdd 3 K)) * spinTau ν hν * ↑((tSeven K)⁻¹) =
      spinTau ν hν := by
    show (tSeven K : CliffordAlgebra (quadOdd 3 K)) * (tauX ν hν * tauY K) * ↑((tSeven K)⁻¹) =
      tauX ν hν * tauY K
    calc (tSeven K : CliffordAlgebra (quadOdd 3 K)) * (tauX ν hν * tauY K) * ↑((tSeven K)⁻¹) =
        ((tSeven K : CliffordAlgebra (quadOdd 3 K)) * tauX ν hν * ↑((tSeven K)⁻¹)) *
          (tSeven K * tauY K * ↑((tSeven K)⁻¹)) := by
          simp only [mul_assoc, coe_inv_mul_coe_mul]
      _ = tauX ν hν * tauY K := by rw [hx, hy, neg_mul_neg]
  exact (hconj _ key.symm).symm

omit hν in
theorem reflection_perpIncl_apply (u w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) [Invertible (quadOdd 1 K u)]
    [Invertible (quadOdd 3 K (perpIncl u))] :
    TauCeti.QuadraticMap.reflection (quadOdd 3 K) (perpIncl u) (perpIncl w) =
      perpIncl (TauCeti.QuadraticMap.reflection (quadOdd 1 K) u w) := by
  rw [← perpEmb_reflection, perpEmb_apply, perpEmbLin_apply, perpCoords_perpIncl,
    LinearEquiv.coe_coe, map_sub]
  abel

omit hν in
theorem reflection_incl_perpIncl (X : Matrix (Fin 2) (Fin 2) K)
    [Invertible (quadOdd 3 K ((frame01 K).incl X))] (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) :
    TauCeti.QuadraticMap.reflection (quadOdd 3 K) ((frame01 K).incl X) (perpIncl w) =
      perpIncl w :=
  TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero _ _ (polar_incl_perpIncl X w)

theorem perpTransport_spinTau [Invertible (quadOdd 1 K (tauW₃ ν))]
    [Invertible (quadOdd 1 K (tauW₄ K))] (w : Fin 1 ⊕ Fin 1 ⊕ Unit → K) :
    perpCoords (spinAction (quadOdd 3 K) (spinTau ν hν) (perpIncl w)) =
      TauCeti.QuadraticMap.reflection (quadOdd 1 K) (tauW₃ ν)
        (TauCeti.QuadraticMap.reflection (quadOdd 1 K) (tauW₄ K) w) := by
  let _ : Invertible (quadOdd 3 K (tauA₁ ν)) :=
    invertibleOfNonzero (by rw [quadOdd_tauA₁]; exact hν)
  let _ : Invertible (quadOdd 3 K (tauA₂ K)) :=
    invertibleOfNonzero (by rw [quadOdd_tauA₂]; exact one_ne_zero)
  let _ : Invertible (quadOdd 3 K (perpIncl (tauW₃ ν))) :=
    invertibleOfNonzero (by rw [quadOdd_perpIncl, quadOdd_tauW₃]; exact inv_ne_zero hν)
  let _ : Invertible (quadOdd 3 K (perpIncl (tauW₄ K))) :=
    invertibleOfNonzero (by rw [quadOdd_perpIncl, quadOdd_tauW₄]; exact one_ne_zero)
  have hx : spinAction (quadOdd 3 K) (tauX ν hν) =
      TauCeti.QuadraticMap.reflection (quadOdd 3 K) (tauA₁ ν) *
        TauCeti.QuadraticMap.reflection (quadOdd 3 K) (perpIncl (tauW₃ ν)) :=
    spinAction_ι_mul_ι (quadOdd_mul_tauA₁₃ ν hν)
  have hy : spinAction (quadOdd 3 K) (tauY K) =
      TauCeti.QuadraticMap.reflection (quadOdd 3 K) (tauA₂ K) *
        TauCeti.QuadraticMap.reflection (quadOdd 3 K) (perpIncl (tauW₄ K)) :=
    spinAction_ι_mul_ι quadOdd_mul_tauA₂₄
  rw [spinTau, map_mul, hx, hy, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, reflection_perpIncl_apply]
  rw [TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero _ (tauA₂ K)
      (polar_incl_perpIncl _ _), reflection_perpIncl_apply,
    TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero _ (tauA₁ ν)
      (polar_incl_perpIncl _ _), perpCoords_perpIncl]

end Tau'

theorem le_ker_of_commutator_eq_self {G A : Type*} [Group G] [CommGroup A] (φ : G →* A)
    {P : Subgroup G} (hP : ⁅P, P⁆ = P) : P ≤ φ.ker := by
  rw [← hP, commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem commutator_subgroupOf_eq_self {G : Type*} [Group G] {H C : Subgroup G} (hHC : H ≤ C)
    (hH : Group.IsPerfect ↥H) : ⁅H.subgroupOf C, H.subgroupOf C⁆ = H.subgroupOf C := by
  have : Group.IsPerfect ↥H := hH
  have : Group.IsPerfect ↥(H.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hHC).symm.toMonoidHom)
      (subgroupOfEquivOfLe hHC).symm.surjective
  exact Subgroup.isPerfect_iff.mp this


variable (K) in
@[expose] noncomputable def spinNormC [Invertible (2 : K)] :
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) →*
      Multiplicative (TauCeti.SquareClassGroup K) :=
  (CliffordAlgebra.orthogonalSpinorNorm (quadOdd 1 K) (nondegenerate_quadOdd 1 K)).comp
    ((perpHom (isUnit_of_invertible (2 : K)).ne_zero).comp (spinCent K))

theorem spinNormC_spinTau_ne_one [Invertible (2 : K)] (ν : K) (hν : ν ≠ 0) (hνs : ¬ IsSquare ν)
    (hτ : spinTau ν hν ∈ centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) :
    spinNormC K ⟨spinTau ν hν, hτ⟩ ≠ 1 := by
  let _ : Invertible (quadOdd 1 K (tauW₃ ν)) :=
    invertibleOfNonzero (by rw [quadOdd_tauW₃]; exact inv_ne_zero hν)
  let _ : Invertible (quadOdd 1 K (tauW₄ K)) :=
    invertibleOfNonzero (by rw [quadOdd_tauW₄]; exact one_ne_zero)
  have hP : perpHom (isUnit_of_invertible (2 : K)).ne_zero (spinCent K ⟨spinTau ν hν, hτ⟩) =
      TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 1 K) (tauW₃ ν) *
        TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 1 K) (tauW₄ K) := by
    apply Subtype.ext
    refine LinearEquiv.ext fun w => ?_
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.coe_reflectionOrthogonal]
    exact perpTransport_spinTau ν hν w
  show CliffordAlgebra.orthogonalSpinorNorm (quadOdd 1 K) (nondegenerate_quadOdd 1 K)
    (perpHom (isUnit_of_invertible (2 : K)).ne_zero (spinCent K ⟨spinTau ν hν, hτ⟩)) ≠ 1
  rw [hP, map_mul, CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal,
    CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal]
  have hu₄ : unitOfInvertible (quadOdd 1 K (tauW₄ K)) = 1 :=
    Units.ext (by rw [val_unitOfInvertible, quadOdd_tauW₄, Units.val_one])
  rw [← map_mul, hu₄, mul_one, TauCeti.squareClassHom_apply]
  intro h
  have h' : TauCeti.squareClass (unitOfInvertible (quadOdd 1 K (tauW₃ ν))) = 0 := by
    simpa using congrArg Multiplicative.toAdd h
  rw [TauCeti.squareClass_eq_zero_iff] at h'
  apply hνs
  have h'' := h'.map (Units.coeHom K)
  rw [Units.coeHom_apply, val_unitOfInvertible, quadOdd_tauW₃] at h''
  obtain ⟨s, hs⟩ := h''
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact inv_ne_zero hν hs
  exact ⟨s⁻¹, by rw [← mul_inv, ← hs, inv_inv]⟩

section Index

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
  (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

theorem spinE_le_ker_spinNormC [Invertible (2 : K)] :
    (spinE K).subgroupOf (centralizer {tSeven K}) ≤ (spinNormC K).ker := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨s1, s2, s3⟩ := isSLTwoOver_spinJ (K := K) hK
  have hp1 := le_ker_of_commutator_eq_self (A := Multiplicative (TauCeti.SquareClassGroup K))
    (spinNormC K)
    (commutator_subgroupOf_eq_self l1 (sl2_facts_spin hp hp2 h5 s1).1.1)
  have hp2' := le_ker_of_commutator_eq_self (A := Multiplicative (TauCeti.SquareClassGroup K))
    (spinNormC K)
    (commutator_subgroupOf_eq_self l2 (sl2_facts_spin hp hp2 h5 s2).1.1)
  have hp3 := le_ker_of_commutator_eq_self (A := Multiplicative (TauCeti.SquareClassGroup K))
    (spinNormC K)
    (commutator_subgroupOf_eq_self l3 (sl2_facts_spin hp hp2 h5 s3).1.1)
  rw [subgroupOf_sup (sup_le l1 l2) l3, subgroupOf_sup l1 l2]
  exact sup_le (sup_le hp1 hp2') hp3

omit h5 in
theorem exists_nonsquare_spin : ∃ ν : K, ν ≠ 0 ∧ ¬ IsSquare ν := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have hring : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := (ringChar.spec K 2).2 (by rw [h])
    exact_mod_cast this
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hring
  exact ⟨ν, fun h => hν (by rw [h]; exact ⟨0, by simp⟩), hν⟩

theorem index_spinE_eq_two :
    ((spinE K).subgroupOf (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))).index =
      2 := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have := finite_spinSeven h2
  obtain ⟨ν, hν0, hνs⟩ := exists_nonsquare_spin hp hp2 hK
  have hτC := spinTau_mem_centralizer ν hν0
  have hτ : (⟨spinTau ν hν0, hτC⟩ : centralizer {tSeven K}) ∉
      (spinE K).subgroupOf (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) :=
    fun h => spinNormC_spinTau_ne_one ν hν0 hνs hτC (spinE_le_ker_spinNormC hp hp2 hK h5 h)
  have hC := card_centralizer_tSeven_le hp hp2 hK h5
  have hE := card_spinE hp hp2 hK h5
  have hEC := card_mul_index ((spinE K).subgroupOf
    (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))))
  rw [Nat.card_congr (subgroupOfEquivOfLe (spinE_le_centralizer hp hp2 hK)).toEquiv] at hEC
  have hpos : 0 < Nat.card (spinE K) := Nat.card_pos
  rw [mul_pow] at hE
  have hle : ((spinE K).subgroupOf
      (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))).index ≤ 2 := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [hEC]
    omega
  have hne1 : ((spinE K).subgroupOf
      (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))).index ≠ 1 := fun h =>
    hτ (by rw [index_eq_one.mp h]; exact mem_top _)
  have hne0 : ((spinE K).subgroupOf
      (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))).index ≠ 0 :=
    index_ne_zero_of_finite
  omega

theorem card_centralizer_tSeven :
    Nat.card (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) =
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 3 := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hE := card_spinE hp hp2 hK h5
  have hEC := card_mul_index ((spinE K).subgroupOf
    (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))))
  rw [Nat.card_congr (subgroupOfEquivOfLe (spinE_le_centralizer hp hp2 hK)).toEquiv,
    index_spinE_eq_two hp hp2 hK h5] at hEC
  rw [← hEC, ← mul_pow, ← hE, mul_comm]

theorem ker_spinNormC [Invertible (2 : K)] :
    (spinNormC K).ker = (spinE K).subgroupOf (centralizer {tSeven K}) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  obtain ⟨ν, hν0, hνs⟩ := exists_nonsquare_spin hp hp2 hK
  have hτC := spinTau_mem_centralizer ν hν0
  have hle := spinE_le_ker_spinNormC hp hp2 hK h5
  have hidx := index_spinE_eq_two hp hp2 hK h5
  have hne : (spinNormC K).ker ≠ ⊤ := fun h =>
    spinNormC_spinTau_ne_one ν hν0 hνs hτC (by rw [← MonoidHom.mem_ker, h]; exact mem_top _)
  have hdvd := index_dvd_of_le hle
  rw [hidx] at hdvd
  have hk2 : (spinNormC K).ker.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (index_eq_one.mp h) hne
    · exact h
  refine (eq_of_le_of_card_ge hle ?_).symm
  have e1 := card_mul_index (spinNormC K).ker
  have e2 := card_mul_index ((spinE K).subgroupOf (centralizer ({tSeven K} :
    Set (spinGroup (quadOdd 3 K)))))
  rw [hk2] at e1
  rw [hidx] at e2
  omega

end Index

end CFSG.ComponentClassification.HarrisLit.T1
