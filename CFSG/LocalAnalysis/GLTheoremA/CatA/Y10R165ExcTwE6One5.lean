module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni5
public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.ClassicalEA
public import CFSG.ClassicalGroups.UnitaryFlag.PointSylow
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open Matrix CFSG CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA
open CFSG.Blueprint.Chevalley CFSG.LinearGroups CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LieType.Chevalley

variable {f p : ℕ} {K : Type} [Field K] [Finite K]

noncomputable abbrev C6 (K : Type) [Field K] : Matrix (Fin 6) (Fin 6) K :=
  ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)

abbrev e0 (K : Type) [Field K] : Fin 6 → K := Pi.single 0 1

abbrev e5 (K : Type) [Field K] : Fin 6 → K := Pi.single 5 1

abbrev U2 (K : Type) [Field K] : Submodule K (Fin 6 → K) :=
  Submodule.span K {e0 K, e5 K}

noncomputable abbrev B6 (h : UnitaryFieldData 2 f K) :
    (Fin 6 → K) →ₛₗ[h.bar] (Fin 6 → K) →ₗ[K] K :=
  gramForm h (C6 K)

theorem B6_isSymm (h : UnitaryFieldData 2 f K) : (B6 h).IsSymm := by
  refine gramForm_isSymm h ?_
  change ((CFSG.LieType.Chevalley.E6GraphLevi.antiId K).map h.bar)ᵀ =
    CFSG.LieType.Chevalley.E6GraphLevi.antiId K
  have hmap : (CFSG.LieType.Chevalley.E6GraphLevi.antiId K).map h.bar =
      CFSG.LieType.Chevalley.E6GraphLevi.antiId K := by
    ext i j
    simp [Matrix.map_apply, CFSG.LieType.Chevalley.E6GraphLevi.antiId]
  rw [hmap]
  exact CFSG.LieType.Chevalley.E6GraphLevi.antiId_transpose (K := K)

theorem B6_separatingLeft (h : UnitaryFieldData 2 f K) : (B6 h).SeparatingLeft :=
  gramForm_separatingLeft h (det_antiIdGL_ne_zero (K := K))

theorem e0_ne_zero (K : Type) [Field K] : e0 K ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [e0] at this

theorem B6_e0_e0 (h : UnitaryFieldData 2 f K) : B6 h (e0 K) (e0 K) = 0 := by
  simp [B6, gramForm_apply, C6, CFSG.SeitzReduction.TwistedE6Pilot.coe_antiIdGL,
    CFSG.LieType.Chevalley.E6GraphLevi.antiId, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_six]

theorem B6_e0_e5 (h : UnitaryFieldData 2 f K) : B6 h (e0 K) (e5 K) = 1 := by
  simp [B6, gramForm_apply, C6, CFSG.SeitzReduction.TwistedE6Pilot.coe_antiIdGL,
    CFSG.LieType.Chevalley.E6GraphLevi.antiId, e0, e5, Matrix.mulVec, dotProduct,
    Fin.sum_univ_six]

theorem B6_e5_e5 (h : UnitaryFieldData 2 f K) : B6 h (e5 K) (e5 K) = 0 := by
  simp [B6, gramForm_apply, C6, CFSG.SeitzReduction.TwistedE6Pilot.coe_antiIdGL,
    CFSG.LieType.Chevalley.E6GraphLevi.antiId, e5, Matrix.mulVec, dotProduct, Fin.sum_univ_six]

theorem hyperbolic_splitting_U2 (h : UnitaryFieldData 2 f K) :
    Module.finrank K (U2 K) = 2 ∧
      ((B6 h).domRestrict₁₂ (U2 K) (U2 K)).SeparatingLeft ∧
      IsCompl (U2 K) (Submodule.orthogonalBilin (B6 h) (U2 K)) ∧
      ((B6 h).domRestrict₁₂ (Submodule.orthogonalBilin (B6 h) (U2 K))
        (Submodule.orthogonalBilin (B6 h) (U2 K))).SeparatingLeft ∧
      Module.finrank K (Submodule.orthogonalBilin (B6 h) (U2 K)) = 4 := by
  have h := (CFSG.LinearGroups.hermitian_hyperbolic_splitting h (B6_isSymm h) (B6_separatingLeft h)
    (e0_ne_zero K) (B6_e0_e0 h)).2 (e5 K) (B6_e0_e5 h) (B6_e5_e5 h)
  obtain ⟨hfin, hsep, hcompl, hsepW, hfr⟩ := h
  refine ⟨hfin, hsep, hcompl, hsepW, ?_⟩
  have hV : Module.finrank K (Fin 6 → K) = 6 := Module.finrank_fin_fun (R := K) (n := 6)
  rw [hfr, hV]

theorem isQuasisimple_pointwiseStab_U2 (h : UnitaryFieldData 2 f K) :
    IsQuasisimple ↥(pointwiseStab (sesqSpecialUnitaryGroupLE (B6 h)) (U2 K)) := by
  obtain ⟨-, -, hcompl, hsepW, hfr⟩ := hyperbolic_splitting_U2 h
  have hdim : 3 ≤ Module.finrank K (Submodule.orthogonalBilin (B6 h) (U2 K)) := by
    rw [hfr]; norm_num
  have hnq : (Module.finrank K (Submodule.orthogonalBilin (B6 h) (U2 K)), 2 ^ f) ≠ (3, 2) := by
    rw [hfr]; norm_num
  have hSU : IsQuasisimple ↥(sesqSpecialUnitaryGroup
      ((B6 h).domRestrict₁₂ (Submodule.orthogonalBilin (B6 h) (U2 K))
        (Submodule.orthogonalBilin (B6 h) (U2 K)))) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_sesqSpecialUnitaryGroup_of_three_le
      h ((B6_isSymm h).domRestrict _) hsepW hdim hnq
  obtain ⟨e2⟩ := sesqSpecialUnitaryGroupLE_mulEquiv (B := (B6 h).domRestrict₁₂
    (Submodule.orthogonalBilin (B6 h) (U2 K))
    (Submodule.orthogonalBilin (B6 h) (U2 K)))
  have hLE : IsQuasisimple ↥(sesqSpecialUnitaryGroupLE ((B6 h).domRestrict₁₂
      (Submodule.orthogonalBilin (B6 h) (U2 K))
      (Submodule.orthogonalBilin (B6 h) (U2 K)))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e2.symm hSU
  obtain ⟨e⟩ := pointwiseStab_sesqSpecialUnitaryGroup_mulEquiv (B := B6 h) (U := U2 K)
    (B6_isSymm h).isRefl hcompl
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hLE

@[expose] noncomputable def toLinLE (K : Type) [Field K] :
    GL (Fin 6) K →* ((Fin 6 → K) ≃ₗ[K] (Fin 6 → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 6 → K)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin).toMonoidHom

theorem toLinLE_apply (g : GL (Fin 6) K) (v : Fin 6 → K) :
    toLinLE K g v = (g : Matrix (Fin 6) (Fin 6) K) *ᵥ v := by
  simp [toLinLE, Matrix.GeneralLinearGroup.toLin_apply]

theorem toLinLE_toLinearMap (g : GL (Fin 6) K) :
    (toLinLE K g : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) K) := by
  apply LinearMap.ext
  intro v
  change toLinLE K g v = Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) K) v
  rw [toLinLE_apply, Matrix.toLin'_apply]

theorem toLinLE_injective (K : Type) [Field K] : Function.Injective (toLinLE K) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 6 → K)).injective.comp
    (Matrix.GeneralLinearGroup.toLin).injective

theorem mem_toLinLE_gramSU (h : UnitaryFieldData 2 f K) (g : GL (Fin 6) K) :
    toLinLE K g ∈ sesqSpecialUnitaryGroupLE (B6 h) ↔ g ∈ gramSU h (C6 K) := by
  rw [mem_sesqSpecialUnitaryGroupLE, mem_gramSU_iff_isometry]
  constructor
  · rintro ⟨hiso, hdet⟩
    refine ⟨fun x y => ?_, ?_⟩
    · simpa only [toLinLE_apply] using hiso x y
    · rw [← LinearMap.det_toLin' (f := (g : Matrix (Fin 6) (Fin 6) K)),
        ← toLinLE_toLinearMap, hdet]
  · rintro ⟨hiso, hdet⟩
    refine ⟨fun x y => ?_, ?_⟩
    · simpa only [toLinLE_apply] using hiso x y
    · rw [toLinLE_toLinearMap, LinearMap.det_toLin', hdet]

@[expose] noncomputable def QSU (h : UnitaryFieldData 2 f K) : Subgroup ↥(gramSU h (C6 K)) where
  carrier := {x | ∀ v ∈ U2 K, toLinLE K (x : GL (Fin 6) K) v = v}
  mul_mem' {x y} hx hy := by
    intro v hv
    rw [Subgroup.coe_mul, map_mul]
    change toLinLE K (x : GL (Fin 6) K) (toLinLE K (y : GL (Fin 6) K) v) = v
    rw [hy v hv]
    exact hx v hv
  one_mem' := by
    intro v _
    rw [Subgroup.coe_one, map_one]
    rfl
  inv_mem' {x} hx := by
    intro v hv
    rw [Subgroup.coe_inv, map_inv]
    have h := hx v hv
    conv_lhs => rw [← h]
    simp

noncomputable def QSUEquiv (h : UnitaryFieldData 2 f K) :
    ↥(QSU h) ≃* ↥(pointwiseStab (sesqSpecialUnitaryGroupLE (B6 h)) (U2 K)) := by
  let H := sesqSpecialUnitaryGroupLE (B6 h)
  let f : ↥(QSU h) →* ↥(pointwiseStab H (U2 K)) :=
    { toFun := fun x =>
        ⟨⟨toLinLE K (x : GL (Fin 6) K),
            (mem_toLinLE_gramSU h _).mpr
              (x : ↥(gramSU h (C6 K))).2⟩,
          (mem_pointwiseStab).mpr (fun v hv => x.2 v hv)⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' x y := by
        apply Subtype.ext
        apply Subtype.ext
        simp }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply toLinLE_injective K
    exact congrArg (fun z : ↥(pointwiseStab H (U2 K)) => ((z : ↥H) :
      (Fin 6 → K) ≃ₗ[K] (Fin 6 → K))) hxy
  · intro y
    let g : GL (Fin 6) K := (Matrix.GeneralLinearGroup.toLin).symm
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 6 → K)).symm (y : ↥H))
    have hg : toLinLE K g = (y : ↥H) := by
      simp only [toLinLE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply, g]
    have hfix : ∀ v ∈ U2 K, toLinLE K g v = v := by
      intro v hv
      rw [hg]
      exact (mem_pointwiseStab.mp y.2) v hv
    have hgram : g ∈ gramSU h (C6 K) :=
      (mem_toLinLE_gramSU h g).mp (by rw [hg]; exact (y : ↥H).2)
    refine ⟨⟨⟨g, hgram⟩, hfix⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hg

theorem isQuasisimple_QSU (h : UnitaryFieldData 2 f K) : IsQuasisimple ↥(QSU h) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (QSUEquiv h).symm
    (isQuasisimple_pointwiseStab_U2 h)

theorem e0_mem_U2 (K : Type) [Field K] : e0 K ∈ U2 K :=
  Submodule.subset_span (by simp)

theorem e5_mem_U2 (K : Type) [Field K] : e5 K ∈ U2 K :=
  Submodule.subset_span (by simp)

theorem diag3_one_fixes_U2 (h : UnitaryFieldData 2 f K) (ζ : Kˣ)
    (hζbar : h.bar (ζ : K) = ζ) :
    ∀ v ∈ U2 K, toLinLE K (diag3 1 ζ 1) v = v := by
  intro v hv
  obtain ⟨a, b, rfl⟩ := (Submodule.mem_span_pair).mp hv
  have h0 : toLinLE K (diag3 1 ζ 1) (e0 K) = e0 K := by
    rw [toLinLE_apply]
    ext i
    fin_cases i <;> simp [diag3, coe_diag3, e0, Matrix.mulVec, Matrix.diagonal, Units.smul_def,
        smul_eq_mul, mul_one]
  have h5 : toLinLE K (diag3 1 ζ 1) (e5 K) = e5 K := by
    rw [toLinLE_apply]
    ext i
    fin_cases i <;> simp [diag3, coe_diag3, e5, Matrix.mulVec, Matrix.diagonal, Units.smul_def,
        smul_eq_mul, mul_one]
  rw [map_add, map_smul, map_smul, h0, h5]

noncomputable def zQSU (h : UnitaryFieldData 2 f K) (ζ : Kˣ)
    (hζbar : h.bar (ζ : K) = ζ) : ↥(QSU h) :=
  ⟨⟨diag3 1 ζ 1,
      diag3_mem_gramSU h 1 ζ 1 (by simp) hζbar (by simp)⟩,
    diag3_one_fixes_U2 h ζ hζbar⟩

private theorem diag3_pow (a b c : Kˣ) (n : ℕ) :
    diag3 a b c ^ n = diag3 (a ^ n) (b ^ n) (c ^ n) := by
  induction n with
  | zero => simp [diag3_one]
  | succ n ih =>
    rw [pow_succ, ih, diag3_mul, pow_succ, pow_succ, pow_succ]

theorem orderOf_zQSU (h : UnitaryFieldData 2 f K) (p : ℕ) (hp : p.Prime) (ζ : Kˣ)
    (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    orderOf (zQSU h ζ hζbar) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← Subgroup.orderOf_coe (zQSU h ζ hζbar)]
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change ((diag3 1 ζ 1 ^ p : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j =
      (1 : GL (Fin 6) K) i j
    rw [diag3_pow]
    have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    rw [hζp, one_pow, diag3_one]
  · intro h1
    have h11 := congrArg (fun g : ↥(gramSU h (C6 K)) =>
      (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 1 1) h1
    simp [zQSU, diag3, coe_diag3] at h11
    have h1' : orderOf ζ = 1 := orderOf_eq_one_iff.mpr h11
    rw [hζ] at h1'
    exact hp.ne_one h1'

noncomputable abbrev Qbar (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    Subgroup (primeFormP h (C6 K)) :=
  ((QuotientGroup.mk' (N6 h)).comp (QSU h).subtype).range

theorem quotient_QSU_injective (h : UnitaryFieldData 2 f K) :
    Function.Injective ((QuotientGroup.mk' (N6 h)).comp (QSU h).subtype) := by
  intro x y hxy
  simp only [MonoidHom.comp_apply] at hxy
  have h1 : (QuotientGroup.mk' (N6 h)) ((QSU h).subtype (x / y)) = 1 := by
    have hsub : (QSU h).subtype (x / y) = (QSU h).subtype x / (QSU h).subtype y :=
      map_div _ _ _
    rw [hsub, map_div (f := QuotientGroup.mk' (N6 h)), hxy]
    exact div_eq_one.mpr rfl
  have hmem : ((x / y : ↥(QSU h)) : ↥(gramSU h (C6 K))) ∈ N6 h :=
    (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨cc, hc, hcn, hg⟩ := (mem_normOneScalars).mp hmem
  have hfix := (x / y).2 (e0 K) (e0_mem_U2 K)
  rw [toLinLE_apply] at hfix
  have hmat : (((x / y : ↥(QSU h)) : ↥(gramSU h (C6 K))) : GL (Fin 6) K) =
      GeneralLinearGroup.scalar (Fin 6) cc := hg
  rw [hmat] at hfix
  have hc1 : cc = 1 := by
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, e0] using hfix
  have hxy1 : x / y = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hmat, hc1]
    simp
  calc x = (x / y) * y := (div_mul_cancel x y).symm
    _ = 1 * y := by rw [hxy1]
    _ = y := one_mul y

theorem isQuasisimple_Qbar (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    IsQuasisimple ↥(Qbar h p hp hp2 ζ hζ hζbar) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (quotient_QSU_injective h)) (isQuasisimple_QSU h)

theorem dvd_card_Qbar (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    p ∣ Nat.card (Qbar h p hp hp2 ζ hζ hζbar) := by
  haveI : Fintype ↥(Qbar h p hp hp2 ζ hζ hζbar) := Fintype.ofFinite _
  let x : ↥(Qbar h p hp hp2 ζ hζ hζbar) :=
    ⟨((QuotientGroup.mk' (N6 h)).comp (QSU h).subtype) (zQSU h ζ hζbar),
      ⟨zQSU h ζ hζbar, rfl⟩⟩
  have hx : orderOf x = p := by
    rw [← Subgroup.orderOf_coe x]
    change orderOf (((QuotientGroup.mk' (N6 h)).comp (QSU h).subtype)
      (zQSU h ζ hζbar)) = p
    rw [orderOf_injective ((QuotientGroup.mk' (N6 h)).comp (QSU h).subtype)
      (quotient_QSU_injective h) (zQSU h ζ hζbar)]
    exact orderOf_zQSU h p hp ζ hζ hζbar
  have hdvd := orderOf_dvd_card (x := x)
  rw [hx] at hdvd
  rwa [Nat.card_eq_fintype_card]

@[expose] noncomputable def zSU (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (ζ : Kˣ)
    (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) : ↥(gramSU h (C6 K)) :=
  ⟨r3Hom h p ζ hζ hζbar (Multiplicative.ofAdd ((1, 0, 0) : ZMod p × ZMod p × ZMod p)),
    (r3Hom h p ζ hζ hζbar _).2⟩

theorem zbar_eq_mk_zSU (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (ζ : Kˣ)
    (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    zbar h p ζ hζ hζbar = (QuotientGroup.mk' (N6 h)) (zSU h p ζ hζ hζbar) := rfl

theorem zSU_eq_diag3 (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    ((zSU h p ζ hζ hζbar : ↥(gramSU h (C6 K))) : GL (Fin 6) K) = diag3 ζ 1 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [zSU, r3Hom, diag3, coe_diag3, ZMod.val_zero, ZMod.val_one]

theorem mem_orthogonal_U2_coords (h : UnitaryFieldData 2 f K) {w : Fin 6 → K}
    (hw : w ∈ Submodule.orthogonalBilin (B6 h) (U2 K)) : w 0 = 0 ∧ w 5 = 0 := by
  have hbar_inj : Function.Injective h.bar := by
    intro a b hab
    have := congrArg h.bar hab
    rwa [h.bar_bar, h.bar_bar] at this
  have h0 : h.bar (w 5) = 0 := by
    have h := hw (e0 K) (e0_mem_U2 K)
    simpa [B6, gramForm_apply, C6, CFSG.SeitzReduction.TwistedE6Pilot.coe_antiIdGL,
      CFSG.LieType.Chevalley.E6GraphLevi.antiId, e0, Matrix.mulVec, dotProduct,
      Fin.sum_univ_six] using h
  have h5 : h.bar (w 0) = 0 := by
    have h := hw (e5 K) (e5_mem_U2 K)
    simpa [B6, gramForm_apply, C6, CFSG.SeitzReduction.TwistedE6Pilot.coe_antiIdGL,
      CFSG.LieType.Chevalley.E6GraphLevi.antiId, e5, Matrix.mulVec, dotProduct,
      Fin.sum_univ_six] using h
  exact ⟨hbar_inj (by rw [h5, map_zero]), hbar_inj (by rw [h0, map_zero])⟩

theorem zSU_fixes_orthogonal (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) {w : Fin 6 → K}
    (hw : w ∈ Submodule.orthogonalBilin (B6 h) (U2 K)) :
    toLinLE K (zSU h p ζ hζ hζbar : GL (Fin 6) K) w = w := by
  obtain ⟨h0, h5⟩ := mem_orthogonal_U2_coords h hw
  rw [zSU_eq_diag3 h p hp ζ hζ hζbar, toLinLE_apply]
  ext i
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal, Fin.sum_univ_six]
  all_goals simp [h0, h5]

theorem zSU_maps_U2 (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) {u : Fin 6 → K}
    (hu : u ∈ U2 K) :
    toLinLE K (zSU h p ζ hζ hζbar : GL (Fin 6) K) u ∈ U2 K := by
  obtain ⟨a, b, rfl⟩ := (Submodule.mem_span_pair).mp hu
  rw [zSU_eq_diag3 h p hp ζ hζ hζbar, toLinLE_apply]
  change ((diag3 ζ 1 1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ
    (a • e0 K + b • e5 K) ∈ U2 K
  have hz0 : ((diag3 ζ 1 1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ e0 K =
      ζ • e0 K := by
    ext i
    fin_cases i <;> simp [diag3, coe_diag3, e0, Matrix.mulVec, Matrix.diagonal, Units.smul_def,
        smul_eq_mul, mul_one]
  have hz5 : ((diag3 ζ 1 1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ e5 K =
      ζ⁻¹ • e5 K := by
    ext i
    fin_cases i <;> simp [diag3, coe_diag3, e5, Matrix.mulVec, Matrix.diagonal, Units.smul_def,
        smul_eq_mul, mul_one]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hz0, hz5]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem QSU_maps_orthogonal (h : UnitaryFieldData 2 f K) (x : ↥(QSU h))
    {w : Fin 6 → K} (hw : w ∈ Submodule.orthogonalBilin (B6 h) (U2 K)) :
    toLinLE K (x : GL (Fin 6) K) w ∈ Submodule.orthogonalBilin (B6 h) (U2 K) := by
  have hxH : toLinLE K (x : GL (Fin 6) K) ∈ sesqSpecialUnitaryGroupLE (B6 h) :=
    (mem_toLinLE_gramSU h _).mpr (x : ↥(gramSU h (C6 K))).2
  have hxI := (mem_sesqSpecialUnitaryGroupLE.mp hxH).1
  rw [Submodule.mem_orthogonalBilin] at hw ⊢
  intro u hu
  calc B6 h u (toLinLE K (x : GL (Fin 6) K) w) =
        B6 h (toLinLE K (x : GL (Fin 6) K) u) (toLinLE K (x : GL (Fin 6) K) w) := by
          rw [x.2 u hu]
    _ = B6 h u w := hxI u w
    _ = 0 := hw u hu

theorem QSU_commute_zSU (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) (x : ↥(QSU h)) :
    (x : ↥(gramSU h (C6 K))) * zSU h p ζ hζ hζbar =
      zSU h p ζ hζ hζbar * x := by
  obtain ⟨-, -, hcompl, -, -⟩ := hyperbolic_splitting_U2 h
  have hlin : toLinLE K ((x : ↥(gramSU h (C6 K))) : GL (Fin 6) K) *
      toLinLE K (zSU h p ζ hζ hζbar : GL (Fin 6) K) =
      toLinLE K (zSU h p ζ hζ hζbar : GL (Fin 6) K) *
        toLinLE K ((x : ↥(gramSU h (C6 K))) : GL (Fin 6) K) := by
    refine linearEquiv_ext_of_isCompl hcompl (fun u hu => ?_) (fun w hw => ?_)
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      rw [x.2 (toLinLE K (zSU h p ζ hζ hζbar : GL (Fin 6) K) u)
        (zSU_maps_U2 h p hp ζ hζ hζbar hu), x.2 u hu]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      rw [zSU_fixes_orthogonal h p hp ζ hζ hζbar hw]
      rw [zSU_fixes_orthogonal h p hp ζ hζ hζbar (QSU_maps_orthogonal h x hw)]
  apply Subtype.ext
  apply toLinLE_injective K
  simp only [Subgroup.coe_mul, map_mul]
  exact hlin

theorem Qbar_le_centralizer_zbar (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    Qbar h p hp hp2 ζ hζ hζbar ≤
      Subgroup.centralizer ({zbar h p ζ hζ hζbar} : Set (primeFormP h (C6 K))) := by
  intro q hq
  obtain ⟨x, rfl⟩ := hq
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [zbar_eq_mk_zSU h p ζ hζ hζbar]
  change (QuotientGroup.mk' (N6 h)) ((x : ↥(gramSU h (C6 K))) * zSU h p ζ hζ hζbar) =
    (QuotientGroup.mk' (N6 h)) (zSU h p ζ hζ hζbar * (x : ↥(gramSU h (C6 K))))
  rw [QSU_commute_zSU h p hp ζ hζ hζbar x]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
