module

public import CFSG.ClassicalInvolution.RouteD.TWS7Op
public import CFSG.ClassicalInvolution.RouteD.GapsFrSpin
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  Matrix
open CFSG.LieType.Universal.Spin (HypFrame spinAction)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

namespace CFSG.ClassicalInvolution.RouteD.TWS7

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_eq_zero_of_eigen_ne {w : V ≃ₗ[K] V}
    (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x y : V} {ε δ : K} (hx : w x = ε • x)
    (hy : w y = δ • y) (hne : ε * δ ≠ 1) : polar Q x y = 0 := by
  have h1 := polar_map_of_mem hwO x y
  rw [hx, hy, polar_smul_left_eq, polar_smul_right_eq, ← mul_assoc] at h1
  have h3 : (ε * δ - 1) * polar Q x y = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne)

theorem coords_eq_zero_of_neg (h2 : (2 : K) ≠ 0) (fr : OFrame Q) {w : V ≃ₗ[K] V}
    (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hwfix : ∀ x ∈ fr.span, w x = x) {y : V}
    (hy : w y = (-1 : K) • y) : fr.coords y = 0 := by
  refine (Frame.mem_perp_iff fr).mp ((Frame.mem_perp_iff_forall_incl fr).mpr fun X => ?_)
  refine polar_eq_zero_of_eigen_ne hwO hy (δ := 1) (y := fr.incl X) (by
    rw [hwfix _ ⟨X, rfl⟩, one_smul]) ?_
  intro h
  apply h2
  linear_combination -h

theorem exists_partner_eigen (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (fr : OFrame Q) {w : V ≃ₗ[K] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hw2 : w * w = 1) (hwfix : ∀ x ∈ fr.span, w x = x) {ε : K} (hε : ε = 1 ∨ ε = -1) {u : V}
    (hu0 : u ≠ 0) (hQu : Q u = 0) (hwu : w u = ε • u) (hcu : fr.coords u = 0) :
    ∃ f : V, Q f = 0 ∧ polar Q u f = 1 ∧ w f = ε • f ∧ fr.coords f = 0 := by
  classical
  have hww : ∀ y, w (w y) = y := fun y => by
    have := congrArg (fun m : V ≃ₗ[K] V => m y) hw2
    simpa using this
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨y₀, hy₀⟩ := exists_polar_ne_zero hQ hu0
  set y₁ : V := y₀ + ε • w y₀ with hy₁
  have hwy₁ : w y₁ = ε • y₁ := by
    rw [hy₁, map_add, map_smul, hww, smul_add, smul_smul, hεε, one_smul, add_comm]
  have hpw : polar Q u (w y₀) = ε * polar Q u y₀ := by
    have h1 := polar_map_of_mem hwO u (w y₀)
    rw [hww, hwu, polar_smul_left_eq] at h1
    exact h1.symm
  have hpu₁ : polar Q u y₁ = 2 * polar Q u y₀ := by
    rw [hy₁, polar_add_right, polar_smul_right_eq, hpw]
    linear_combination (polar Q u y₀) * hεε
  set y₂ : V := y₁ - fr.incl (fr.coords y₁) with hy₂
  have hcy₂ : fr.coords y₂ = 0 := by rw [hy₂, map_sub, Frame.coords_incl, sub_self]
  have hwy₂ : w y₂ = ε • y₂ := by
    rcases hε with rfl | rfl
    · rw [hy₂, map_sub, hwfix _ ⟨_, rfl⟩, hwy₁]
      simp
    · have hc1 : fr.coords y₁ = 0 := coords_eq_zero_of_neg h2 fr hwO hwfix hwy₁
      rw [hy₂, hc1, map_zero, sub_zero]
      exact hwy₁
  have hpu₂ : polar Q u y₂ = 2 * polar Q u y₀ := by
    have hup : ∀ Y, polar Q u (fr.incl Y) = 0 :=
      (Frame.mem_perp_iff_forall_incl fr).mp ((Frame.mem_perp_iff fr).mpr hcu)
    rw [hy₂, polar_sub_right, hup, sub_zero, hpu₁]
  have hc0 : polar Q u y₂ ≠ 0 := by
    rw [hpu₂]
    exact mul_ne_zero h2 hy₀
  set c : K := polar Q u y₂ with hc
  refine ⟨c⁻¹ • y₂ + (-(c⁻¹ * c⁻¹ * Q y₂)) • u, ?_, ?_, ?_, ?_⟩
  · rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQu, mul_zero, polar_smul_left_eq,
      polar_smul_right_eq, polar_comm Q y₂ u, ← hc]
    field_simp
    ring
  · rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, ← hc,
      polar_self_eq_zero hQu]
    field_simp
    ring
  · rw [map_add, map_smul, map_smul, hwy₂, hwu, smul_comm c⁻¹ ε y₂,
      smul_comm (-(c⁻¹ * c⁻¹ * Q y₂)) ε u, smul_add]
  · rw [map_add, map_smul, map_smul, hcy₂, hcu]
    simp

theorem polar_perp_span {fr : OFrame Q} {x y : V} (hx : fr.coords x = 0) (hy : y ∈ fr.span) :
    polar Q x y = 0 := by
  obtain ⟨Y, rfl⟩ := hy
  exact (Frame.mem_perp_iff_forall_incl fr).mp ((Frame.mem_perp_iff fr).mpr hx) Y

theorem orth_symm {P P' : HypPair Q} (h : P.Orth P') : P'.Orth P :=
  ⟨by rw [polar_comm]; exact h.ee, by rw [polar_comm]; exact h.fe,
    by rw [polar_comm]; exact h.ef, by rw [polar_comm]; exact h.ff⟩

end General

section Adapted

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [Finite K] [FiniteDimensional K V]

theorem exists_adapted_frame (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (F₀ : HypFrame Q 4) (fr : OFrame Q) {w : V ≃ₗ[K] V}
    (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hw2 : w * w = 1)
    (hwfix : ∀ x ∈ fr.span, w x = x) {up um : V} (hcup : fr.coords up = 0)
    (hcum : fr.coords um = 0) (hup0 : up ≠ 0) (hum0 : um ≠ 0) (hwup : w up = up)
    (hwum : w um = -um) (hQup : Q up = 0) (hQum : Q um = 0) :
    ∃ κ : spinGroup Q, ∀ (i : Fin 4) (s : Bool),
      w (spinAction Q κ (F₀.vec i s)) =
        (if i.val = 0 then (-1 : K) else 1) • spinAction Q κ (F₀.vec i s) := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨fm, hQfm, hpfm, hwfm, hcfm⟩ := exists_partner_eigen h2 hQ fr hwO hw2 hwfix
    (ε := -1) (Or.inr rfl) hum0 hQum (by rw [hwum]; simp) hcum
  obtain ⟨fp, hQfp, hpfp, hwfp, hcfp⟩ := exists_partner_eigen h2 hQ fr hwO hw2 hwfix
    (ε := 1) (Or.inl rfl) hup0 hQup (by rw [hwup, one_smul]) hcup
  rw [one_smul] at hwfp
  let P0 : HypPair Q := ⟨um, fm, hQum, hQfm, hpfm⟩
  let P1 : HypPair Q := ⟨up, fp, hQup, hQfp, hpfp⟩
  let P : Fin 4 → HypPair Q := ![P0, P1, fr.P, fr.P']
  have hm1 : (-1 : K) * 1 ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  have hneg : (-1 : K) = -1 := rfl
  have hP01 : P0.Orth P1 := by
    have hu : w um = (-1 : K) • um := by rw [hwum]; simp
    have hf : w fm = (-1 : K) • fm := hwfm
    have hu' : w up = (1 : K) • up := by rw [hwup, one_smul]
    have hf' : w fp = (1 : K) • fp := by rw [hwfp, one_smul]
    exact ⟨polar_eq_zero_of_eigen_ne hwO hu hu' hm1, polar_eq_zero_of_eigen_ne hwO hu hf' hm1,
      polar_eq_zero_of_eigen_ne hwO hf hu' hm1, polar_eq_zero_of_eigen_ne hwO hf hf' hm1⟩
  have hPW : ∀ {x y : V}, fr.coords x = 0 → y ∈ fr.span → polar Q x y = 0 := fun hx hy =>
    polar_perp_span hx hy
  have hmemP : fr.P.e ∈ fr.span ∧ fr.P.f ∈ fr.span ∧ fr.P'.e ∈ fr.span ∧ fr.P'.f ∈ fr.span :=
    ⟨fr.e₁_mem_span, fr.f₁_mem_span, fr.e₂_mem_span, fr.f₂_mem_span⟩
  have hP02 : P0.Orth fr.P :=
    ⟨hPW hcum fr.e₁_mem_span, hPW hcum fr.f₁_mem_span, hPW hcfm fr.e₁_mem_span,
      hPW hcfm fr.f₁_mem_span⟩
  have hP03 : P0.Orth fr.P' :=
    ⟨hPW hcum fr.e₂_mem_span, hPW hcum fr.f₂_mem_span, hPW hcfm fr.e₂_mem_span,
      hPW hcfm fr.f₂_mem_span⟩
  have hP12 : P1.Orth fr.P :=
    ⟨hPW hcup fr.e₁_mem_span, hPW hcup fr.f₁_mem_span, hPW hcfp fr.e₁_mem_span,
      hPW hcfp fr.f₁_mem_span⟩
  have hP13 : P1.Orth fr.P' :=
    ⟨hPW hcup fr.e₂_mem_span, hPW hcup fr.f₂_mem_span, hPW hcfp fr.e₂_mem_span,
      hPW hcfp fr.f₂_mem_span⟩
  have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact hP01 | exact orth_symm hP01 | exact hP02 | exact orth_symm hP02
      | exact hP03 | exact orth_symm hP03 | exact hP12 | exact orth_symm hP12
      | exact hP13 | exact orth_symm hP13 | exact fr.orth | exact orth_symm fr.orth
  obtain ⟨κ, hκ1, a, b, c, d, hκe, hκf⟩ := CFSG.ClassicalInvolution.RouteD.Gaps.exists_spin_family
    hodd hQ' F₀ hP (3 : Fin 4)
  have hxQ : ∀ s, Q (spinAction Q κ (F₀.vec 3 s)) = 0 := fun s => by
    rw [CFSG.LieType.Universal.Spin.map_spinAction]
    exact F₀.map_vec 3 s
  have hxp : polar Q (spinAction Q κ (F₀.vec 3 true)) (spinAction Q κ (F₀.vec 3 false)) = 1 := by
    rw [CFSG.LieType.Universal.Spin.polar_spinAction]
    simpa using F₀.polar_vec_not 3 true
  have hxp' : polar Q (spinAction Q κ (F₀.vec 3 false)) (spinAction Q κ (F₀.vec 3 true)) = 1 := by
    rw [polar_comm]
    exact hxp
  have he3 : fr.P'.e =
      a • spinAction Q κ (F₀.vec 3 true) + b • spinAction Q κ (F₀.vec 3 false) := by
    show (P 3).e = _
    rw [hκe, map_add, map_smul, map_smul]
  have hf3 : fr.P'.f =
      c • spinAction Q κ (F₀.vec 3 true) + d • spinAction Q κ (F₀.vec 3 false) := by
    show (P 3).f = _
    rw [hκf, map_add, map_smul, map_smul]
  set xt := spinAction Q κ (F₀.vec 3 true) with hxt
  set xf := spinAction Q κ (F₀.vec 3 false) with hxf
  have hab : a * b = 0 := by
    have h := fr.Q_e₂
    have h' : Q (fr.P'.e) = 0 := h
    rw [he3, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hxQ true, hxQ false,
      polar_smul_left_eq, polar_smul_right_eq, hxp] at h'
    linear_combination h'
  have hcd : c * d = 0 := by
    have h' : Q (fr.P'.f) = 0 := fr.Q_f₂
    rw [hf3, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hxQ true, hxQ false,
      polar_smul_left_eq, polar_smul_right_eq, hxp] at h'
    linear_combination h'
  have hpol : a * d + b * c = 1 := by
    have h' : polar Q fr.P'.e fr.P'.f = 1 := fr.polar_e₂_f₂
    rw [he3, hf3, polar_add_left, polar_add_right, polar_add_right, polar_smul_left_eq,
      polar_smul_right_eq, polar_smul_left_eq, polar_smul_right_eq, polar_smul_left_eq,
      polar_smul_right_eq, polar_smul_left_eq, polar_smul_right_eq,
      polar_self_eq_zero (hxQ true), polar_self_eq_zero (hxQ false), hxp, hxp'] at h'
    linear_combination h'
  have hdet : a * d - b * c ≠ 0 := by
    intro h
    have h1 : (a * d - b * c) ^ 2 = 1 := by
      linear_combination (a * d + b * c + 1) * hpol + (-4 * (c * d)) * hab
    rw [h] at h1
    norm_num at h1
  have hwe3 : w fr.P'.e = fr.P'.e := hwfix _ fr.e₂_mem_span
  have hwf3 : w fr.P'.f = fr.P'.f := hwfix _ fr.f₂_mem_span
  rw [he3, map_add, map_smul, map_smul] at hwe3
  rw [hf3, map_add, map_smul, map_smul] at hwf3
  have hwxt : w xt = xt := by
    have h0 : (a * d - b * c) • (w xt - xt) = 0 := by
      have e1 : a • w xt + b • w xf - (a • xt + b • xf) = 0 := sub_eq_zero.mpr hwe3
      have e2 : c • w xt + d • w xf - (c • xt + d • xf) = 0 := sub_eq_zero.mpr hwf3
      calc (a * d - b * c) • (w xt - xt)
          = d • (a • w xt + b • w xf - (a • xt + b • xf)) -
            b • (c • w xt + d • w xf - (c • xt + d • xf)) := by module
        _ = 0 := by rw [e1, e2]; simp
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_left hdet)
  have hwxf : w xf = xf := by
    have h0 : (a * d - b * c) • (w xf - xf) = 0 := by
      have e1 : a • w xt + b • w xf - (a • xt + b • xf) = 0 := sub_eq_zero.mpr hwe3
      have e2 : c • w xt + d • w xf - (c • xt + d • xf) = 0 := sub_eq_zero.mpr hwf3
      calc (a * d - b * c) • (w xf - xf)
          = a • (c • w xt + d • w xf - (c • xt + d • xf)) -
            c • (a • w xt + b • w xf - (a • xt + b • xf)) := by module
        _ = 0 := by rw [e1, e2]; simp
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_left hdet)
  refine ⟨κ, fun i s => ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl | rfl
  · obtain ⟨h0e, h0f⟩ := hκ1 0 (by decide)
    cases s
    · have : spinAction Q κ (F₀.vec 0 false) = fm := h0f.symm
      rw [this]
      simpa using hwfm
    · have : spinAction Q κ (F₀.vec 0 true) = um := h0e.symm
      rw [this]
      simpa using hwum
  · obtain ⟨h1e, h1f⟩ := hκ1 1 (by decide)
    cases s
    · have : spinAction Q κ (F₀.vec 1 false) = fp := h1f.symm
      rw [this]
      simpa using hwfp
    · have : spinAction Q κ (F₀.vec 1 true) = up := h1e.symm
      rw [this]
      simpa using hwup
  · obtain ⟨h2e, h2f⟩ := hκ1 2 (by decide)
    cases s
    · have : spinAction Q κ (F₀.vec 2 false) = fr.P.f := h2f.symm
      rw [this]
      simpa using hwfix _ fr.f₁_mem_span
    · have : spinAction Q κ (F₀.vec 2 true) = fr.P.e := h2e.symm
      rw [this]
      simpa using hwfix _ fr.e₁_mem_span
  · cases s
    · simpa using hwxf
    · simpa using hwxt

end Adapted

end CFSG.ClassicalInvolution.RouteD.TWS7
