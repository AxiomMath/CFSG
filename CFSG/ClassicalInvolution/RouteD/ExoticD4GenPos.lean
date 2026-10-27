module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4GenMix
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinFrame
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Center
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Balance.Bootstrap (La_neg_one_of_mem_span La_neg_one_of_mem_perp)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section Helpers

theorem mem_span_of_La_neg_one (h2 : (2 : F) ≠ 0) (fr : OFrame Q) {x : V}
    (hx : fr.La (-1) x = -x) : x ∈ fr.span := by
  rw [Frame.La_neg_one_apply] at hx
  rw [fr.mem_span_iff]
  have h : (2 : F) • x = (2 : F) • fr.incl (fr.coords x) := by
    calc (2 : F) • x = x - (-x) := by module
      _ = x - (x - (2 : F) • fr.incl (fr.coords x)) := by rw [← hx]
      _ = (2 : F) • fr.incl (fr.coords x) := by abel
  exact smul_right_injective V h2 h

theorem mem_perp_of_La_neg_one (h2 : (2 : F) ≠ 0) (fr : OFrame Q) {x : V}
    (hx : fr.La (-1) x = x) : x ∈ fr.perp := by
  rw [Frame.La_neg_one_apply] at hx
  rw [fr.mem_perp_iff]
  have h : (2 : F) • fr.incl (fr.coords x) = 0 := by
    rw [sub_eq_self] at hx
    exact hx
  have h0 : fr.incl (fr.coords x) = 0 := (smul_eq_zero.mp h).resolve_left h2
  have := congrArg fr.coords h0
  rwa [Frame.coords_incl, map_zero] at this

theorem finrank_perp_eq_four [FiniteDimensional F V] (hdim : Module.finrank F V = 8)
    (fr : OFrame Q) : Module.finrank F fr.perp = 4 := by
  have h1 := Submodule.finrank_add_eq_of_isCompl fr.isCompl_span_perp
  rw [Frame.finrank_span, hdim] at h1
  omega

theorem span_eq_perp_of_span_eq_perp [FiniteDimensional F V] (hdim : Module.finrank F V = 8)
    {fr₁ fr₃ : OFrame Q} (hY : fr₃.span = fr₁.perp) : fr₁.span = fr₃.perp := by
  refine Submodule.eq_of_le_of_finrank_eq (fun x hx => mem_perp₃_of_mem_span₁ hY hx) ?_
  rw [Frame.finrank_span, finrank_perp_eq_four hdim]

end Helpers

section Singular

theorem polar_span_perp (fr : OFrame Q) {x y : V} (hx : x ∈ fr.span) (hy : y ∈ fr.perp) :
    polar Q x y = 0 := by
  calc polar Q x y = polar Q y x := polar_comm Q x y
    _ = polar Q y (fr.incl (fr.coords x)) := by rw [← fr.mem_span_iff.mp hx]
    _ = 0 := by rw [fr.polar_incl_right, fr.mem_perp_iff.mp hy]; simp

theorem Q_eq_zero_of_mem_span_pair (fr : OFrame Q) (a b : F) :
    Q (a • fr.e₁ + b • fr.e₂) = 0 := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, fr.Q_e₁, fr.Q_e₂,
    polar_smul_left_eq, polar_smul_right_eq, fr.polar_e₁_e₂]
  ring

theorem exists_singular_of_finrank_ge_three [FiniteDimensional F V] (fr : OFrame Q)
    {T : Submodule F V} (hT : T ≤ fr.span) (h3 : 3 ≤ Module.finrank F T) :
    ∃ t ∈ T, t ≠ 0 ∧ Q t = 0 := by
  set L : Submodule F V := Submodule.span F (Set.range ![fr.e₁, fr.e₂]) with hL
  have hLspan : L ≤ fr.span := by
    rw [hL, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Frame.e₁_mem_span fr
    · exact Frame.e₂_mem_span fr
  have hli : LinearIndependent F ![fr.e₁, fr.e₂] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (fun v => polar Q v fr.f₁) hab
    have h2 := congrArg (fun v => polar Q v fr.f₂) hab
    simp only [polar_add_left, polar_smul_left_eq, polar_zero_left, fr.polar_e₁_f₁,
      fr.polar_e₂_f₁, fr.polar_e₁_f₂, fr.polar_e₂_f₂] at h1 h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  have hLdim : Module.finrank F L = 2 := by
    rw [hL, finrank_span_eq_card hli]
    simp
  have hsup : T ⊔ L ≤ fr.span := sup_le hT hLspan
  have h4 : Module.finrank F ↥(T ⊔ L) ≤ 4 := by
    have := Submodule.finrank_mono hsup
    rwa [Frame.finrank_span] at this
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq T L
  have hpos : 0 < Module.finrank F ↥(T ⊓ L) := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  refine ⟨x, (x.2).1, fun h => hx (Subtype.ext h), ?_⟩
  have hxL : (x : V) ∈ Submodule.span F (Set.range ![fr.e₁, fr.e₂]) := (x.2).2
  rw [Submodule.mem_span_range_iff_exists_fun] at hxL
  obtain ⟨c, hc⟩ := hxL
  rw [← hc, Fin.sum_univ_two]
  exact Q_eq_zero_of_mem_span_pair fr (c 0) (c 1)

theorem exists_singular_polar_eq_zero (fr : OFrame Q) (z : V) :
    ∃ s ∈ fr.span, s ≠ 0 ∧ Q s = 0 ∧ polar Q s z = 0 := by
  by_cases ha : polar Q fr.e₁ z = 0
  · exact ⟨fr.e₁, Frame.e₁_mem_span fr, e₁_ne_zero fr, fr.Q_e₁, ha⟩
  · refine ⟨polar Q fr.e₂ z • fr.e₁ + (-polar Q fr.e₁ z) • fr.e₂,
      Submodule.add_mem _ (Submodule.smul_mem _ _ (Frame.e₁_mem_span fr))
        (Submodule.smul_mem _ _ (Frame.e₂_mem_span fr)), ?_,
      Q_eq_zero_of_mem_span_pair fr _ _, ?_⟩
    · intro h
      have h1 := congrArg (fun v => polar Q v fr.f₂) h
      simp only [polar_add_left, polar_smul_left_eq, polar_zero_left, fr.polar_e₁_f₂,
        fr.polar_e₂_f₂] at h1
      simp at h1
      exact ha h1
    · rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq]
      ring

end Singular

section Swap

variable {fr fr' frY : OFrame Q}

theorem case_swap [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (hY : frY.span = fr.perp)
    {G : Subgroup (V ≃ₗ[F] V)} (h₁ : omegaGrp fr ≤ G) (h₃ : omegaGrp frY ≤ G)
    (h' : omegaGrp fr' ≤ G)
    (hanti : ∀ x, fr'.La (-1) (fr.La (-1) x) = -fr.La (-1) (fr'.La (-1) x)) :
    elementaryGroup Q ≤ G := by
  set t' : V ≃ₗ[F] V := fr'.La (-1) with ht'
  have ht'2 : ∀ x, t' (t' x) = x := fun x => by
    have h := congrArg (fun T : V ≃ₗ[F] V => T x) (Frame.La_neg_one_mul_self fr')
    exact h
  have hO' : t' ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fr'.La_mem_orthogonalGroup (-1)
  have hQ' : ∀ x, Q (t' x) = Q x := fun x => map_of_mem hO' x
  have hP' : ∀ x y, polar Q (t' x) (t' y) = polar Q x y := fun x y => polar_map_of_mem hO' x y
  have hperp : ∀ x ∈ fr.span, t' x ∈ fr.perp := by
    intro x hx
    refine mem_perp_of_La_neg_one h2 fr ?_
    have h1 := hanti x
    rw [La_neg_one_of_mem_span fr hx, map_neg] at h1
    exact (neg_injective h1).symm
  have hcr : ∀ x ∈ fr.span, ∀ y ∈ fr.span, polar Q x (t' y) = 0 := fun x hx y hy =>
    polar_span_perp fr hx (hperp y hy)
  have hmem : ∀ x ∈ fr.span, x - t' x ∈ fr'.span := by
    intro x hx
    refine mem_span_of_La_neg_one h2 fr' ?_
    show t' (x - t' x) = -(x - t' x)
    rw [map_sub, ht'2]
    abel
  have hQd : ∀ x ∈ fr.span, Q (x - t' x) = 2 * Q x := by
    intro x hx
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q, hQ', polar_neg_right,
      hcr x hx x hx]
    ring
  have hPd : ∀ x ∈ fr.span, ∀ y ∈ fr.span, polar Q (x - t' x) (y - t' y) = 2 * polar Q x y := by
    intro x hx y hy
    rw [polar_sub_left, polar_sub_right, polar_sub_right, hP', hcr x hx y hy,
      polar_comm Q (t' x) y, hcr y hy x hx]
    ring
  set x₁ := fr.e₁ with hx₁
  set x₂ := fr.e₂ with hx₂
  set x' := fr.f₂ with hx'
  have hx₁s : x₁ ∈ fr.span := Frame.e₁_mem_span fr
  have hx₂s : x₂ ∈ fr.span := Frame.e₂_mem_span fr
  have hx's : x' ∈ fr.span := Frame.f₂_mem_span fr
  set v := x₁ - t' x₁ with hv
  set w := x₂ - t' x₂ with hw
  have hQv : Q v = 0 := by rw [hv, hQd x₁ hx₁s, fr.Q_e₁, mul_zero]
  have hQw : Q w = 0 := by rw [hw, hQd x₂ hx₂s, fr.Q_e₂, mul_zero]
  have hpvw : polar Q v w = 0 := by rw [hv, hw, hPd x₁ hx₁s x₂ hx₂s, fr.polar_e₁_e₂, mul_zero]
  have hg : eichler Q v w ∈ G :=
    h' (eichler_mem_omegaGrp fr' (hmem x₁ hx₁s) (hmem x₂ hx₂s) hQv hpvw)
  have hgO := eichler_mem_orthogonalGroup Q v w
  have hgx₁ : eichler Q v w x₁ = x₁ := by
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [hv, polar_sub_right, hcr x₁ hx₁s x₁ hx₁s, fr.polar_e₁_e₁]; ring
    · rw [hw, polar_sub_right, hcr x₁ hx₁s x₂ hx₂s, fr.polar_e₁_e₂]; ring
  have hE₁ : eichler Q x₁ (x' - x₁) ∈ G := by
    refine h₁ (eichler_mem_omegaGrp fr hx₁s (Submodule.sub_mem _ hx's hx₁s) fr.Q_e₁ ?_)
    rw [polar_sub_right, fr.polar_e₁_f₂, fr.polar_e₁_e₁]; ring
  have hE₂ : eichler Q x₁ x' ∈ G :=
    h₁ (eichler_mem_omegaGrp fr hx₁s hx's fr.Q_e₁ fr.polar_e₁_f₂)
  have hc := eichler_conj hgO x₁ x'
  rw [hgx₁] at hc
  have hE₃ : eichler Q x₁ (eichler Q v w x') ∈ G := by
    rw [← hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hE₂) (Subgroup.inv_mem _ hg)
  have hgx' : eichler Q v w x' = (x' - x₁) + t' x₁ := by
    rw [eichler_apply hQv hpvw]
    have e1 : polar Q x' v = 0 := by
      rw [hv, polar_sub_right, hcr x' hx's x₁ hx₁s, fr.polar_f₂_e₁]; ring
    have e2 : polar Q x' w = 1 := by
      rw [hw, polar_sub_right, hcr x' hx's x₂ hx₂s, fr.polar_f₂_e₂]; ring
    rw [e1, e2, hQw, hv]
    module
  have hp1 : polar Q x₁ (x' - x₁) = 0 := by
    rw [polar_sub_right, fr.polar_e₁_f₂, fr.polar_e₁_e₁]; ring
  have hp2 : polar Q x₁ (t' x₁) = 0 := hcr x₁ hx₁s x₁ hx₁s
  have hE₄ : eichler Q x₁ (t' x₁) ∈ G := by
    have h := eichler_mul hp1 hp2
    rw [← hgx'] at h
    have : eichler Q x₁ (t' x₁) = (eichler Q x₁ (x' - x₁))⁻¹ * eichler Q x₁ (eichler Q v w x') := by
      rw [← h]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE₁) hE₃
  have hy0 : t' x₁ ≠ 0 := by
    intro h
    apply e₁_ne_zero fr
    show x₁ = 0
    rw [← ht'2 x₁, h, map_zero]
  exact elementaryGroup_le_of_mixed h2 hY h₁ h₃ hx₁s (hY ▸ hperp x₁ hx₁s) fr.Q_e₁ (e₁_ne_zero fr)
    hy0 hE₄

end Swap

section Comm

variable {fr fr' frY : OFrame Q}

theorem case_comm [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (hdim : Module.finrank F V = 8)
    (hY : frY.span = fr.perp) {G : Subgroup (V ≃ₗ[F] V)} (h₁ : omegaGrp fr ≤ G)
    (h₃ : omegaGrp frY ≤ G) (h' : omegaGrp fr' ≤ G) (hne1 : fr'.span ≠ fr.span)
    (hne2 : fr'.span ≠ fr.perp)
    (hcomm : ∀ x, fr'.La (-1) (fr.La (-1) x) = fr.La (-1) (fr'.La (-1) x)) :
    elementaryGroup Q ≤ G := by
  set t : V ≃ₗ[F] V := fr.La (-1) with ht
  have ht2 : ∀ x, t (t x) = x := fun x => by
    have h := congrArg (fun T : V ≃ₗ[F] V => T x) (Frame.La_neg_one_mul_self fr)
    exact h
  have hY' : fr.span = frY.perp := span_eq_perp_of_span_eq_perp hdim hY
  have hinv : (2⁻¹ : F) + 2⁻¹ = 1 := by
    field_simp
    norm_num
  have hdec : ∀ x ∈ fr'.span, (2⁻¹ : F) • (x - t x) ∈ fr.span ∧
      (2⁻¹ : F) • (x - t x) ∈ fr'.span ∧ (2⁻¹ : F) • (x + t x) ∈ fr.perp ∧
      (2⁻¹ : F) • (x + t x) ∈ fr'.span ∧
      x = (2⁻¹ : F) • (x - t x) + (2⁻¹ : F) • (x + t x) := by
    intro x hx
    have hx' : fr'.La (-1) x = -x := La_neg_one_of_mem_span fr' hx
    have htx' : t x ∈ fr'.span := by
      refine mem_span_of_La_neg_one h2 fr' ?_
      rw [hcomm x, hx', map_neg]
    have hsub : x - t x ∈ fr'.span := Submodule.sub_mem _ hx htx'
    have hadd : x + t x ∈ fr'.span := Submodule.add_mem _ hx htx'
    refine ⟨?_, Submodule.smul_mem _ _ hsub, ?_, Submodule.smul_mem _ _ hadd, ?_⟩
    · refine mem_span_of_La_neg_one h2 fr ?_
      show t ((2⁻¹ : F) • (x - t x)) = -((2⁻¹ : F) • (x - t x))
      rw [map_smul, map_sub, ht2]
      module
    · refine mem_perp_of_La_neg_one h2 fr ?_
      show t ((2⁻¹ : F) • (x + t x)) = (2⁻¹ : F) • (x + t x)
      rw [map_smul, map_add, ht2, add_comm]
    · calc x = ((2⁻¹ : F) + 2⁻¹) • x := by rw [hinv, one_smul]
        _ = _ := by module
  set U : Submodule F V := fr.span ⊓ fr'.span with hU
  set U₂ : Submodule F V := fr.perp ⊓ fr'.span with hU₂
  have hdU : ∀ x ∈ fr'.span, (2⁻¹ : F) • (x - t x) ∈ U := fun x hx =>
    ⟨(hdec x hx).1, (hdec x hx).2.1⟩
  have hdU₂ : ∀ x ∈ fr'.span, (2⁻¹ : F) • (x + t x) ∈ U₂ := fun x hx =>
    ⟨(hdec x hx).2.2.1, (hdec x hx).2.2.2.1⟩
  have hU₂ne : U₂ ≠ ⊥ := by
    intro h
    apply hne1
    refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [Frame.finrank_span, Frame.finrank_span])
    intro x hx
    have h0 : (2⁻¹ : F) • (x + t x) = 0 := (Submodule.mem_bot F).mp (h ▸ hdU₂ x hx)
    rw [(hdec x hx).2.2.2.2, h0, add_zero]
    exact (hdec x hx).1
  have hUne : U ≠ ⊥ := by
    intro h
    apply hne2
    refine Submodule.eq_of_le_of_finrank_eq ?_
      (by rw [Frame.finrank_span, finrank_perp_eq_four hdim])
    intro x hx
    have h0 : (2⁻¹ : F) • (x - t x) = 0 := (Submodule.mem_bot F).mp (h ▸ hdU x hx)
    rw [(hdec x hx).2.2.2.2, h0, zero_add]
    exact (hdec x hx).2.2.1
  by_cases hA : ∃ s ∈ U, s ≠ 0 ∧ Q s = 0
  · obtain ⟨s, hsU, hs0, hQs⟩ := hA
    obtain ⟨w, hwU₂, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU₂ne
    have hE : eichler Q s w ∈ G :=
      h' (eichler_mem_omegaGrp fr' hsU.2 hwU₂.2 hQs (polar_span_perp fr hsU.1 hwU₂.1))
    exact elementaryGroup_le_of_mixed h2 hY h₁ h₃ hsU.1 (by rw [hY]; exact hwU₂.1) hQs hs0 hw0 hE
  by_cases hA' : ∃ s ∈ U₂, s ≠ 0 ∧ Q s = 0
  · obtain ⟨s, hsU₂, hs0, hQs⟩ := hA'
    obtain ⟨w, hwU, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
    have hE : eichler Q s w ∈ G :=
      h' (eichler_mem_omegaGrp fr' hsU₂.2 hwU.2 hQs (by
        rw [polar_comm]
        exact polar_span_perp fr hwU.1 hsU₂.1))
    exact elementaryGroup_le_of_mixed h2 hY' h₃ h₁ (by rw [hY]; exact hsU₂.1) hwU.1 hQs hs0 hw0 hE
  push Not at hA hA'
  have hdimU : Module.finrank F U ≤ 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t0, ht0, ht00, ht0Q⟩ :=
      exists_singular_of_finrank_ge_three fr (T := U) inf_le_left (by omega)
    exact hA t0 ht0 ht00 ht0Q
  have hsup : U ⊔ U₂ = fr'.span := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
    intro x hx
    rw [(hdec x hx).2.2.2.2]
    exact Submodule.add_mem_sup (hdU x hx) (hdU₂ x hx)
  have hdisj : U ⊓ U₂ = ⊥ := by
    have : Disjoint U U₂ := (fr.isCompl_span_perp.disjoint).mono inf_le_left inf_le_left
    exact disjoint_iff.mp this
  have hsum : Module.finrank F U + Module.finrank F U₂ = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U U₂
    rw [hsup, hdisj, finrank_bot, Frame.finrank_span] at h
    omega
  have hdimU₂ : 2 ≤ Module.finrank F U₂ := by omega
  set v := fr'.e₁ with hv
  have hvs : v ∈ fr'.span := Frame.e₁_mem_span fr'
  have hQv : Q v = 0 := fr'.Q_e₁
  have hv0 : v ≠ 0 := e₁_ne_zero fr'
  set vX := (2⁻¹ : F) • (v - t v) with hvX
  set vY := (2⁻¹ : F) • (v + t v) with hvY
  have hvXU : vX ∈ U := hdU v hvs
  have hvYU : vY ∈ U₂ := hdU₂ v hvs
  have hvsum : v = vX + vY := (hdec v hvs).2.2.2.2
  have hvXs : vX ∈ fr.span := hvXU.1
  have hvYp : vY ∈ fr.perp := hvYU.1
  have hvX0 : vX ≠ 0 := by
    intro h
    have e : v = vY := by rw [hvsum, h, zero_add]
    have hvY0 : vY ≠ 0 := fun h' => hv0 (e.trans h')
    exact hA' vY hvYU hvY0 (by rw [← e]; exact hQv)
  have hvY0 : vY ≠ 0 := by
    intro h
    have e : v = vX := by rw [hvsum, h, add_zero]
    exact hA vX hvXU hvX0 (by rw [← e]; exact hQv)
  have hκ : Q vX ≠ 0 := hA vX hvXU hvX0
  have hQsum : Q v = Q vX + Q vY := by
    conv_lhs => rw [hvsum]
    rw [QuadraticMap.map_add Q, polar_span_perp fr hvXs hvYp, add_zero]
  have hQvY : Q vY = -Q vX := by
    have : Q vX + Q vY = 0 := by rw [← hQsum, hQv]
    exact eq_neg_of_add_eq_zero_right this
  have hQvY0 : Q vY ≠ 0 := by rw [hQvY]; exact neg_ne_zero.mpr hκ
  obtain ⟨y₂, hy₂U₂, hy₂0, hy₂v⟩ : ∃ y₂ ∈ U₂, y₂ ≠ 0 ∧ polar Q y₂ vY = 0 := by
    set φ : U₂ →ₗ[F] F := ((polarBilin Q).flip vY).comp U₂.subtype with hφ
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2' : Module.finrank F (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      simpa using this
    have h3 : 0 < Module.finrank F (LinearMap.ker φ) := by omega
    obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h3
    refine ⟨((z : U₂) : V), (z : U₂).2, fun h => hz (Subtype.ext (Subtype.ext h)), ?_⟩
    have h4 : φ (z : U₂) = 0 := LinearMap.mem_ker.mp z.2
    exact h4
  have hy₂s' : y₂ ∈ fr'.span := hy₂U₂.2
  have hy₂p : y₂ ∈ fr.perp := hy₂U₂.1
  have hpvy₂ : polar Q v y₂ = 0 := by
    rw [hvsum, polar_add_left, polar_span_perp fr hvXs hy₂p, polar_comm Q vY y₂, hy₂v, add_zero]
  have hg : eichler Q v y₂ ∈ G := h' (eichler_mem_omegaGrp fr' hvs hy₂s' hQv hpvy₂)
  have hgO := eichler_mem_orthogonalGroup Q v y₂
  obtain ⟨s, hs, hs0, hQs, hsvX⟩ := exists_singular_polar_eq_zero fr vX
  have hsvY : polar Q s vY = 0 := polar_span_perp fr hs hvYp
  have hsv : polar Q s v = 0 := by rw [hvsum, polar_add_right, hsvX, hsvY, add_zero]
  have hsy₂ : polar Q s y₂ = 0 := polar_span_perp fr hs hy₂p
  have hgs : eichler Q v y₂ s = s := eichler_apply_of_polar_eq_zero hsv hsy₂
  have hE₁ : eichler Q s vX ∈ G := h₁ (eichler_mem_omegaGrp fr hs hvXs hQs hsvX)
  have hc := eichler_conj hgO s vX
  rw [hgs] at hc
  have hE₂ : eichler Q s (eichler Q v y₂ vX) ∈ G := by
    rw [← hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hE₁) (Subgroup.inv_mem _ hg)
  set κ := Q vX with hκdef
  set c : F := 2 * κ with hcdef
  have hc0 : c ≠ 0 := mul_ne_zero h2 hκ
  set x₁ : V := (1 - Q y₂ * c) • vX with hx₁
  set y₁ : V := c • y₂ - (Q y₂ * c) • vY with hy₁
  have hpvXv : polar Q vX v = c := by
    rw [hvsum, polar_add_right, polar_span_perp fr hvXs hvYp, polar_self_eq_two_mul, add_zero]
  have hgvX : eichler Q v y₂ vX = x₁ + y₁ := by
    rw [eichler_apply hQv hpvy₂, hpvXv, polar_span_perp fr hvXs hy₂p]
    conv_lhs => rw [hvsum]
    module
  have hx₁s : x₁ ∈ fr.span := Submodule.smul_mem _ _ hvXs
  have hy₁p : y₁ ∈ fr.perp :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hy₂p) (Submodule.smul_mem _ _ hvYp)
  have hsx₁ : polar Q s x₁ = 0 := by rw [hx₁, polar_smul_right_eq, hsvX, mul_zero]
  have hsy₁ : polar Q s y₁ = 0 := polar_span_perp fr hs hy₁p
  have hE₃ : eichler Q s x₁ ∈ G := h₁ (eichler_mem_omegaGrp fr hs hx₁s hQs hsx₁)
  have hE₄ : eichler Q s y₁ ∈ G := by
    have h := eichler_mul hsx₁ hsy₁
    rw [← hgvX] at h
    have : eichler Q s y₁ = (eichler Q s x₁)⁻¹ * eichler Q s (eichler Q v y₂ vX) := by
      rw [← h]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE₃) hE₂
  have hy₁0 : y₁ ≠ 0 := by
    intro h0
    have h1 : y₂ = Q y₂ • vY := by
      have h5 : c • (y₂ - Q y₂ • vY) = 0 := by
        rw [← h0, hy₁]
        module
      exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_left hc0)
    have h6 : polar Q y₂ vY = Q y₂ * (2 * Q vY) := by
      conv_lhs => rw [h1]
      rw [polar_smul_left_eq, polar_self_eq_two_mul]
    rw [hy₂v] at h6
    have h7 : Q y₂ = 0 := by
      have := h6.symm
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (mul_ne_zero h2 hQvY0)
    apply hy₂0
    rw [h1, h7, zero_smul]
  exact elementaryGroup_le_of_mixed h2 hY h₁ h₃ hs (by rw [hY]; exact hy₁p) hQs hs0 hy₁0 hE₄

end Comm

end CFSG.ClassicalInvolution.RouteD.Exotic
