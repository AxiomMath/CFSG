module

public import CFSG.ClassicalInvolution.Asc77.WP3SCVOrthA
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Lift
public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.SCV

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBHigherLinearField Matrix
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.ClassicalGroups.Orthogonal.Small CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

section Lift

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem exists_aut_of_centralizing_La (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    [Group.IsPerfect (spinGroup Q)] (hrange : (spinAction Q).range = elementaryGroup Q)
    (fr : Frame Q) {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (σ : ↥ψ.range ≃* ↥ψ.range) (hlift : LiftSimAt Q ψ σ)
    (hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹) :
    ∃ (α : spinGroup Q ≃* spinGroup Q) (a : (ι → F) ≃ₗ[F] (ι → F)) (μ : Fˣ),
      (∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x)) ∧
      (∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹) ∧
      (∀ g ∈ fr.La.range, a * g = g * a) ∧ (∀ v, Q (a v) = μ * Q v) := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set θ := spinAction Q with hθ
  obtain ⟨α, hαψ, A, φ, μ, hsim, hmat⟩ := hlift
  set P : Subgroup ((ι → F) ≃ₗ[F] (ι → F)) := fr.La.range with hP
  have hPE : P ≤ θ.range := by
    rw [hrange]
    exact fun g ⟨A, hA⟩ => hA ▸ fr.La_mem_elementaryGroup A
  have hcentral : ∀ s ∈ P.comap θ, s⁻¹ * α s ∈ Subgroup.center (spinGroup Q) := by
    intro s hs
    have hℓ := hσ s (Subgroup.mem_comap.mp hs)
    set x := ψ.rangeRestrict s with hx
    have hζ : ∀ m : ↥ψ.range, (x⁻¹ * σ x) * m = m * (x⁻¹ * σ x) := by
      intro m
      obtain ⟨ℓ, rfl⟩ := σ.surjective m
      have h1 := hℓ ℓ
      rw [map_mul, map_mul, map_inv] at h1
      calc x⁻¹ * σ x * σ ℓ = x⁻¹ * (σ x * σ ℓ * (σ x)⁻¹) * σ x := by group
        _ = x⁻¹ * (x * σ ℓ * x⁻¹) * σ x := by rw [h1]
        _ = σ ℓ * (x⁻¹ * σ x) := by group
    refine Orth15.mem_center_of_commutators_central fun t => hψ ?_
    rw [← MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, map_commutatorElement, map_mul,
      map_inv, hαψ s]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hζ _)
  have hfix := alpha_fixes_commutators α hcentral
  have hF4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨t, ht⟩
  have hSL : Group.IsPerfect SL(2, F) := CFSG.LinearGroups.special_linear_dimension_two_perfect hF4
  have hL₁ : ⁅fr.La.range, fr.La.range⁆ = fr.La.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range fr.La)
  have hPperf : ⁅P, P⁆ = P := hL₁
  have hlift2 := exists_lift_commutator θ hPE hPperf
  have hN : (LinearMap.toMatrix' (nuLin fr)) ≠ 0 := by
    intro h0
    exact nuLin_ne_zero fr ((LinearMap.toMatrix').injective (by rw [h0, map_zero]))
  have hφ : φ = RingEquiv.refl F := by
    refine ringEquiv_eq_refl_of_commute (LinearMap.toMatrix' (nuLin fr)) hN A φ fun c => ?_
    set g := fr.La (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c)
      with hg
    have hgP : g ∈ P := ⟨_, rfl⟩
    obtain ⟨s, hs, hsg⟩ := hlift2 g hgP
    have hαs : α s = s := hfix s hs
    have hm := hmat s
    rw [hαs] at hm
    have hM : ((spinMatrix Q s : GL ι F) : Matrix ι ι F) =
        1 + c • LinearMap.toMatrix' (nuLin fr) := by
      rw [coe_spinMatrix, hsg, hg]
      have := La_transvection_eq fr c
      rw [show ((g : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) →ₗ[F] (ι → F)) = 1 + c • nuLin fr from this,
        map_add, map_smul, LinearMap.toMatrix'_one]
    have hMA : ((spinMatrix Q s : GL ι F) : Matrix ι ι F) * (A : Matrix ι ι F) =
        (A : Matrix ι ι F) * (((spinMatrix Q s : GL ι F) : Matrix ι ι F).map φ) := by
      set G := glFieldEquiv ι φ (spinMatrix Q s) with hG
      have h1 : spinMatrix Q s * A = A * G := by
        calc spinMatrix Q s * A = (A * G * A⁻¹) * A := by rw [← hm]
          _ = A * G := by group
      have h2' := congrArg (fun g : GL ι F => (g : Matrix ι ι F)) h1
      simp only [Units.val_mul] at h2'
      have hGm : (G : Matrix ι ι F) = ((spinMatrix Q s : GL ι F) : Matrix ι ι F).map φ := by
        ext i j
        exact glFieldEquiv_entry ι φ _ i j
      rw [hGm] at h2'
      exact h2'
    rw [hM] at hMA
    exact hMA.symm
  subst hφ
  have hmat' : ∀ x, spinMatrix Q (α x) = A * spinMatrix Q x * A⁻¹ := by
    intro x
    rw [hmat x, glFieldEquiv_refl]
  set a : (ι → F) ≃ₗ[F] (ι → F) := glLin A with ha
  have hθα : ∀ x, θ (α x) = a * θ x * a⁻¹ := by
    intro x
    rw [← glLin_spinMatrix, hmat', map_mul, map_mul, map_inv, glLin_spinMatrix]
  have hcomm : ∀ g ∈ P, a * g = g * a := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := hlift2 g hg
    have h1 := hθα s
    rw [hfix s hs] at h1
    calc a * θ s = (a * θ s * a⁻¹) * a := by group
      _ = θ s * a := by rw [← h1]
  have hsim' : ∀ v, Q (a v) = μ * Q v := by
    intro v
    have := hsim v
    simpa [ha, glLin_apply] using this
  exact ⟨α, a, μ, hαψ, hθα, hcomm, hsim'⟩

theorem exists_sq_scalar (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hV : 3 ≤ Module.finrank F (ι → F)) {ψ : spinGroup Q →* H}
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) (σ : ↥ψ.range ≃* ↥ψ.range)
    (hσ2 : ∀ y, σ (σ y) = y) (α : spinGroup Q ≃* spinGroup Q) (a : (ι → F) ≃ₗ[F] (ι → F))
    (μ : Fˣ) (hαψ : ∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x))
    (hθα : ∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹)
    (hsim : ∀ v, Q (a v) = μ * Q v) :
    ∃ s : F, s ≠ 0 ∧ ∀ x, a (a x) = s • x := by
  classical
  set θ := spinAction Q with hθ
  let β : spinGroup Q ≃* spinGroup Q := α.trans α
  have hβ : ∀ g, β g = α (α g) := fun g => rfl
  have hψβ : ∀ g, ψ (β g) = ψ g := by
    intro g
    have h1 : ψ.rangeRestrict (β g) = ψ.rangeRestrict g := by
      rw [hβ, hαψ, hαψ, hσ2]
    exact congrArg Subtype.val h1
  have hcent : ∀ s ∈ (⊤ : Subgroup (spinGroup Q)), s⁻¹ * β s ∈ Subgroup.center (spinGroup Q) := by
    intro s _
    apply hψ
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψβ, inv_mul_cancel]
  have hperf : ⁅(⊤ : Subgroup (spinGroup Q)), ⊤⁆ = ⊤ := Group.isPerfect_def.1 inferInstance
  have hfix : ∀ g, β g = g := fun g =>
    alpha_fixes_commutators β hcent g (by rw [hperf]; exact Subgroup.mem_top g)
  have hcomm : ∀ g : spinGroup Q, a * a * θ g = θ g * (a * a) := by
    intro g
    have h1 : θ g = a * (a * θ g * a⁻¹) * a⁻¹ := by
      conv_lhs => rw [← hfix g, hβ, hθα, hθα]
    calc a * a * θ g = (a * (a * θ g * a⁻¹) * a⁻¹) * (a * a) := by group
      _ = θ g * (a * a) := by rw [← h1]
  have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
  let g₀ : (ι → F) ≃ₗ[F] (ι → F) := LinearEquiv.smulOfUnit μ⁻¹ * (a * a)
  have hg₀ : ∀ x, g₀ x = ((μ⁻¹ : Fˣ) : F) • a (a x) := fun x => rfl
  have hiso : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    rw [hg₀, map_smul_eq_sq, hsim, hsim]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  have hcommE : ∀ h ∈ elemOn Q ⊤, g₀ * h = h * g₀ := by
    intro h hh
    have hh' : h ∈ θ.range := by
      rw [hrange]
      exact elemOn_le_elementaryGroup hh
    obtain ⟨g, rfl⟩ := hh'
    refine LinearEquiv.ext fun x => ?_
    have := LinearEquiv.congr_fun (hcomm g) x
    simp only [LinearEquiv.mul_apply] at this ⊢
    rw [hg₀, hg₀, map_smul, this]
  have h3 : 3 ≤ Module.finrank F ↥(⊤ : Submodule F (ι → F)) := by
    rw [finrank_top]
    exact hV
  obtain ⟨c, hc⟩ := exists_smul_of_commute_elemOn hodd (polarNondegOn_top hQ) h3 hiso
    (fun x => by simp) hcommE
  have hs : ∀ x, a (a x) = ((μ : F) * c) • x := by
    intro x
    have h1 := hc x (Submodule.mem_top)
    rw [hg₀] at h1
    have h2 : a (a x) = (μ : F) • c • x := by
      rw [← h1, smul_smul, Units.mul_inv, one_smul]
    rw [h2, smul_smul]
  refine ⟨(μ : F) * c, ?_, hs⟩
  intro h0
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : ι → F)
  apply hx
  have h1 := hs x
  rw [h0, zero_smul] at h1
  have h2 : a x = 0 := a.injective (by rw [h1, map_zero])
  exact a.injective (by rw [h2, map_zero])

end Lift

section Plane

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem scalar_on_plane [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (fr : Frame Q) (hperp3 : 3 ≤ Module.finrank F fr.perp)
    (hW1 : ∀ P P' : HypPair (Q.restrict fr.perp), ¬ P.Orth P') (a : V ≃ₗ[F] V) (μ : Fˣ)
    (hsim : ∀ v, Q (a v) = μ * Q v) (hLa : ∀ g ∈ fr.La.range, a * g = g * a) {s : F}
    (hs : s ≠ 0) (ha2 : ∀ x, a (a x) = s • x) :
    ∃ c : F, (∀ Y, a (fr.incl Y) = c • fr.incl Y) ∧ ∀ x, fr.coords x = 0 → fr.coords (a x) = 0 := by
  have hg : ∀ (A : SL(2, F)) x, a.toLinearMap (fr.La A x) = fr.La A (a.toLinearMap x) := by
    intro A x
    have := LinearEquiv.congr_fun (hLa (fr.La A) ⟨A, rfl⟩) x
    simpa using this
  obtain ⟨h, hh, hperp⟩ := CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_mulRight_of_commute_La
    fr a.toLinearMap hg
  have e1 : a (fr.incl 1) = fr.incl h := by simpa using hh 1
  have hhh : h * h = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 := ha2 (fr.incl 1)
    rw [e1] at h1
    have h2 : a (fr.incl h) = fr.incl (h * h) := hh h
    rw [h2, ← map_smul] at h1
    exact fr.incl_injective (by simpa using h1)
  have hdet : h.det = μ := by
    have := hsim (fr.incl 1)
    rw [e1, Frame.Q_incl, Frame.Q_incl, Matrix.det_one, mul_one] at this
    exact this
  rcases mat_sq_cases h hhh with ⟨c, hc⟩ | hneg
  · refine ⟨c, fun Y => ?_, hperp⟩
    have := hh Y
    rw [hc, mul_smul_comm, mul_one, map_smul] at this
    exact this
  · exfalso
    have hμs : (μ : F) = -s := by rw [← hdet, hneg]
    have hmem : ∀ x ∈ fr.perp, a x ∈ fr.perp := fun x hx =>
      (Frame.mem_perp_iff fr).mpr (hperp x ((Frame.mem_perp_iff fr).mp hx))
    refine false_of_skew hodd (Orth15.two_ne_zero_of_odd_card hodd)
      (nondegenerate_polarBilin_restrict
        (CFSG.ClassicalInvolution.ModelFacts.polarNondegOn_perp hQ fr)) hW1 hperp3
      ((a : V →ₗ[F] V).restrict hmem) hs (fun y => Subtype.ext (ha2 y)) (fun y => ?_)
    show Q (a y) = _
    rw [hsim, hμs]
    rfl

end Plane

section Inner

variable {S H : Type} [Group S] [Group H]

theorem innerHom_apply_apply (ψ : S →* H) (r : S) (ℓ : ↥ψ.range) :
    ((innerHom ψ r : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) ℓ =
      ψ.rangeRestrict r * ℓ * (ψ.rangeRestrict r)⁻¹ := by
  apply Subtype.ext
  rw [innerHom_apply, toInducedAutOn_apply_coe]
  rfl

theorem conj_commute_of_commute (ψ : S →* H) (v : ↥(inducedAutOn ψ.range)) {r : S}
    (h : v * innerHom ψ r = innerHom ψ r * v) (ℓ : ↥ψ.range) :
    (v : MulAut ↥ψ.range) (ψ.rangeRestrict r * ℓ * (ψ.rangeRestrict r)⁻¹) =
      ψ.rangeRestrict r * (v : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict r)⁻¹ := by
  have h1 := congrArg (fun g : ↥(inducedAutOn ψ.range) => ((g : MulAut ↥ψ.range) ℓ : ↥ψ.range)) h
  simp only [Subgroup.coe_mul, MulAut.mul_apply, innerHom_apply_apply] at h1
  exact h1

theorem commute_of_fixes (ψ : S →* H) (v : ↥(inducedAutOn ψ.range)) {r : S}
    (h : (v : MulAut ↥ψ.range) (ψ.rangeRestrict r) = ψ.rangeRestrict r) :
    v * innerHom ψ r = innerHom ψ r * v := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro ℓ
  show (v : MulAut ↥ψ.range) (((innerHom ψ r : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) ℓ) =
    ((innerHom ψ r : ↥(inducedAutOn ψ.range)) : MulAut ↥ψ.range) ((v : MulAut ↥ψ.range) ℓ)
  rw [innerHom_apply_apply, innerHom_apply_apply, map_mul, map_mul, map_inv, h]

theorem mul_self_apply (ψ : S →* H) (v : ↥(inducedAutOn ψ.range)) (hv2 : v * v = 1)
    (y : ↥ψ.range) : (v : MulAut ↥ψ.range) ((v : MulAut ↥ψ.range) y) = y := by
  have h1 := congrArg (fun g : ↥(inducedAutOn ψ.range) => ((g : MulAut ↥ψ.range) y : ↥ψ.range)) hv2
  simpa only [Subgroup.coe_mul, MulAut.mul_apply, Subgroup.coe_one, MulAut.one_apply] using h1

end Inner

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem sigma_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 3 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hperpOK : ∀ fr : Frame Q, 3 ≤ Module.finrank F fr.perp ∧
      ∀ P P' : HypPair (Q.restrict fr.perp), ¬ P.Orth P')
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hxx : x' * x⁻¹ ∈ Subgroup.center (spinGroup Q)) {ψ : spinGroup Q →* H}
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) (hlift : LiftSim Q ψ)
    (v : ↥(inducedAutOn ψ.range)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * innerHom ψ r = innerHom ψ r * v) :
    ∀ r ∈ R', v * innerHom ψ r = innerHom ψ r * v := by
  classical
  set θ := spinAction Q with hθ
  have hkerθ : θ.ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hmk : QuotientGroup.mk' (Subgroup.center (spinGroup Q)) x =
      QuotientGroup.mk' (Subgroup.center (spinGroup Q)) x' := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 := Subgroup.mem_center_iff.mp hxx x⁻¹
    have h2 : x⁻¹ * x' = x' * x⁻¹ := mul_right_cancel (by rw [mul_assoc, h1, mul_assoc])
    rw [h2]
    exact hxx
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨fr, hfrR, hfrR', -, -⟩ := swap_of_twin_pair hodd hrange hZ hproj hRp hR'p hR hR' hinj
    hinj' hne hx hx2 hx1 hx' hx'2 hx'1 (QuotientGroup.mk' (Subgroup.center (spinGroup Q)))
    (by rw [QuotientGroup.ker_mk']) hmk
  set σ : ↥ψ.range ≃* ↥ψ.range := (v : MulAut ↥ψ.range) with hσ
  have hσ2 : ∀ y, σ (σ y) = y := mul_self_apply ψ v hv2
  have hcentral : ∀ z ∈ Subgroup.center (spinGroup Q), ∀ ℓ : ↥ψ.range,
      ψ.rangeRestrict z * ℓ = ℓ * ψ.rangeRestrict z := by
    intro z hz ℓ
    obtain ⟨y, rfl⟩ := MonoidHom.rangeRestrict_surjective ψ ℓ
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  have hσLa : ∀ s : spinGroup Q, θ s ∈ fr.La.range → ∀ ℓ : ↥ψ.range,
      σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    rw [← hfrR] at hs
    obtain ⟨r, hr, hrs⟩ := hs
    have hz : r⁻¹ * s ∈ Subgroup.center (spinGroup Q) := by
      apply hkerθ
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrs, inv_mul_cancel]
    have e : ψ.rangeRestrict s = ψ.rangeRestrict r * ψ.rangeRestrict (r⁻¹ * s) := by
      rw [← map_mul]
      congr 1
      group
    have hconj : ∀ m : ↥ψ.range, ψ.rangeRestrict s * m * (ψ.rangeRestrict s)⁻¹ =
        ψ.rangeRestrict r * m * (ψ.rangeRestrict r)⁻¹ := by
      intro m
      have hzc := hcentral _ hz m
      have h1 : ψ.rangeRestrict (r⁻¹ * s) * m * (ψ.rangeRestrict (r⁻¹ * s))⁻¹ = m := by
        rw [hzc]
        group
      calc ψ.rangeRestrict s * m * (ψ.rangeRestrict s)⁻¹
          = ψ.rangeRestrict r * (ψ.rangeRestrict (r⁻¹ * s) * m *
            (ψ.rangeRestrict (r⁻¹ * s))⁻¹) * (ψ.rangeRestrict r)⁻¹ := by
            rw [e]
            group
        _ = ψ.rangeRestrict r * m * (ψ.rangeRestrict r)⁻¹ := by rw [h1]
    rw [hconj, hconj]
    exact conj_commute_of_commute ψ v (hvR r hr) ℓ
  obtain ⟨α, a, μ, hαψ, hθα, hcomm, hsim⟩ := exists_aut_of_centralizing_La hodd h5 hrange fr hψ σ
    (hlift σ) hσLa
  obtain ⟨s, hs0, hs2⟩ := exists_sq_scalar hodd hQ hrange hV hψ σ hσ2 α a μ hαψ hθα hsim
  obtain ⟨hp3, hW1⟩ := hperpOK fr
  obtain ⟨c, hc, hperp⟩ := scalar_on_plane hodd hQ fr hp3 hW1 a μ hsim hcomm hs0 hs2
  have hcommR' : ∀ g ∈ fr.swap.La.range, a * g = g * a := by
    rintro _ ⟨B, rfl⟩
    exact LinearEquiv.ext fun x => comm_swap_of_scalar fr a.toLinearMap c hc hperp B x
  have hcent' : ∀ s ∈ R', s⁻¹ * α s ∈ Subgroup.center (spinGroup Q) := by
    intro s hs
    apply hkerθ
    have hmem : θ s ∈ fr.swap.La.range := by
      rw [← hfrR']
      exact Subgroup.mem_map_of_mem _ hs
    have h1 := hθα s
    have h2 : a * θ s * a⁻¹ = θ s := by rw [hcommR' _ hmem]; group
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, h2, inv_mul_cancel]
  have hfix := alpha_fixes_commutators α hcent'
  intro r hr
  apply commute_of_fixes
  rw [← hαψ, hfix r (hR'p hr)]

end Main

end CFSG.ClassicalInvolution.Asc77.SCV
