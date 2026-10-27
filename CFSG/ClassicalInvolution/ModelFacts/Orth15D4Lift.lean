module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBHigherLinearField Matrix
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

@[expose] def LiftSimAt (Q : QuadraticForm F (ι → F)) {H : Type} [Group H]
    (ψ : spinGroup Q →* H) (σ : ↥ψ.range ≃* ↥ψ.range) : Prop :=
  ∃ α : spinGroup Q ≃* spinGroup Q,
    (∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x)) ∧
      ∃ (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ),
        (∀ v : ι → F, Q (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q v)) ∧
          ∀ x, spinMatrix Q (α x) = A * glFieldEquiv ι φ (spinMatrix Q x) * A⁻¹

omit [Finite F] in
theorem liftSim_iff_forall_liftSimAt (ψ : spinGroup Q →* H) :
    LiftSim Q ψ ↔ ∀ σ : ↥ψ.range ≃* ↥ψ.range, LiftSimAt Q ψ σ := Iff.rfl

@[expose] def LiftSimFr (Q : QuadraticForm F (ι → F)) {H : Type} [Group H]
    (ψ : spinGroup Q →* H) : Prop :=
  ∀ (fr : Frame Q) (σ : ↥ψ.range ≃* ↥ψ.range),
    (∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹) → LiftSimAt Q ψ σ

omit [Finite F] in
theorem LiftSim.liftSimFr {ψ : spinGroup Q →* H} (h : LiftSim Q ψ) : LiftSimFr Q ψ :=
  fun _ σ _ => h σ

theorem exists_aut_of_centralizing_at (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    [Group.IsPerfect (spinGroup Q)] (hrange : (spinAction Q).range = elementaryGroup Q)
    (fr : Frame Q) {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (σ : ↥ψ.range ≃* ↥ψ.range) (hlift : LiftSimAt Q ψ σ)
    (hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹) :
    ∃ (α : spinGroup Q ≃* spinGroup Q) (a : (ι → F) ≃ₗ[F] (ι → F)) (c : F),
      (∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x)) ∧
      (∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹) ∧
      (∀ x ∈ fr.span, a x = c • x) ∧ (∃ μ : Fˣ, (μ : F) = c ^ 2 ∧
        ∀ v, Q (a v) = μ * Q v) := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set θ := spinAction Q with hθ
  obtain ⟨α, hαψ, A, φ, μ, hsim, hmat⟩ := hlift
  set P : Subgroup ((ι → F) ≃ₗ[F] (ι → F)) := fr.La.range ⊔ fr.swap.La.range with hP
  have hPE : P ≤ θ.range := by
    rw [hrange]
    exact sup_le (fun g ⟨A, hA⟩ => hA ▸ fr.La_mem_elementaryGroup A)
      (fun g ⟨A, hA⟩ => hA ▸ fr.swap.La_mem_elementaryGroup A)
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
    refine mem_center_of_commutators_central fun t => hψ ?_
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
  have hL₂ : ⁅fr.swap.La.range, fr.swap.La.range⁆ = fr.swap.La.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range fr.swap.La)
  have hPperf : ⁅P, P⁆ = P := by
    refine le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy => ?_) (sup_le ?_ ?_)
    · simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    · calc fr.La.range = ⁅fr.La.range, fr.La.range⁆ := hL₁.symm
        _ ≤ ⁅P, P⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc fr.swap.La.range = ⁅fr.swap.La.range, fr.swap.La.range⁆ := hL₂.symm
        _ ≤ ⁅P, P⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  have hlift2 := exists_lift_commutator θ hPE hPperf
  have hN : (LinearMap.toMatrix' (nuLin fr)) ≠ 0 := by
    intro h0
    exact nuLin_ne_zero fr ((LinearMap.toMatrix').injective (by rw [h0, map_zero]))
  have hφ : φ = RingEquiv.refl F := by
    refine ringEquiv_eq_refl_of_commute (LinearMap.toMatrix' (nuLin fr)) hN A φ fun c => ?_
    set g := fr.La (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c)
      with hg
    have hgP : g ∈ P := Subgroup.mem_sup_left (⟨_, rfl⟩ : g ∈ fr.La.range)
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
  obtain ⟨⟨c, hc⟩, -⟩ := scalar_on_span_of_commute h2 fr
    (fun A₀ => hcomm _ (Subgroup.mem_sup_left (⟨A₀, rfl⟩ : fr.La A₀ ∈ fr.La.range)))
    (fun B₀ => hcomm _ (Subgroup.mem_sup_right (⟨B₀, rfl⟩ : fr.swap.La B₀ ∈ fr.swap.La.range)))
  have hsim' : ∀ v, Q (a v) = μ * Q v := by
    intro v
    have := hsim v
    simpa [ha, glLin_apply] using this
  refine ⟨α, a, c, hαψ, hθα, hc, μ, ?_, hsim'⟩
  have hv := hsim' (fr.incl 1)
  rw [hc _ ⟨1, rfl⟩, QuadraticMap.map_smul, Frame.Q_incl, Matrix.det_one] at hv
  rw [pow_two]
  simpa using hv.symm

end Core

section Final

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem exists_isometry_of_centralizing_at (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    [Group.IsPerfect (spinGroup Q)] (hrange : (spinAction Q).range = elementaryGroup Q)
    (fr : Frame Q) {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (σ : ↥ψ.range ≃* ↥ψ.range) (hlift : LiftSimAt Q ψ σ)
    (hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹) :
    ∃ (α : spinGroup Q ≃* spinGroup Q) (w : (ι → F) ≃ₗ[F] (ι → F)),
      (∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x)) ∧
      w ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ x ∈ fr.span, w x = x) ∧
      ∀ x, spinAction Q (α x) = w * spinAction Q x * w⁻¹ := by
  classical
  set θ := spinAction Q with hθ
  obtain ⟨α, a, c, hαψ, hθα, hc, μ, hμc, hsim⟩ :=
    exists_aut_of_centralizing_at hodd h5 hrange fr hψ σ hlift hσ
  have hc0 : c ≠ 0 := by
    intro h0
    apply μ.ne_zero
    rw [hμc, h0]
    ring
  set sm : (ι → F) ≃ₗ[F] (ι → F) := LinearEquiv.smulOfNeZero F (ι → F) c hc0 with hsm_def
  set sm' : (ι → F) ≃ₗ[F] (ι → F) :=
    LinearEquiv.smulOfNeZero F (ι → F) c⁻¹ (inv_ne_zero hc0) with hsm'_def
  have hsm_comm : ∀ g : (ι → F) ≃ₗ[F] (ι → F), sm * g = g * sm := fun g => by
    ext x
    simp [sm]
  have hsm_inv : sm * sm' = 1 := by
    ext x
    simp [sm, sm', hc0]
  set w : (ι → F) ≃ₗ[F] (ι → F) := sm' * a with hw
  have ha : a = sm * w := by rw [hw, ← mul_assoc, hsm_inv, one_mul]
  have hwspan : ∀ x ∈ fr.span, w x = x := by
    intro x hx
    rw [hw, LinearEquiv.mul_apply, hc x hx]
    simp [sm', hc0]
  have hwiso : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    have h1 : w x = c⁻¹ • a x := by
      rw [hw, LinearEquiv.mul_apply]
      simp [sm']
    rw [h1, QuadraticMap.map_smul, hsim, hμc]
    simp only [smul_eq_mul]
    field_simp
  have hθw : ∀ x, θ (α x) = w * θ x * w⁻¹ := by
    intro x
    rw [hθα, ha, _root_.mul_inv_rev]
    calc sm * w * θ x * (w⁻¹ * sm⁻¹) = sm * (w * θ x * w⁻¹) * sm⁻¹ := by group
      _ = (w * θ x * w⁻¹) * sm * sm⁻¹ := by rw [hsm_comm]
      _ = w * θ x * w⁻¹ := by group
  exact ⟨α, w, hαψ, hwiso, hwspan, hθw⟩

theorem alphaOf_spin_frame_centralizer_eq_bot_at (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (fr : Frame Q) (hV : 7 ≤ Module.finrank F (ι → F))
    {ψ : spinGroup Q →* H} [Finite H] (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    {s₂ : spinGroup Q} (hs₂ : spinAction Q s₂ = fr.La (-1))
    (v : ↥(inducedAutOn ψ.range)) (hlift : LiftSimAt Q ψ (v : MulAut ↥ψ.range))
    (hv : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      v * toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ =
        toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ * v)
    (hy2 : v * v * (v * v) = 1) (hy1 : v * v ≠ 1)
    (hyz : v * v ≠ toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩, v * v} :
      Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h3 : 3 ≤ Module.finrank F (ι → F) := by omega
  obtain ⟨e, he, hker, hnorm, hcent⟩ := exists_hom_spin hodd hQ h3 hrange ψ hψ
  have : Finite ↥(inducedAutOn ψ.range) := inferInstance
  have := hnorm
  have hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * (v : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    have h := congrArg (fun g : ↥(inducedAutOn ψ.range) => ((g : MulAut ↥ψ.range) ℓ : ↥ψ.range))
      (hv s hs)
    exact Subtype.ext (congrArg Subtype.val h)
  obtain ⟨α, w, hαψ, hwiso, hwspan, hθw⟩ :=
    exists_isometry_of_centralizing_at hodd h5 hrange fr hψ (v : MulAut ↥ψ.range) hlift hσ
  have hy_mem : w * w ∈ elementaryGroup Q := sq_mem_of_frame hodd hQ fr hV hwiso
  have hspan_y : ∀ x ∈ fr.span, (w * w) x = x := fun x hx => by
    rw [LinearEquiv.mul_apply, hwspan x hx, hwspan x hx]
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift hrange α hy_mem hθw
  have hey : e ⟨w * w, hy_mem⟩ = v * v := e_sq_eq e he v α hαψ hy_mem hŷ hαα
  have hyy : w * w * (w * w) = 1 :=
    sq_eq_one_of_e e hker fr hy_mem hspan_y (by rw [hey]; exact hy2)
  have hyO : w * w ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hy_mem
  have hzmem : fr.La (-1) ∈ elementaryGroup Q := fr.La_mem_elementaryGroup (-1)
  have hez : e ⟨fr.La (-1), hzmem⟩ =
      toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩ := by
    have := he s₂ (by rw [hs₂]; exact hzmem)
    rw [← this]
    congr 1
    exact Subtype.ext hs₂.symm
  have hR : minusSp (w * w) ≠ ⊥ := by
    intro hbot
    apply hy1
    have h1 : w * w = 1 := eq_one_of_minusSp_eq_bot h2 hyy hbot
    have : (⟨w * w, hy_mem⟩ : ↥(elementaryGroup Q)) = 1 := Subtype.ext h1
    rw [this, map_one] at hey
    exact hey.symm
  have hW : plusSp (w * w) ⊓ fr.perp ≠ ⊥ := by
    intro hbot
    have hneg := mul_La_neg_one_eq_neg h2 fr hyO hyy hspan_y hbot
    have hnegmem : (LinearEquiv.neg F : (ι → F) ≃ₗ[F] (ι → F)) ∈ elementaryGroup Q := by
      rw [← hneg]
      exact mul_mem hy_mem hzmem
    have hecent : e ⟨LinearEquiv.neg F, hnegmem⟩ = 1 := by
      apply hcent
      rintro _ ⟨g, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext (LinearEquiv.ext fun x => ?_)
      simp
    have h1 : e ⟨(w * w) * fr.La (-1), mul_mem hy_mem hzmem⟩ =
        e ⟨w * w, hy_mem⟩ * e ⟨fr.La (-1), hzmem⟩ := by
      rw [← map_mul]
      rfl
    have h2' : e ⟨(w * w) * fr.La (-1), mul_mem hy_mem hzmem⟩ = 1 := by
      have : (⟨(w * w) * fr.La (-1), mul_mem hy_mem hzmem⟩ : ↥(elementaryGroup Q)) =
          ⟨LinearEquiv.neg F, hnegmem⟩ := Subtype.ext hneg
      rw [this, hecent]
    rw [h1, hey, hez] at h2'
    have hz2 : toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩ *
        toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩ = 1 := by
      rw [← hez, ← map_mul]
      have : (⟨fr.La (-1), hzmem⟩ * ⟨fr.La (-1), hzmem⟩ : ↥(elementaryGroup Q)) = 1 :=
        Subtype.ext fr.La_neg_one_mul_self
      rw [this, map_one]
    apply hyz
    exact (mul_eq_one_iff_eq_inv.mp h2').trans (inv_eq_of_mul_eq_one_left hz2)
  have key := alphaOf_frame_klein_eq_bot hodd h5 hQ fr hy_mem hyy hspan_y hV hR hW e hker hcent
  rw [hez, hey] at key
  exact key

end Final

section OuterPair

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)}

theorem alphaOf_spin_twin_pair_outer_ord (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hV : 7 ≤ Module.finrank F (ι → F))
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x') {H : Type} [Group H] [Finite H]
    {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hlift : LiftSimFr Q ψ) (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * spinInd ψ r = spinInd ψ r * v)
    (hvR' : ∀ r ∈ R', v * spinInd ψ r = spinInd ψ r * v) (hy2 : v * v * (v * v) = 1)
    (hy1 : v * v ≠ 1) (hyz : v * v ≠ spinInd ψ x) :
    alphaOf (Subgroup.closure ({spinInd ψ x, v * v} : Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨F₁, hF₁, hF₁', hθx, -⟩ := swap_of_twin_pair_ord hodd hRp hR'p hR hR' hinj hinj' hne hx
    hx2 hx1 hx' hx'2 hx'1 hord
  have hv' : ∀ s : spinGroup Q, spinAction Q s ∈ F₁.La.range ⊔ F₁.swap.La.range →
      v * toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ =
        toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ * v := by
    intro s hs
    rw [← hF₁, ← hF₁'] at hs
    exact commute_spinInd_of_mem_map_sup (ker_spinAction_le_center Q) ψ v hvR hvR' hs
  have hσ : ∀ s : spinGroup Q, spinAction Q s ∈ F₁.La.range ⊔ F₁.swap.La.range →
      ∀ ℓ : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * (v : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    have h := congrArg (fun g : ↥(inducedAutOn ψ.range) => ((g : MulAut ↥ψ.range) ℓ : ↥ψ.range))
      (hv' s hs)
    exact Subtype.ext (congrArg Subtype.val h)
  exact alphaOf_spin_frame_centralizer_eq_bot_at hodd h5 hQ hrange F₁ hV hψ hθx v
    (hlift F₁ (v : MulAut ↥ψ.range) hσ) hv' hy2 hy1 hyz

end OuterPair

end CFSG.ClassicalInvolution.G2D4Models.Twin
