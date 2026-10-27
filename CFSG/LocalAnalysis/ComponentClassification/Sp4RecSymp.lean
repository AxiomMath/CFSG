module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSympLift
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpWitness
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGL

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open LinearMap (BilinForm)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem eq_zero_of_eq_neg' {W : Type*} [AddCommGroup W] [Module K W] (h2 : (2 : K) ≠ 0)
    {v : W} (h : v = -v) : v = 0 := by
  have h1 : (2 : K) • v = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    exact neg_add_cancel v
  exact (smul_eq_zero.mp h1).resolve_left h2

theorem eq_of_smul_eq {W : Type*} [AddCommGroup W] [Module K W] {v : W} (hv : v ≠ 0) {a b : K}
    (h : a • v = b • v) : a = b := by
  have h1 : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hv)

theorem false_of_extra_involution [Finite K] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {B : BilinForm K V}
    {g u : isometryGroup B} {K₁ K₂ : Subgroup (projectiveSymplectic B)}
    (hc : PairConfig _ (QuotientGroup.mk' (scalarSigns B) g) K₁ K₂) (hu : u * u = 1) {l : K}
    {v₁ v₂ w : V} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hw : w ≠ 0) (hu₁ : u.val v₁ = -v₁)
    (hu₂ : u.val v₂ = v₂) (huw : u.val w = w) (hg₁ : g.val v₁ = l • v₁)
    (hg₂ : g.val v₂ = l • v₂)
    (hmem : QuotientGroup.mk' (scalarSigns B) u ∈ K₁ ∨
      QuotientGroup.mk' (scalarSigns B) u ∈ K₂) : False := by
  set π := QuotientGroup.mk' (scalarSigns B)
  have hsq : π u ^ 2 = 1 := by rw [← map_pow, pow_two, hu, map_one]
  have hne : π u ≠ 1 := by
    intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_scalarSigns_iff] at h
    rcases h with rfl | rfl
    · exact hv₁ (eq_zero_of_eq_neg' h2 hu₁)
    · exact hw (eq_zero_of_eq_neg' h2 huw.symm)
  have hord : orderOf (π u) = 2 := orderOf_eq_prime hsq hne
  have hux : π u = π g :=
    hmem.elim (fun h => hc.involution_K _ h hord) fun h => hc.involution_K' _ h hord
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    mem_scalarSigns_iff] at hux
  have hl : ∀ c : K, c • v₁ = -v₁ → c • v₂ = v₂ → False := by
    intro c h₁ h₂
    have e₁ : c = -1 := eq_of_smul_eq hv₁ (h₁.trans (neg_one_smul K v₁).symm)
    have e₂ : c = 1 := eq_of_smul_eq hv₂ (h₂.trans (one_smul K v₂).symm)
    apply h2
    have : (1 : K) = -1 := e₂.symm.trans e₁
    linear_combination this
  rcases hux with h | h
  · have hg : g = u := (inv_mul_eq_one.mp h).symm
    subst hg
    exact hl l (hg₁.symm.trans hu₁) (hg₂.symm.trans hu₂)
  · have hg : g = u * negIsometry B := by rw [← h, mul_inv_cancel_left]
    have hgv : ∀ v, g.val v = -(u.val v) := fun v => by
      rw [hg]
      change u.val (-v) = -(u.val v)
      exact map_neg u.val v
    refine hl (-l) ?_ ?_
    · rw [neg_smul, ← hg₁, hgv, hu₁, neg_neg]
    · rw [neg_smul, ← hg₂, hgv, hu₂, neg_neg]

theorem exists_plane_involution {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {C : BilinForm K W} (hC : C.IsAlt) (hnd : C.Nondegenerate) (hW : 4 ≤ finrank K W) :
    ∃ t : sesqUnitaryGroup C, t * t = 1 ∧ ∃ v₁ v₂ : W, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧
      ((t : LinearMap.GeneralLinearGroup K W) : Module.End K W) v₁ = -v₁ ∧
      ((t : LinearMap.GeneralLinearGroup K W) : Module.End K W) v₂ = v₂ := by
  obtain ⟨m, b, hm, h11, -, h12⟩ := exists_blueprint_symplectic_basis C hC hnd
  have hm2 : 2 ≤ m := by omega
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  have hi : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have hu : C (b (Sum.inl i₀)) (b (Sum.inr i₀)) = 1 := by rw [h12]; simp
  set τ := OddClassSelector.planeInvolution hC hu
  have hτ : ∀ v, τ (τ v) = v := OddClassSelector.planeMap_involutive hC hu
  have hmem : LinearMap.GeneralLinearGroup.ofLinearEquiv τ ∈ sesqUnitaryGroup C := fun x y =>
    (mem_isometryGroup_iff C τ).mp (OddClassSelector.planeInvolution_mem hC hu) x y
  refine ⟨⟨_, hmem⟩, ?_, b (Sum.inl i₀), b (Sum.inl i₁), b.ne_zero _, b.ne_zero _, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact hτ v
  · change τ _ = _
    rw [OddClassSelector.planeInvolution_apply, hu, hC.self_eq_zero, one_smul, zero_smul,
      sub_zero, two_smul]
    abel
  · change τ _ = _
    rw [OddClassSelector.planeInvolution_apply, h11, h12]
    simp [hi]

theorem false_of_split_factor [Finite K] [FiniteDimensional K V] (hodd : Odd (Nat.card K))
    {B : BilinForm K V} {g : isometryGroup B} {K₁ K₂ : Subgroup (projectiveSymplectic B)}
    (hc : PairConfig _ (QuotientGroup.mk' (scalarSigns B) g) K₁ K₂) {X : Type*} [Group X]
    [Finite X] (ι : X →* isometryGroup B) {M₁ M₂ : Subgroup X} (hM₁ : IsPComponent 2 M₁)
    (hM₂ : IsPComponent 2 M₂) (hne : M₁ ≠ M₂)
    (hK₁ : ∀ u ∈ M₁, QuotientGroup.mk' (scalarSigns B) (ι u) ∈ K₁)
    (hK₂ : ∀ u ∈ M₂, QuotientGroup.mk' (scalarSigns B) (ι u) ∈ K₂) {W₁ W₂ : Submodule K V}
    {C₁ : BilinForm K W₁} {C₂ : BilinForm K W₂} (hC₁ : C₁.IsAlt) (hnd₁ : C₁.Nondegenerate)
    (hC₂ : C₂.IsAlt) (hnd₂ : C₂.Nondegenerate) (hW₁ : 4 ≤ finrank K W₁) (hW₂ : W₂ ≠ ⊥)
    (E : X ≃* sesqUnitaryGroup C₁ × sesqUnitaryGroup C₂)
    (hact₁ : ∀ (y : X) (v : W₁), (ι y).val v =
      ((((E y).1 : LinearMap.GeneralLinearGroup K W₁) : Module.End K W₁) v : W₁))
    (hact₂ : ∀ (y : X) (w : W₂), (ι y).val w =
      ((((E y).2 : LinearMap.GeneralLinearGroup K W₂) : Module.End K W₂) w : W₂))
    {l : K} (hg : ∀ v ∈ W₁, g.val v = l • v) : False := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have hW₂' : 2 ≤ finrank K W₂ :=
    CatalogueBSymplecticB.two_le_finrank_of_ne_bot hW₂ C₂ hC₂ hnd₂
  have hu₂ : ∀ J₁ J₂ : Subgroup (sesqUnitaryGroup C₂), IsPComponent 2 J₁ → IsPComponent 2 J₂ →
      J₁ = J₂ := fun J₁ J₂ k₁ k₂ => (sp_pComponent_eq hodd hC₂ hnd₂ hW₂' k₁).1 J₂ k₂
  have hN₁ := CatalogueBAlternating.pComponent_map_equiv 2 E _ hM₁
  have hN₂ := CatalogueBAlternating.pComponent_map_equiv 2 E _ hM₂
  obtain ⟨M, hMK, hMtop⟩ : ∃ M : Subgroup X,
      (∀ u ∈ M, QuotientGroup.mk' (scalarSigns B) (ι u) ∈ K₁ ∨
        QuotientGroup.mk' (scalarSigns B) (ι u) ∈ K₂) ∧
      M.map E.toMonoidHom = (⊤ : Subgroup (sesqUnitaryGroup C₁)).prod ⊥ := by
    have hleft : ∀ M : Subgroup X, IsPComponent 2 (M.map E.toMonoidHom) →
        M.map E.toMonoidHom = ((M.map E.toMonoidHom).map (MonoidHom.fst _ _)).prod ⊥ →
        M.map E.toMonoidHom = (⊤ : Subgroup (sesqUnitaryGroup C₁)).prod ⊥ := by
      intro M hN hl
      rw [hl, (sp_pComponent_eq hodd hC₁ hnd₁ (by omega) (isPComponent_fst hN hl)).2 hW₁]
    rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2 _ hN₁ with
      hl₁ | hr₁
    · exact ⟨M₁, fun u hu => Or.inl (hK₁ u hu), hleft M₁ hN₁ hl₁⟩
    rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2 _ hN₂ with
      hl₂ | hr₂
    · exact ⟨M₂, fun u hu => Or.inr (hK₂ u hu), hleft M₂ hN₂ hl₂⟩
    exfalso
    have h12 : M₁.map E.toMonoidHom = M₂.map E.toMonoidHom := by
      rw [hr₁, hr₂, hu₂ _ _ (isPComponent_snd hN₁ hr₁) (isPComponent_snd hN₂ hr₂)]
    exact hne (map_injective E.injective h12)
  obtain ⟨t, ht, v₁, v₂, hv₁, hv₂, htv₁, htv₂⟩ := exists_plane_involution hC₁ hnd₁ hW₁
  set u := E.symm (t, 1) with hu
  have huM : u ∈ M := by
    have h1 : (t, (1 : sesqUnitaryGroup C₂)) ∈ M.map E.toMonoidHom := by
      rw [hMtop]
      exact ⟨mem_top t, one_mem _⟩
    rw [mem_map_equiv] at h1
    exact h1
  have huu : ι u * ι u = 1 := by
    rw [← map_mul, hu, ← map_mul, Prod.mk_mul_mk, ht, one_mul, ← Prod.one_eq_mk, map_one,
      map_one]
  have hEu : E u = (t, 1) := by rw [hu, MulEquiv.apply_symm_apply]
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₂
  refine false_of_extra_involution h2 hc huu (l := l) (v₁ := v₁) (v₂ := v₂) (w := w)
    (fun h => hv₁ (Subtype.ext h)) (fun h => hv₂ (Subtype.ext h)) hw0 ?_ ?_ ?_
    (hg _ v₁.2) (hg _ v₂.2) (hMK u huM)
  · rw [hact₁, hEu]
    exact congrArg Subtype.val htv₁
  · rw [hact₁, hEu]
    exact congrArg Subtype.val htv₂
  · have := hact₂ u ⟨w, hwW⟩
    rw [hEu] at this
    exact this

theorem herm_centralizer_pComponent_eq [Finite K] [FiniteDimensional K V]
    (hodd : Odd (Nat.card K)) (B : BilinForm K V) (A : LinearMap.GeneralLinearGroup K V)
    (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1)
    (hF : IsField (scalarSquareField (A : Module.End K V)))
    (hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))))
    (hdim : 3 ≤ Module.finrank (scalarSquareField (A : Module.End K V)) V)
    (bar : scalarSquareField (A : Module.End K V) →+* scalarSquareField (A : Module.End K V))
    (hbar : ∀ (x : scalarSquareField (A : Module.End K V)) (a b : K),
      (x : Module.End K V) = a • 1 + b • A → (bar x : Module.End K V) = a • 1 - b • A)
    (hbarbar : ∀ x, bar (bar x) = x)
    (h : V →ₛₗ[bar] V →ₗ[scalarSquareField (A : Module.End K V)]
      scalarSquareField (A : Module.End K V))
    (hsymm : h.IsSymm) (hsep : h.SeparatingLeft)
    (hiff : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ similitudeCentralizer B A ↔
      g ∈ Subgroup.centralizer {A} ∧
        ∀ v w, h ((g : Module.End K V) v) ((g : Module.End K V) w) = h v w)
    {L₁ L₂ : Subgroup (symplecticOperatorCentralizer B A)} (h₁ : IsPComponent 2 L₁)
    (h₂ : IsPComponent 2 L₂) : L₁ = L₂ := by
  let : Field (scalarSquareField (A : Module.End K V)) := hF.toField
  have := finite_of_odd_card hEodd
  have : Module.Finite (scalarSquareField (A : Module.End K V)) V :=
    evaluationModule_finite (A : Module.End K V)
  let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
  let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[scalarSquareField (A : Module.End K V)]
    scalarSquareField (A : Module.End K V) := h
  have hnd : h'.Nondegenerate :=
    ⟨hsep, fun y hy => hsep y fun x => by
      rw [← hsymm.eq x y]
      exact (congrArg bar (hy x)).trans (map_zero bar)⟩
  have hsigma : sigma ^ 2 = 1 := RingEquiv.ext hbarbar
  have hne : sigma ≠ 1 := by
    intro heq
    let x : scalarSquareField (A : Module.End K V) :=
      ⟨A, Algebra.self_mem_adjoin_singleton K _⟩
    have hx := hbar x 0 1 (by simp only [zero_smul, zero_add, one_smul, x])
    have hfix : bar x = x := DFunLike.congr_fun heq x
    rw [hfix] at hx
    simp only [zero_smul, zero_sub, one_smul, x] at hx
    have h2 := two_ne_zero_of_odd_natCard hodd
    have hA : (2 : K) • (A : Module.End K V) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hx]
      exact add_neg_cancel _
    apply hAns 0
    rw [zero_smul]
    calc (A : Module.End K V) = (2 : K)⁻¹ • ((2 : K) • (A : Module.End K V)) := by
          rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = 0 := by rw [hA, smul_zero]
  have hq2 : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield
      (scalarSquareField (A : Module.End K V)) sigma) ≠ 2 := by
    intro heq
    have hfodd := CatalogueBOrthogonalFieldFixed.subfield_card_odd hEodd
      (CatalogueBLinearTwoDescent.fixedSubfield (scalarSquareField (A : Module.End K V)) sigma)
    rw [heq] at hfodd
    exact Nat.not_even_iff_odd.mpr hfodd even_two
  set e := evaluationIsometryEquiv B A (CatalogueBUnitaryIsometry.isometryGroup h')
    (fun φ => ∀ v w, h (φ v) (φ w) = h v w)
    (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h') hiff
  have hall := (CatalogueBUnitaryIsometry.isometry_all_dimensions_nonsmall h' hsymm hnd hsigma
    hne (by omega) hq2 (by omega) (fun hpq => by
      have := congrArg Prod.fst hpq
      simp only at this
      omega)).2 2 Nat.prime_two
  have e₁ := (hall _ (CatalogueBAlternating.pComponent_map_equiv 2 e _ h₁)).1
  have e₂ := (hall _ (CatalogueBAlternating.pComponent_map_equiv 2 e _ h₂)).1
  exact map_injective e.injective (e₁.trans e₂.symm)

end CFSG.ComponentClassification.Sp4Rec
