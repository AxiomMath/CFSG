module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentUnitary
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryRestrictionScalarCentralizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal

open Module CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open TauCeti.QuadraticMap (orthogonalGroup)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_centralizer_equiv_sesqUnitary {E : Type} [Field E] [Module E V] {σ : E →+* E}
    {sigma : E ≃+* E} {h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E} {Hf : V →ₛₗ[σ] V →ₗ[E] E}
    (hHf : ∀ x y, Hf x y = h x y) (T : orthogonalGroup Q)
    (e : orthogonalOperatorCentralizer Q (T : V ≃ₗ[K] V).toLinearMap ≃*
      CatalogueBUnitaryIsometry.isometryGroup h)
    (he : ∀ (g : orthogonalOperatorCentralizer Q (T : V ≃ₗ[K] V).toLinearMap) (x : V),
      ((e g : CatalogueBUnitaryIsometry.isometryGroup h) : V ≃ₗ[E] V) x =
        ((g : orthogonalGroup Q) : V ≃ₗ[K] V) x) :
    ∃ e' : Subgroup.centralizer {T} ≃* sesqUnitaryGroup Hf,
      ∀ (x : Subgroup.centralizer {T}) (v : V),
        (((e' x : sesqUnitaryGroup Hf) : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) v =
          ((x : orthogonalGroup Q) : V ≃ₗ[K] V) v := by
  let iso : CatalogueBUnitaryIsometry.isometryGroup h ≃* sesqUnitaryGroup Hf :=
    { toFun := fun g => ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv
        (g : V ≃ₗ[E] V), fun x y => by
          change Hf ((g : V ≃ₗ[E] V) x) ((g : V ≃ₗ[E] V) y) = Hf x y
          rw [hHf, hHf]
          exact (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h _).mp g.2 x y⟩
      invFun := fun g => ⟨LinearMap.GeneralLinearGroup.toLinearEquiv
        (g : LinearMap.GeneralLinearGroup E V),
          (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h _).mpr fun x y => by
            rw [← hHf, ← hHf]
            exact mem_sesqUnitaryGroup.mp g.2 x y⟩
      left_inv := fun _ => Subtype.ext (LinearEquiv.ext fun _ => rfl)
      right_inv := fun _ => Subtype.ext (Units.ext (LinearMap.ext fun _ => rfl))
      map_mul' := fun _ _ => Subtype.ext (Units.ext (LinearMap.ext fun _ => rfl)) }
  refine ⟨(MulEquiv.subgroupCongr (centralizer_eq_orthogonalOperatorCentralizer T)).trans
    (e.trans iso), fun x v => ?_⟩
  exact he _ v

theorem exists_unitary_transfer {E : Type} [Field E] [Module E V] {σ : E →+* E}
    {sigma : E ≃+* E} {h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E} (hσ : ∀ z, sigma z = σ z)
    (hsymm : h.IsSymm) (hnd : h.Nondegenerate) (T : orthogonalGroup Q)
    (e : orthogonalOperatorCentralizer Q (T : V ≃ₗ[K] V).toLinearMap ≃*
      CatalogueBUnitaryIsometry.isometryGroup h)
    (he : ∀ (g : orthogonalOperatorCentralizer Q (T : V ≃ₗ[K] V).toLinearMap) (x : V),
      ((e g : CatalogueBUnitaryIsometry.isometryGroup h) : V ≃ₗ[E] V) x =
        ((g : orthogonalGroup Q) : V ≃ₗ[K] V) x) :
    ∃ Hf : V →ₛₗ[σ] V →ₗ[E] E, Hf.IsSymm ∧ Hf.Nondegenerate ∧
      ∃ e' : Subgroup.centralizer {T} ≃* sesqUnitaryGroup Hf,
        ∀ (x : Subgroup.centralizer {T}) (v : V),
          (((e' x : sesqUnitaryGroup Hf) : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) v =
            ((x : orthogonalGroup Q) : V ≃ₗ[K] V) v := by
  let Hf : V →ₛₗ[σ] V →ₗ[E] E := LinearMap.mk₂'ₛₗ σ (RingHom.id E) (fun x y => h x y)
    (fun x₁ x₂ y => by rw [map_add, LinearMap.add_apply])
    (fun c x y => by rw [LinearMap.map_smulₛₗ₂, ← hσ]; rfl)
    (fun x y₁ y₂ => by rw [map_add])
    (fun c x y => by rw [map_smul]; rfl)
  have hHf : ∀ x y, Hf x y = h x y := fun _ _ => rfl
  refine ⟨Hf, ⟨fun x y => ?_⟩, ⟨fun x hx => hnd.1 x fun y => ?_, fun y hy => hnd.2 y fun x => ?_⟩,
    exists_centralizer_equiv_sesqUnitary hHf T e he⟩
  · rw [hHf, hHf, ← hσ]
    exact hsymm.eq x y
  · rw [← hHf]
    exact hx y
  · rw [← hHf]
    exact hy x

theorem commute_of_commute_specialUnitary {E : Type} [Field E] [Module E V] {p f : ℕ}
    (hU : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V] (hm : 3 ≤ finrank E V)
    {Hf : V →ₛₗ[hU.bar] V →ₗ[E] E} (hH : Hf.IsSymm) (hnd : Hf.Nondegenerate)
    (hfixK : ∀ c : hU.fixedField, ∃ a : K, ∀ v : V, (c : E) • v = a • v)
    {R : Subgroup (orthogonalGroup Q)}
    (hRc : ∀ r ∈ R, ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∀ v,
      (r : V ≃ₗ[K] V) ((g : V →ₗ[E] V) v) = (g : V →ₗ[E] V) ((r : V ≃ₗ[K] V) v)) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  have hsmul : ∀ (g : V ≃ₗ[K] V) (c : hU.fixedField) (v : V), g (c • v) = c • g v := by
    intro g c v
    obtain ⟨a, ha⟩ := hfixK c
    change g ((c : E) • v) = (c : E) • g v
    rw [ha, ha, map_smul]
  let toF : (V ≃ₗ[K] V) → LinearMap.GeneralLinearGroup hU.fixedField V := fun g =>
    ⟨{ toFun := g
       map_add' := g.map_add
       map_smul' := hsmul g },
      { toFun := g.symm
        map_add' := g.symm.map_add
        map_smul' := hsmul g.symm },
      LinearMap.ext fun v => g.apply_symm_apply v,
      LinearMap.ext fun v => g.symm_apply_apply v⟩
  have hcent : ∀ r ∈ R, toF (r : V ≃ₗ[K] V) ∈ Subgroup.centralizer
      (((sesqSpecialUnitaryGroup Hf).map (glRestrictScalars hU.fixedField)) :
        Set (LinearMap.GeneralLinearGroup hU.fixedField V)) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    refine Units.ext (LinearMap.ext fun v => ?_)
    change (g : V →ₗ[E] V) ((r : V ≃ₗ[K] V) v) = (r : V ≃ₗ[K] V) ((g : V →ₗ[E] V) v)
    exact (hRc r hr g hg v).symm
  have hcomm := (natural_odd_unitary_restriction_scalar_centralizer hU hp hm hH hnd).2
  intro r₁ h₁ r₂ h₂
  have h3 := hcomm _ (hcent r₁ h₁) _ (hcent r₂ h₂)
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  exact LinearMap.congr_fun (congrArg Units.val h3) v

theorem unitary_case {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) [FiniteDimensional K V] (hd : 5 ≤ finrank K V)
    (hQ : Q.polarBilin.Nondegenerate) {T : orthogonalGroup Q}
    (hTns : ∀ c : K, (T : V ≃ₗ[K] V).toLinearMap ≠ c • 1)
    (hTT : ∀ x, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) x) = -x) (hns : ∀ l : K, l ^ 2 ≠ -1)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    {R : Subgroup (orthogonalGroup Q)}
    (hR : R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
      Subgroup (orthogonalGroup Q)) : Set (orthogonalGroup Q)))
    (hRp : ⁅R, R⁆ = R) : R = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hsq0 : ∀ x : V, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) x) = ((-1 : Kˣ) : K) • x := fun x => by
    rw [Units.val_neg, Units.val_one, neg_one_smul]
    exact hTT x
  have hsim0 : ∀ x y : V, Q.polarBilin ((T : V ≃ₗ[K] V) x) ((T : V ≃ₗ[K] V) y) =
      ((1 : Kˣ) : K) * Q.polarBilin x y := fun x y => by
    rw [Units.val_one, one_mul]
    exact polarBilin_map_of_mem T.2 x y
  have hnsq : ¬ IsSquare (((-1 : Kˣ) : K)) := by
    rintro ⟨c, hc⟩
    apply hns c
    rw [Units.val_neg, Units.val_one] at hc
    rw [hc, sq]
  obtain ⟨-, -, -, hns4⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ f hℓ hℓ2 hf
      hK (by omega) Q hQ (T : V ≃ₗ[K] V) (-1) 1 hsq0 hsim0 hTns
  have h4 := hns4 hnsq
  let : Field (scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap) :=
    scalarField (T : V ≃ₗ[K] V).toLinearMap _ hnsq
      (CatalogueBOrthogonalScalarSquareStructure.original_endomorphism_square _ _ hsq0)
  let : Module (scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap) V :=
    evaluationModule (T : V ≃ₗ[K] V).toLinearMap
  obtain ⟨⟨-, -, -, -, -, -, -, -, hcard, -, -, -, -, -, hconjpow, hconjfix, -, halg, -, hfinE,
    hfinrank, -⟩, -, hneg⟩ := h4
  obtain ⟨hsymm, hnd, -, -, -, -, e, he1, -, -, -⟩ :=
    hneg (by rw [Units.val_one, Units.val_neg, Units.val_one, div_neg, div_one])
  have hU : UnitaryFieldData ℓ f (scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap) :=
    ⟨hℓ, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨Hf, hHsymm, hHnd, e', he'⟩ := exists_unitary_transfer (σ := hU.bar)
    (fun z => (hconjpow z).trans (hU.bar_apply z).symm) hsymm hnd T e he1
  have hdimE : 3 ≤ finrank (scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap) V := by omega
  obtain ⟨-, -, hSU⟩ := eq_unitarySpecial_of_isComponent hU hℓ2 (by omega) hHsymm hHnd.1
    (isComponent_map_of_isComponent e' hL)
  have hcorr : ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∃ x ∈ L, ∀ v,
      ((x : orthogonalGroup Q) : V ≃ₗ[K] V) v =
        ((g : LinearMap.GeneralLinearGroup (scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap) V) :
          V →ₗ[scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap] V) v := by
    intro g hg
    have hgU := (mem_sesqSpecialUnitaryGroup.mp hg).1
    have hmem : (⟨g, hgU⟩ : sesqUnitaryGroup Hf) ∈ L.map e'.toMonoidHom := by
      rw [hSU, mem_unitarySpecial]
      exact (mem_sesqSpecialUnitaryGroup.mp hg).2
    obtain ⟨x, hx, hxg⟩ := hmem
    refine ⟨x, hx, fun v => ?_⟩
    rw [← he' x v]
    exact congrArg (fun y : sesqUnitaryGroup Hf =>
      ((y : LinearMap.GeneralLinearGroup (scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap) V) :
        V →ₗ[scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap] V) v) hxg
  have hRc : ∀ r ∈ R, ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∀ v,
      (r : V ≃ₗ[K] V) (((g : LinearMap.GeneralLinearGroup
        (scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap) V) :
          V →ₗ[scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap] V) v) =
        ((g : LinearMap.GeneralLinearGroup (scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap) V) :
          V →ₗ[scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap] V) ((r : V ≃ₗ[K] V) v) := by
    intro r hr g hg v
    obtain ⟨x, hx, hxg⟩ := hcorr g hg
    rw [← hxg, ← hxg]
    have h1 := Subgroup.mem_centralizer_iff.mp (hR hr) _ (Subgroup.mem_map_of_mem _ hx)
    exact (LinearEquiv.congr_fun (congrArg (fun y : orthogonalGroup Q => (y : V ≃ₗ[K] V)) h1)
      v).symm
  have hfixK : ∀ c : hU.fixedField, ∃ a : K, ∀ v : V,
      (c : scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap) • v = a • v := by
    intro c
    have hc : hU.bar (c : scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap) = c :=
      hU.mem_fixedField.mp c.2
    obtain ⟨a, ha⟩ := (hconjfix (c : scalarAlgebra (T : V ≃ₗ[K] V).toLinearMap)).mp
      ((hconjpow _).trans ((hU.bar_apply _).symm.trans hc))
    exact ⟨a, fun v => by rw [ha, halg]⟩
  have hRcomm := commute_of_commute_specialUnitary hU hℓ2 hdimE hHsymm hHnd hfixK hRc
  have hRle : R ≤ Subgroup.centralizer (R : Set (orthogonalGroup Q)) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun s hs => hRcomm s hs r hr
  rw [← hRp, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRle]

end CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal
