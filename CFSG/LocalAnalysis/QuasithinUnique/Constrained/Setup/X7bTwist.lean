module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bRepInd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open scoped MonoidAlgebra
open CFSG.Semidihedral.Principal Representation

section Twist

variable {k k' G : Type} [Field k] [Field k'] [Monoid G]

instance ringEquivInvPair (τ : k ≃+* k') :
    RingHomInvPair (τ : k →+* k') (τ.symm : k' →+* k) :=
  RingHomInvPair.of_ringEquiv τ

instance ringEquivInvPair' (τ : k ≃+* k') :
    RingHomInvPair (τ.symm : k' →+* k) (τ : k →+* k') :=
  RingHomInvPair.of_ringEquiv τ.symm

variable (τ : k ≃+* k') {V V' : Type} [AddCommGroup V] [Module k V] [AddCommGroup V']
  [Module k' V']

structure TwistEquiv (ρ : Representation k G V) (ρ' : Representation k' G V') where
  e : V ≃ₛₗ[(τ : k →+* k')] V'
  comm : ∀ g v, e (ρ g v) = ρ' g (e v)

variable {τ} {ρ : Representation k G V} {ρ' : Representation k' G V'}

@[expose] def TwistEquiv.mapSub (T : TwistEquiv τ ρ ρ') (W : Subrepresentation ρ) :
    Subrepresentation ρ' where
  toSubmodule := W.toSubmodule.map (T.e : V →ₛₗ[(τ : k →+* k')] V')
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, W.apply_mem_toSubmodule g hv, T.comm g v⟩

@[expose] noncomputable def TwistEquiv.subrepOrderIso (T : TwistEquiv τ ρ ρ') :
    Subrepresentation ρ ≃o Subrepresentation ρ' where
  toFun := T.mapSub
  invFun W' := ⟨W'.toSubmodule.comap (T.e : V →ₛₗ[(τ : k →+* k')] V'), by
    intro g v hv
    show T.e (ρ g v) ∈ W'.toSubmodule
    rw [T.comm]
    exact W'.apply_mem_toSubmodule g hv⟩
  left_inv W := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.comap_map_eq_of_injective T.e.injective _
  right_inv W' := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_comap_eq_of_surjective T.e.surjective _
  map_rel_iff' {W₁ W₂} := by
    show W₁.toSubmodule.map (T.e : V →ₛₗ[(τ : k →+* k')] V') ≤
      W₂.toSubmodule.map (T.e : V →ₛₗ[(τ : k →+* k')] V') ↔ W₁.toSubmodule ≤ W₂.toSubmodule
    exact Submodule.map_le_map_iff_of_injective T.e.injective _ _

theorem TwistEquiv.isIrreducible (T : TwistEquiv τ ρ ρ') (h : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible ρ' :=
  (OrderIso.isSimpleOrder_iff T.subrepOrderIso).mp h

@[expose] def twistLinearEquiv {W W' : Type} [AddCommGroup W] [Module k W] [AddCommGroup W']
    [Module k' W'] (e : V ≃ₛₗ[(τ : k →+* k')] V') (f : W ≃ₛₗ[(τ : k →+* k')] W')
    (φ : V ≃ₗ[k] W) : V' ≃ₗ[k'] W' where
  toFun v' := f (φ (e.symm v'))
  invFun w' := e (φ.symm (f.symm w'))
  map_add' x y := by simp
  map_smul' c v := by
    simp only [map_smulₛₗ, RingHom.id_apply]
    simp
  left_inv v' := by simp
  right_inv w' := by simp

@[expose] def twistLinearEquivInv {W W' : Type} [AddCommGroup W] [Module k W] [AddCommGroup W']
    [Module k' W'] (e : V ≃ₛₗ[(τ : k →+* k')] V') (f : W ≃ₛₗ[(τ : k →+* k')] W')
    (φ : V' ≃ₗ[k'] W') : V ≃ₗ[k] W where
  toFun v := f.symm (φ (e v))
  invFun w := e.symm (φ.symm (f w))
  map_add' x y := by simp
  map_smul' c v := by
    simp only [map_smulₛₗ, RingHom.id_apply]
    simp
  left_inv v := by simp
  right_inv w := by simp

theorem TwistEquiv.nonempty_equiv_iff {W W' : Type} [AddCommGroup W] [Module k W]
    [AddCommGroup W'] [Module k' W'] {σ : Representation k G W} {σ' : Representation k' G W'}
    (T : TwistEquiv τ ρ ρ') (S : TwistEquiv τ σ σ') :
    Nonempty (Representation.Equiv ρ' σ') ↔ Nonempty (Representation.Equiv ρ σ) := by
  have hS : ∀ g w', S.e.symm (σ' g w') = σ g (S.e.symm w') := fun g w' => by
    apply S.e.injective
    rw [LinearEquiv.apply_symm_apply, S.comm, LinearEquiv.apply_symm_apply]
  have hT : ∀ g v', T.e.symm (ρ' g v') = ρ g (T.e.symm v') := fun g v' => by
    apply T.e.injective
    rw [LinearEquiv.apply_symm_apply, T.comm, LinearEquiv.apply_symm_apply]
  constructor
  · rintro ⟨φ⟩
    have hφ : ∀ g v', φ.toLinearEquiv (ρ' g v') = σ' g (φ.toLinearEquiv v') := fun g v' =>
      IntertwiningMap.isIntertwining ρ' σ' φ.toIntertwiningMap g v'
    refine ⟨Representation.Equiv.mk (twistLinearEquivInv T.e S.e φ.toLinearEquiv) (fun g => ?_)⟩
    ext v
    show S.e.symm (φ.toLinearEquiv (T.e (ρ g v))) = σ g (S.e.symm (φ.toLinearEquiv (T.e v)))
    rw [T.comm, hφ, hS]
  · rintro ⟨φ⟩
    have hφ : ∀ g v, φ.toLinearEquiv (ρ g v) = σ g (φ.toLinearEquiv v) := fun g v =>
      IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v
    refine ⟨Representation.Equiv.mk (twistLinearEquiv T.e S.e φ.toLinearEquiv) (fun g => ?_)⟩
    ext v'
    show S.e (φ.toLinearEquiv (T.e.symm (ρ' g v'))) = σ' g (S.e (φ.toLinearEquiv (T.e.symm v')))
    rw [hT, hφ, S.comm]

@[expose] noncomputable def TwistEquiv.sub (T : TwistEquiv τ ρ ρ') (W : Subrepresentation ρ) :
    TwistEquiv τ W.toRepresentation (T.mapSub W).toRepresentation where
  e := Submodule.equivMapOfInjective (T.e : V →ₛₗ[(τ : k →+* k')] V') T.e.injective W.toSubmodule
  comm g v := by
    apply Subtype.ext
    exact T.comm g (v : V)

@[expose] noncomputable def TwistEquiv.quot (T : TwistEquiv τ ρ ρ') (W : Subrepresentation ρ) :
    TwistEquiv τ W.quotient (T.mapSub W).quotient where
  e := LinearEquiv.ofLinearMap
    (Submodule.mapQ W.toSubmodule (T.mapSub W).toSubmodule
      (T.e : V →ₛₗ[(τ : k →+* k')] V') (Submodule.le_comap_map _ _))
    (Submodule.mapQ (T.mapSub W).toSubmodule W.toSubmodule
      (T.e.symm : V' →ₛₗ[(τ.symm : k' →+* k)] V) (by
        rintro _ ⟨v, hv, rfl⟩
        simpa using hv))
    (by
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        show Submodule.Quotient.mk (T.e (T.e.symm x)) = Submodule.Quotient.mk x
        rw [LinearEquiv.apply_symm_apply])
    (by
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        show Submodule.Quotient.mk (T.e.symm (T.e x)) = Submodule.Quotient.mk x
        rw [LinearEquiv.symm_apply_apply])
  comm g v := by
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      show Submodule.Quotient.mk (T.e (ρ g v)) = Submodule.Quotient.mk (ρ' g (T.e v))
      rw [T.comm]

theorem repMultiplicity_twist {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {V' E E' : Type} [AddCommGroup V'] [Module k' V'] [AddCommGroup E] [Module k E]
    [AddCommGroup E'] [Module k' E'] {ρ : Representation k G V} {ρ' : Representation k' G V'}
    {σ : Representation k G E} {σ' : Representation k' G E'} (T : TwistEquiv τ ρ ρ')
    (S : TwistEquiv τ σ σ') : repMultiplicity ρ' σ' = repMultiplicity ρ σ := by
  have key := rep_induction (k := k) (G := G)
    (fun {V} _ _ _ ρ => ∀ {V' E E' : Type} [AddCommGroup V'] [Module k' V'] [AddCommGroup E]
      [Module k E] [AddCommGroup E'] [Module k' E'] {ρ' : Representation k' G V'}
      {σ : Representation k G E} {σ' : Representation k' G E'} (_ : TwistEquiv τ ρ ρ')
      (_ : TwistEquiv τ σ σ'), repMultiplicity ρ' σ' = repMultiplicity ρ σ)
    (fun {V} _ _ _ ρ hsub {V'} {E} {E'} _ _ _ _ _ _ {ρ'} {σ} {σ'} T S => by
      have : Subsingleton V' := T.e.surjective.subsingleton
      have : Subsingleton (Representation.asModule ρ) := inferInstanceAs (Subsingleton V)
      have : Subsingleton (Representation.asModule ρ') := inferInstanceAs (Subsingleton V')
      unfold repMultiplicity
      rw [compositionMultiplicity_of_subsingleton, compositionMultiplicity_of_subsingleton])
    (fun {V} _ _ _ ρ hρ {V'} {E} {E'} _ _ _ _ _ _ {ρ'} {σ} {σ'} T S => by
      rw [repMultiplicity_of_isIrreducible (T.isIrreducible hρ) σ',
        repMultiplicity_of_isIrreducible hρ σ]
      have := T.nonempty_equiv_iff S
      by_cases h : Nonempty (Representation.Equiv ρ σ)
      · simp only [h, this.mpr h, ↓reduceIte]
      · have h2 : ¬ Nonempty (Representation.Equiv ρ' σ') := fun h' => h (this.mp h')
        simp only [h, h2, ↓reduceIte])
    (fun {V} _ _ _ ρ W hW1 hW2 {V'} {E} {E'} _ _ _ _ _ _ {ρ'} {σ} {σ'} T S => by
      have : Module.Finite k' V' :=
        Module.Finite.of_surjective (T.e : V →ₛₗ[(τ : k →+* k')] V') T.e.surjective
      rw [repMultiplicity_sub_quot ρ' (T.mapSub W) σ', repMultiplicity_sub_quot ρ W σ,
        hW1 (T.sub W) S, hW2 (T.quot W) S])
  exact key _ ρ rfl T S

end Twist

section MatrixTwist

open CFSG.QuasithinUnique.Setup.X7 (matRep matMap)

variable {k k' G : Type} [Field k] [Field k'] [Group G] (τ : k ≃+* k') {ι : Type} [Fintype ι]
  [DecidableEq ι]

@[expose] def matRepTwist (R : G →* Matrix ι ι k) :
    TwistEquiv τ (matRep R) (matRep (matMap (τ : k →+* k') R)) where
  e :=
    { toFun := fun v i => τ (v i)
      invFun := fun w i => τ.symm (w i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c v => by ext i; simp
      left_inv := fun v => by ext i; simp
      right_inv := fun w => by ext i; simp }
  comm g v := by
    ext i
    simp [CFSG.QuasithinUnique.Setup.X7.matRep_apply, Matrix.mulVec, dotProduct,
      CFSG.QuasithinUnique.Setup.X7.matMap_apply, map_sum]

theorem repMultiplicity_matMap {κ : Type} [Fintype κ] [DecidableEq κ] (R : G →* Matrix ι ι k)
    (S : G →* Matrix κ κ k) :
    repMultiplicity (matRep (matMap (τ : k →+* k') R)) (matRep (matMap (τ : k →+* k') S)) =
      repMultiplicity (matRep R) (matRep S) :=
  repMultiplicity_twist (matRepTwist τ R) (matRepTwist τ S)

end MatrixTwist

end CFSG.QuasithinUnique.Setup.X7b
