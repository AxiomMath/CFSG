module

public import CFSG.ClassicalGroups.Orthogonal.RingEquivTransport
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal

open Module

theorem finrank_eq_of_finiteFields_ringEquiv
    {K₀ K V : Type*} [Field K₀] [Field K] [Finite K₀] [Finite K]
    [AddCommGroup V] [Finite V] [Module K₀ V] [Module K V]
    (e : K₀ ≃+* K) : finrank K₀ V = finrank K V := by
  let : Module.Finite K₀ V := Module.Finite.of_finite
  let : Module.Finite K V := Module.Finite.of_finite
  have hcard : Nat.card K₀ = Nat.card K := Nat.card_congr e.toEquiv
  have h0 : Nat.card V = Nat.card K₀ ^ finrank K₀ V := Module.natCard_eq_pow_finrank
  have h1 : Nat.card V = Nat.card K ^ finrank K V := Module.natCard_eq_pow_finrank
  rw [hcard] at h0
  exact Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card K) (h0.symm.trans h1)

private theorem halfDim_zeroSubspace_ringEquiv
    {K₀ K V : Type*} [Field K₀] [Field K] [Finite K₀] [Finite K]
    [AddCommGroup V] [Finite V] [Module K₀ V] [Module K V]
    (e : K₀ ≃+* K) (hsmul : ∀ (c : K₀) (v : V), c • v = e c • v)
    (q : V → K) :
    (∃ U : Submodule K₀ V, 2 * finrank K₀ U = finrank K₀ V ∧
      ∀ x ∈ U, e.symm (q x) = 0) ↔
    (∃ W : Submodule K V, 2 * finrank K W = finrank K V ∧
      ∀ x ∈ W, q x = 0) := by
  have hdim := finrank_eq_of_finiteFields_ringEquiv (V := V) e
  constructor
  · rintro ⟨U, hU, hzero⟩
    let W : Submodule K V :=
      { carrier := U
        add_mem' := U.add_mem
        zero_mem' := U.zero_mem
        smul_mem' := fun c v hv => by
          have h := U.smul_mem (e.symm c) hv
          rwa [hsmul, RingEquiv.apply_symm_apply] at h }
    let : Module K₀ W := (inferInstance : Module K₀ U)
    have hWU : finrank K W = finrank K₀ U :=
      (finrank_eq_of_finiteFields_ringEquiv (V := W) e).symm
    refine ⟨W, ?_, ?_⟩
    · rw [hWU, ← hdim]
      exact hU
    · intro x hx
      apply e.symm.injective
      simpa only [map_zero] using hzero x hx
  · rintro ⟨W, hW, hzero⟩
    let U : Submodule K₀ V :=
      { carrier := W
        add_mem' := W.add_mem
        zero_mem' := W.zero_mem
        smul_mem' := fun c v hv => by
          rw [hsmul]
          exact W.smul_mem (e c) hv }
    let : Module K U := (inferInstance : Module K W)
    have hUW : finrank K₀ U = finrank K W :=
      finrank_eq_of_finiteFields_ringEquiv (V := U) e
    refine ⟨U, ?_, ?_⟩
    · rw [hUW, hdim]
      exact hW
    · intro x hx
      rw [hzero x hx, map_zero]

open QuadraticMap Subgroup

section Transport

variable {K₀ K V : Type*} [Field K₀] [Field K] [AddCommGroup V]
  [Module K V] [Module K₀ V]
  (e : K₀ ≃+* K) (hsmul : ∀ (c : K₀) (v : V), c • v = e c • v)

theorem orthogonalGroup_map_restrictScalarsHom (Q : QuadraticForm K V) :
    (TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q)).map
      (restrictScalarsHom e hsmul) = TauCeti.QuadraticMap.orthogonalGroup Q := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact mem_orthogonalGroup_restrictScalarsHom hg
  · intro g hg
    let g' : V ≃ₗ[K₀] V :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun c v => by
          show g (c • v) = c • g v
          rw [hsmul, hsmul]
          exact g.map_smul (e c) v
        invFun := g.symm
        left_inv := g.left_inv
        right_inv := g.right_inv }
    have hg' : g' ∈
        TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q) := by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg ⊢
      intro x
      rw [formOfRingEquiv_apply, formOfRingEquiv_apply]
      change e.symm (Q (g x)) = e.symm (Q x)
      rw [hg x]
    exact ⟨g', hg', LinearEquiv.ext fun _ => rfl⟩

theorem derived_map_restrictScalarsHom (Q : QuadraticForm K V) :
    (⁅TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q),
      TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q)⁆).map
      (restrictScalarsHom e hsmul) =
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [Subgroup.map_commutator, orthogonalGroup_map_restrictScalarsHom]

@[expose] def derivedFieldEquiv (Q : QuadraticForm K V) :
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q),
      TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q)⁆ ≃*
    ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((⁅TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q),
      TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q)⁆).equivMapOfInjective
    (restrictScalarsHom e hsmul) restrictScalarsHom_injective).trans
      (MulEquiv.subgroupCongr (derived_map_restrictScalarsHom e hsmul Q))

theorem derivedFieldEquiv_coe (Q : QuadraticForm K V)
    (x : ↥⁅TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q),
      TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q)⁆) :
    (derivedFieldEquiv e hsmul Q x : V ≃ₗ[K] V) =
      restrictScalarsHom e hsmul (x : V ≃ₗ[K₀] V) := rfl

end Transport

theorem isPlusType_formOfRingEquiv
    {K₀ K V : Type} [Field K₀] [Field K] [Finite K₀] [Finite K]
    [AddCommGroup V] [Finite V] [Module K₀ V] [Module K V]
    (e : K₀ ≃+* K) (hsmul : ∀ (c : K₀) (v : V), c • v = e c • v)
    (Q : QuadraticForm K V) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (formOfRingEquiv e hsmul Q) ↔
      CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
  halfDim_zeroSubspace_ringEquiv e hsmul Q

end CFSG.ClassicalGroups.Orthogonal

end
