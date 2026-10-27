module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.O62

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {W : Type*} [AddCommGroup W]
  [Module (ZMod 2) W]

@[expose] def conjL (L : V ≃ₗ[ZMod 2] W) : (V ≃ₗ[ZMod 2] V) ≃* (W ≃ₗ[ZMod 2] W) where
  toFun g := L.symm.trans (g.trans L)
  invFun h := L.trans (h.trans L.symm)
  left_inv g := by
    ext
    simp
  right_inv h := by
    ext
    simp
  map_mul' g h := by
    ext
    simp

theorem conjL_apply (L : V ≃ₗ[ZMod 2] W) (g : V ≃ₗ[ZMod 2] V) (x : W) :
    conjL L g x = L (g (L.symm x)) := rfl

theorem conjL_symm_apply (L : V ≃ₗ[ZMod 2] W) (h : W ≃ₗ[ZMod 2] W) (v : V) :
    (conjL L).symm h v = L.symm (h (L v)) := rfl

variable {Q : QuadraticForm (ZMod 2) V} {Q' : QuadraticForm (ZMod 2) W}

theorem mem_orthogonalGroup_conjL {L : V ≃ₗ[ZMod 2] W} (hL : ∀ v, Q' (L v) = Q v)
    {g : V ≃ₗ[ZMod 2] V} :
    conjL L g ∈ TauCeti.QuadraticMap.orthogonalGroup Q' ↔
      g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  simp only [TauCeti.QuadraticMap.mem_orthogonalGroup_iff, conjL_apply]
  constructor
  · intro h v
    have := h (L v)
    rwa [LinearEquiv.symm_apply_apply, hL, hL] at this
  · intro h x
    rw [hL, h, ← hL, LinearEquiv.apply_symm_apply]

theorem commSpace_conjL (L : V ≃ₗ[ZMod 2] W) (g : V ≃ₗ[ZMod 2] V) :
    commSpace (conjL L g) = (commSpace g).map (L : V →ₗ[ZMod 2] W) := by
  ext y
  simp only [mem_commSpace, Submodule.mem_map, conjL_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨g (L.symm x) - L.symm x, ⟨L.symm x, rfl⟩, by
      rw [map_sub, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨L u, by rw [LinearEquiv.symm_apply_apply, map_sub]⟩

theorem finrank_commSpace_conjL (L : V ≃ₗ[ZMod 2] W) (g : V ≃ₗ[ZMod 2] V) :
    finrank (ZMod 2) (commSpace (conjL L g)) = finrank (ZMod 2) (commSpace g) := by
  rw [commSpace_conjL]
  exact LinearEquiv.finrank_map_eq L _

theorem mem_omegaGroup_conjL [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    (hQ : Q.polarBilin.Nondegenerate) (hQ' : Q'.polarBilin.Nondegenerate)
    {L : V ≃ₗ[ZMod 2] W} (hL : ∀ v, Q' (L v) = Q v) {g : V ≃ₗ[ZMod 2] V} :
    conjL L g ∈ omegaGroup Q' hQ' ↔ g ∈ omegaGroup Q hQ := by
  rw [mem_omegaGroup, mem_omegaGroup, mem_orthogonalGroup_conjL hL, finrank_commSpace_conjL]

theorem map_conjL_le_orthogonalGroup {L : V ≃ₗ[ZMod 2] W} (hL : ∀ v, Q' (L v) = Q v)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP : P ≤ TauCeti.QuadraticMap.orthogonalGroup Q) :
    P.map (conjL L).toMonoidHom ≤ TauCeti.QuadraticMap.orthogonalGroup Q' := by
  rintro _ ⟨g, hg, rfl⟩
  exact (mem_orthogonalGroup_conjL hL).mpr (hP hg)

theorem card_map_conjL (L : V ≃ₗ[ZMod 2] W) (P : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Nat.card (P.map (conjL L).toMonoidHom) = Nat.card P :=
  Subgroup.card_map_of_injective (conjL L).injective

end CFSG.LargeExtraspecial.O62
