module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.Quasithin.Background.SmithB42L2Sl2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
open scoped MatrixGroups

section Rep

variable {X : Type} [Group X] {V : Type} [CommGroup V] {W : Type} [AddCommGroup W]
  [Module (ZMod 2) W]

@[expose] noncomputable def repOf (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    (φ : X →* ↥L) : Representation (ZMod 2) X W :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((binPsi θ).toMonoidHom.comp (L.subtype.comp φ))

theorem repOf_apply (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)} (φ : X →* ↥L)
    (x : X) (w : W) : repOf θ φ x w = binPsi θ ((φ x : ↥L) : MulAut V) w := rfl

theorem repOf_ker (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)} (φ : X →* ↥L) :
    ∀ x : X, repOf θ φ x = 1 → φ x = 1 := by
  intro x hx
  have h1 : binPsi θ ((φ x : ↥L) : MulAut V) = 1 := by
    refine LinearEquiv.ext fun w => ?_
    have := LinearMap.congr_fun hx w
    rw [repOf_apply] at this
    exact this
  exact Subtype.ext ((binPsi θ).injective (h1.trans (map_one _).symm))

theorem repOf_irreducible (θ : V ≃* Multiplicative W) [Nontrivial W]
    {L : Subgroup (MulAut V)}
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    {φ : X →* ↥L} (hφ : Function.Surjective φ) : (repOf θ φ).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨inferInstance, fun U hU => B42L2.irr_map θ hirr U ?_⟩
  rintro _ ⟨l, hl, rfl⟩ u hu
  obtain ⟨x, hx⟩ := hφ ⟨l, hl⟩
  have h1 := hU x u hu
  rw [repOf_apply, hx] at h1
  exact h1

theorem intertwines_map (θ : V ≃* Multiplicative W) {L : Subgroup (MulAut V)}
    {φ : X →* ↥L} (hφ : Function.Surjective φ) {Q : Subgroup (MulAut V)}
    (hQ : Q ≤ Subgroup.normalizer (L : Set (MulAut V))) :
    ∀ a ∈ Q.map (binPsi θ).toMonoidHom, ∀ x : X, ∃ y : X,
      ∀ w, a (repOf θ φ x w) = repOf θ φ y (a w) := by
  rintro _ ⟨g, hg, rfl⟩ x
  have hmem : g * ((φ x : ↥L) : MulAut V) * g⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hQ hg) _).mp (φ x).2
  obtain ⟨y, hy⟩ := hφ ⟨_, hmem⟩
  refine ⟨y, fun u => ?_⟩
  show binPsi θ g (repOf θ φ x u) = repOf θ φ y (binPsi θ g u)
  rw [repOf_apply, repOf_apply, hy, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply,
    ← map_mul, ← map_mul]
  congr 2
  group

end Rep

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
