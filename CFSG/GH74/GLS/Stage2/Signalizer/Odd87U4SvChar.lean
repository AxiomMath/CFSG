module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NatMod
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Char

variable {p₀ f₀ : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p₀ f₀ K)

@[expose] noncomputable def hypRho :
    ↥(hypSU h 2 0) →* ((HypIndex 2 0 → K) ≃ₗ[K] (HypIndex 2 0 → K)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (HypIndex 2 0 → K)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin (n := HypIndex 2 0) (R := K)).toMonoidHom).comp
      (hypSU h 2 0).subtype

theorem hypRho_apply (g : ↥(hypSU h 2 0)) (v : HypIndex 2 0 → K) :
    hypRho h g v = ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v :=
  rfl

theorem hypRho_injective : Function.Injective (hypRho h) := by
  intro a b hab
  apply Subtype.ext
  have h1 : (LinearMap.GeneralLinearGroup.generalLinearEquiv K (HypIndex 2 0 → K)).toMonoidHom
      (Matrix.GeneralLinearGroup.toLin (n := HypIndex 2 0) (R := K) (a : GL (HypIndex 2 0) K)) =
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (HypIndex 2 0 → K)).toMonoidHom
      (Matrix.GeneralLinearGroup.toLin (n := HypIndex 2 0) (R := K) (b : GL (HypIndex 2 0) K)) :=
    hab
  exact Matrix.GeneralLinearGroup.toLin.injective
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (HypIndex 2 0 → K)).injective h1)

theorem exists_proper_invariant_subspace_hypSU {p : ℕ} [Fact p.Prime] (hp : p = p₀)
    {X : Subgroup (hypPSU h 2 0)} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    {C : Subgroup (hypPSU h 2 0)} (hC : C ≤ normalizer (X : Set (hypPSU h 2 0))) :
    ∃ W : Submodule K (HypIndex 2 0 → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ C → ∀ w ∈ W,
        ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W := by
  have := h.finite
  have hchar : CharP K p := hp ▸ h.charP
  have hker : (hypProj h 2 0).ker ≤ Subgroup.center ↥(hypSU h 2 0) := by
    rw [ker_hypProj]
    exact normOneScalars_le_center h _ _
  have hcop : Nat.Coprime p (Nat.card (hypProj h 2 0).ker) :=
    NatMod.coprime_card_of_scalars (hypRho h) (hypRho_injective h) (fun z hz => by
      obtain ⟨c, -, -, hc⟩ := ((SetLike.ext_iff.1 (ker_hypProj h 2 0)) z).1 hz
      refine ⟨(c : K), fun v => ?_⟩
      rw [hypRho_apply, hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
      ext i
      rw [Matrix.mulVec_diagonal]
      rfl)
  obtain ⟨W, hW0, hWt, hW⟩ := exists_proper_invariant_subspace (hypRho h) (hypRho_injective h)
    (hypProj h 2 0) (hypProj_surjective h 2 0) hker hcop hX hX1 hC
  exact ⟨W, hW0, hWt, fun g hg w hw => hW g hg w hw⟩

end Char

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
