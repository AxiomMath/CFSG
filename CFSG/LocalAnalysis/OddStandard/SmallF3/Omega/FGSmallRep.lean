module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem fg_card_linearEquiv_dvd {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [FiniteDimensional (ZMod 3) U] (hU : Module.finrank (ZMod 3) U ≤ 3) :
    Nat.card (U ≃ₗ[ZMod 3] U) ∣ 11232 := by
  classical
  generalize hd : Module.finrank (ZMod 3) U = d at hU
  have hcard : Nat.card (U ≃ₗ[ZMod 3] U) = Nat.card (GL (Fin d) (ZMod 3)) := by
    let b : Module.Basis (Fin d) (ZMod 3) U := Module.finBasisOfFinrankEq (ZMod 3) U hd
    exact Nat.card_congr
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) U).symm.trans
        ((LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
          (Matrix.GeneralLinearGroup.toLin).symm)).toEquiv
  rw [hcard, Matrix.card_GL_field d]
  simp only [ZMod.card]
  interval_cases d <;> decide

theorem fg_pointwise_of_card {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (H : Subgroup (V ≃ₗ[ZMod 3] V)) [IsSimpleGroup ↥H]
    (W : Submodule (ZMod 3) V) (hW : ∀ g ∈ H, ∀ w ∈ W, g w ∈ W) {N : ℕ}
    (hN : Nat.card (↥W ≃ₗ[ZMod 3] ↥W) ∣ N) (hcard : ¬ Nat.card ↥H ∣ N) :
    ∀ g ∈ H, ∀ w ∈ W, g w = w := by
  have hmap : ∀ g : V ≃ₗ[ZMod 3] V, g ∈ H → W.map (g : V →ₗ[ZMod 3] V) = W := by
    intro g hg
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro w hw
      exact hW g hg w hw
    · intro x hx
      rw [Submodule.mem_map]
      exact ⟨g⁻¹ x, hW g⁻¹ (H.inv_mem hg) x hx, by simp⟩
  let φ : ↥H →* (↥W ≃ₗ[ZMod 3] ↥W) :=
    { toFun := fun g => g.1.ofSubmodules W W (hmap g.1 g.2)
      map_one' := by
        ext x
        simp [LinearEquiv.ofSubmodules_apply]
      map_mul' := fun g h => by
        ext x
        simp [LinearEquiv.ofSubmodules_apply, LinearEquiv.mul_apply] }
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hker | hker
  · exfalso
    have hf : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
    exact hcard (dvd_trans (Subgroup.card_dvd_of_injective φ hf) hN)
  · intro g hg w hw
    have hmem : (⟨g, hg⟩ : ↥H) ∈ φ.ker := by
      rw [hker]
      exact Subgroup.mem_top _
    have h1 : φ ⟨g, hg⟩ = 1 := MonoidHom.mem_ker.mp hmem
    have := congrArg (fun e : (↥W ≃ₗ[ZMod 3] ↥W) => (e ⟨w, hw⟩ : V)) h1
    simpa [φ, LinearEquiv.ofSubmodules_apply] using this

theorem fg_pointwise_of_finrank_le {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (H : Subgroup (V ≃ₗ[ZMod 3] V)) [IsSimpleGroup ↥H]
    (hcard : ¬ Nat.card ↥H ∣ 11232) (W : Submodule (ZMod 3) V)
    (hW : ∀ g ∈ H, ∀ w ∈ W, g w ∈ W) (hdim : Module.finrank (ZMod 3) W ≤ 3) :
    ∀ g ∈ H, ∀ w ∈ W, g w = w :=
  fg_pointwise_of_card H W hW (fg_card_linearEquiv_dvd hdim) hcard

end CFSG.OddStandard.SmallF3.Omega
