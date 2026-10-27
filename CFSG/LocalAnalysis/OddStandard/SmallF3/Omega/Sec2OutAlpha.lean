module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenCover

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open scoped commutatorElement

variable {Y P : Type} [Group Y] [Group P] {ρ : Y →* P}

theorem exists_induced_aut (hρ : Function.Surjective ρ) {σ : MulAut Y} (hσ : σ * σ = 1)
    (hker : ∀ n ∈ ρ.ker, σ n ∈ ρ.ker) :
    ∃ α : MulAut P, (∀ y, ρ (σ y) = α (ρ y)) ∧ α * α = 1 := by
  have hk : ρ.ker ≤ (ρ.comp σ.toMonoidHom).ker := fun n hn => hker n hn
  let α₀ : P →* P := ρ.liftOfSurjective hρ ⟨ρ.comp σ.toMonoidHom, hk⟩
  have hα₀ : ∀ y, α₀ (ρ y) = ρ (σ y) := fun y =>
    MonoidHom.liftOfRightInverse_comp_apply ρ _ _ ⟨ρ.comp σ.toMonoidHom, hk⟩ y
  have hα₀₀ : ∀ p, α₀ (α₀ p) = p := by
    intro p
    obtain ⟨y, rfl⟩ := hρ p
    rw [hα₀, hα₀, aut_apply_apply hσ]
  let α : MulAut P :=
    { toFun := α₀
      invFun := α₀
      left_inv := hα₀₀
      right_inv := hα₀₀
      map_mul' := map_mul α₀ }
  refine ⟨α, fun y => (hα₀ y).symm, ?_⟩
  ext p
  exact hα₀₀ p

theorem exists_inner_of_conj (hρ : OddCentralCover ρ) (hperf : commutator Y = ⊤)
    {σ : MulAut Y} {α : MulAut P} (h : ∀ y, ρ (σ y) = α (ρ y)) {p : P}
    (hp : α = MulAut.conj p) : ∃ y₀ : Y, ∀ y : Y, σ y = y₀ * y * y₀⁻¹ := by
  obtain ⟨y₀, hy₀⟩ := hρ.surjective p
  let M : Subgroup Y := MonoidHom.eqLocus σ.toMonoidHom (MulAut.conj y₀).toMonoidHom
  have hdiff : ∀ y : Y, ∃ n ∈ center Y, σ y = (y₀ * y * y₀⁻¹) * n := by
    intro y
    refine ⟨(y₀ * y * y₀⁻¹)⁻¹ * σ y, hρ.ker_le_center (MonoidHom.mem_ker.mpr ?_), by group⟩
    rw [map_mul, map_inv, h, hp, ← hy₀]
    simp only [MulAut.conj_apply, map_mul, map_inv]
    group
  have hcomm : commutator Y ≤ M := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨n₁, hn₁, h₁⟩ := hdiff g₁
    obtain ⟨n₂, hn₂, h₂⟩ := hdiff g₂
    change σ ⁅g₁, g₂⁆ = y₀ * ⁅g₁, g₂⁆ * y₀⁻¹
    have hc : (y₀ * ⁅g₁, g₂⁆ * y₀⁻¹) = ⁅y₀ * g₁ * y₀⁻¹, y₀ * g₂ * y₀⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [hc, ← commutatorElement_mul_central (y₀ * g₁ * y₀⁻¹) _ n₁ hn₁,
      ← commutatorElement_mul_central_right _ (y₀ * g₂ * y₀⁻¹) n₂ hn₂, ← h₁, ← h₂]
    exact (map_commutatorElement σ.toMonoidHom g₁ g₂)
  rw [hperf, top_le_iff] at hcomm
  refine ⟨y₀, fun y => ?_⟩
  have hy : y ∈ M := by rw [hcomm]; exact mem_top y
  exact hy

end CFSG.OddStandard.SmallF3.Omega
