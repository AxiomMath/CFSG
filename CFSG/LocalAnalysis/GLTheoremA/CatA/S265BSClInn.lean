module

public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

theorem exists_innerSection {Ω G : Type} [Group Ω] [Group G] (Φ : Ω →* MulAut G)
    (hZ : Subgroup.center G = ⊥) :
    ∃ (W : Subgroup Ω) (ρ : W →* G), W.Normal ∧
      (∀ w : Ω, w ∈ W ↔ ∃ s : G, MulAut.conj s = Φ w) ∧ (∀ w : W, MulAut.conj (ρ w) = Φ w) ∧
        ∀ w : W, ρ w = 1 ↔ Φ w = 1 := by
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    intro s t hst
    have hc : t⁻¹ * s ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => by
      have h1 : s * g * s⁻¹ = t * g * t⁻¹ := by
        simpa only [MulAut.conj_apply] using congrArg (fun β : MulAut G => β g) hst
      calc g * (t⁻¹ * s) = t⁻¹ * (t * g * t⁻¹) * s := by group
        _ = t⁻¹ * (s * g * s⁻¹) * s := by rw [h1]
        _ = t⁻¹ * s * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  have hnorm : (MulAut.conj : G →* MulAut G).range.Normal := ⟨fun n hn α => by
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hn
    refine MonoidHom.mem_range.2 ⟨α s, MulEquiv.ext fun z => ?_⟩
    simp [MulAut.conj_apply]⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥((MulAut.conj : G →* MulAut G).range.comap Φ) →* G,
      ∀ w, MulAut.conj (ρ w) = Φ w :=
    ⟨((MonoidHom.ofInjective hinj).symm : _ ≃* G).toMonoidHom.comp
      (Φ.subgroupComap (MulAut.conj : G →* MulAut G).range),
      fun w => MonoidHom.apply_ofInjective_symm hinj (Φ.subgroupComap _ w)⟩
  refine ⟨_, ρ, hnorm.comap Φ, fun w => ?_, hρ, fun w => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · rw [Subgroup.mem_comap, MonoidHom.mem_range]
  · rw [← hρ w, h1, map_one]
  · apply hinj
    rw [hρ w, h1, map_one]

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
