module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaAux
import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaFinal

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaModel

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem model_equiv {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (hR : Red28 W K S) {V U₁ U₂ : Subgroup X} (sf : SingleFactor K V U₁ U₂)
    (hZ : Subgroup.center ↥(bar W K) = ⊥) {a : X} (hΩ : OmegaModelWith Q W K a U₁ U₂) :
    ∃ (θ : ↥K →* ↥(StatedOmega Q)) (t : GL ι (ZMod 2)),
      Function.Surjective θ ∧ (∀ k : ↥K, θ k = 1 ↔ (k : X) ∈ W) ∧ IsTransvection t ∧
      (∀ x, Q (Matrix.mulVec (t : Matrix ι ι (ZMod 2)) x) = Q x) ∧
      t ∈ Subgroup.normalizer (StatedOmega Q : Set (GL ι (ZMod 2))) ∧
      ∀ k k' : ↥K, (k' : X) = a * (k : X) * a⁻¹ →
        ((θ k' : ↥(StatedOmega Q)) : GL ι (ZMod 2)) =
          t * ((θ k : ↥(StatedOmega Q)) : GL ι (ZMod 2)) * t⁻¹ := by
  obtain ⟨θ, t, hθs, hθW, htr, hQt, htn, hθa, hiso⟩ := hΩ
  obtain ⟨θb, hθb⟩ := OmegaAux.descend θ hθW
  have hθbk : ∀ k : ↥K, θb (toBar W K k) = θ k := fun k => by
    rw [← hθb]; rfl
  have hinj : Function.Injective θb := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hker
    have hnc : ¬ θb.ker ≤ Subgroup.center ↥(bar W K) := by
      rw [hZ]; intro hle; exact hker (le_bot_iff.mp hle)
    have htop : θb.ker = ⊤ :=
      InducedAux.eq_top_of_quasisimple_normal hR.quasi.1.commutator_eq_top hR.quasi.2.1 _ hnc
    refine OmegaFinal.theta_ne_one Q sf θ hiso fun k => ?_
    rw [← hθbk]
    exact MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top _)
  refine ⟨θ, t, hθs, fun k => ⟨fun h1 => ?_, hθW k⟩, htr, hQt, htn, hθa⟩
  have : toBar W K k = 1 := hinj (by rw [hθbk, h1, map_one])
  exact InducedAux.toBar_eq_one_iff.mp this

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaModel
