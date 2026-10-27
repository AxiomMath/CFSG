module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OrigCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwisted
import CFSG.LieType.Steinberg.CentralExt.TwistedE6PosLift
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKernelCore

set_option linter.style.haveILetI false

public section

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.SeitzReduction.F4Pilot (twistedIsogenyC twistedIsogenyC_surjective
  ker_twistedIsogenyC)

namespace TwE6CoverData

variable {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} {S : ℕ → LargeEvenLabel → Prop}
  {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
  {hmark : GGInnerDiagOnLabel S 3 Bs X}

theorem exists_scMap (D : TwE6CoverData hS hmark) (hn3 : 3 ≤ D.lab.n) :
    letI := D.fieldK
    letI := D.finiteK
    ∃ μ : ↥(fixedGroup D.K D.σ.toRingHom) →* ↥X, Function.Surjective μ ∧
      (∀ u, D.ψ (μ u) = twistedIsogenyC D.hn D.hK D.σ.toRingHom D.hσ u) ∧
      μ.ker ≤ Subgroup.center ↥(fixedGroup D.K D.σ.toRingHom) := by
  letI := D.fieldK
  letI := D.finiteK
  classical
  have : Finite ↥(fixedGroup D.K D.σ.toRingHom) := by
    have : Finite (Module.End D.K (Fin e6Data.d →₀ D.K)) := Module.finite_of_finite D.K
    infer_instance
  have h5 : 5 ≤ 2 ^ D.lab.n :=
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ D.lab.n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨α, hα, hαs⟩ := E6ThreeKernel.exists_surjective_of_split
    (twistedIsogenyC_surjective D.hn D.hK D.σ.toRingHom D.hσ)
    (fun E _ _ π hπ hc =>
      TwistedE6Closed.twistedE6_exists_section_of_central D.σ.toRingHom h5 D.hK D.hσ hπ hc)
    D.hψ (le_of_eq D.hker) D.commH
  refine ⟨α, hαs, hα, fun s hs => ?_⟩
  rw [← ker_twistedIsogenyC D.hn D.hK D.σ.toRingHom D.hσ, MonoidHom.mem_ker, ← hα,
    MonoidHom.mem_ker.mp hs, map_one]

noncomputable def scMap (D : TwE6CoverData hS hmark) (hn3 : 3 ≤ D.lab.n) :
    letI := D.fieldK
    letI := D.finiteK
    ↥(fixedGroup D.K D.σ.toRingHom) →* ↥X :=
  Classical.choose (D.exists_scMap hn3)

theorem scMap_spec (D : TwE6CoverData hS hmark) (hn3 : 3 ≤ D.lab.n) :
    letI := D.fieldK
    letI := D.finiteK
    Function.Surjective (D.scMap hn3) ∧
      (∀ u, D.ψ (D.scMap hn3 u) = twistedIsogenyC D.hn D.hK D.σ.toRingHom D.hσ u) ∧
      (D.scMap hn3).ker ≤ Subgroup.center ↥(fixedGroup D.K D.σ.toRingHom) :=
  Classical.choose_spec (D.exists_scMap hn3)

end TwE6CoverData

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
