module

public import CFSG.GH74.Generic.BProg.B3.L2CompU3Fix
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B3.L2CompU3Data

open CFSG CFSG.Blueprint Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.GH74.Generic.S45
open scoped Matrix

theorem psu_fixed_data_D8 {S : Type} [Group S] [Finite S] {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel S .PSU 3 r f) {ya : MulAut S} (hsq : ya * ya = 1) :
    ∃ a b : S, ya a = a ∧ ya b = b ∧ a ^ 4 = 1 ∧ a ^ 2 ≠ 1 ∧ b * b = 1 ∧
      b * a * b⁻¹ = a⁻¹ := by
  classical
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  have hr : r.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hud : UnitaryFieldData r f F := ⟨hr, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : S ≃* unitaryPSU hud 3 := e₀.trans (unitaryPSUEquiv hud (by omega)).symm
  let θ : unitarySU r f F 3 →* S := ψ.symm.toMonoidHom.comp (unitaryProj hud 3)
  have hθ : Function.Surjective θ := ψ.symm.surjective.comp (unitaryProj_surjective hud 3)
  have hθ1 : ∀ g : unitarySU r f F 3, θ g = 1 ↔ g ∈ unitaryScalars hud 3 := by
    intro g
    change ψ.symm (unitaryProj hud 3 g) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_unitaryProj]
  have hker : θ.ker ≤ Subgroup.center (unitarySU r f F 3) := fun g hg =>
    unitaryScalars_le_center hud 3 ((hθ1 g).1 hg)
  obtain ⟨A, φ, hA, hAu, hlift, hinv⟩ := exists_lift_unitarySU' hud hr2 (le_refl 3) θ hθ hker
    (ya : S ≃* S)
  obtain ⟨hφ, hcomp⟩ := hinv (fun x => by
    have := congrArg (fun φ : MulAut S => φ x) hsq
    simpa using this)
  obtain ⟨c, d, hc, hd, hc2, hc4, hd2, hdc⟩ :=
    L2CompU3Fix.exists_fixed_unitary_D8 hud hr2 hA hAu hφ hcomp
  have ha4 : θ c ^ 4 = 1 := by rw [← map_pow, hc4, map_one]
  have hbb : θ d * θ d = 1 := by rw [← map_mul, hd2, map_one]
  refine ⟨θ c, θ d, ?_, ?_, ha4, ?_, hbb, ?_⟩
  · have := hlift c
    rw [hc] at this
    exact this.symm
  · have := hlift d
    rw [hd] at this
    exact this.symm
  · intro h2
    rw [← map_pow] at h2
    exact hc2 ((hθ1 _).1 h2)
  · have hbinv : (θ d)⁻¹ = θ d := inv_eq_of_mul_eq_one_right hbb
    have hainv : (θ c)⁻¹ = θ c ^ 3 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact ha4
    rw [hbinv, hainv, ← map_mul, ← map_mul, hdc, map_pow]

end CFSG.GH74.Generic.BProg.B3.L2CompU3Data
