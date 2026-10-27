module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf30Setup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3
public import CFSG.ClassicalInvolution.Q3.Q3T6DSFuse

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

section TypeR

theorem std20Frame_typeRHyp {G : Type} [Group G] [Finite G] {K K' J : Subgroup G}
    {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G} (d : Std20Frame K K' J S R R' W V z t) :
    TypeRHyp (CoreAssembly.conjClass K) where
  hyp := d.hyp
  twoGroup := by
    rintro L ⟨g, rfl⟩
    let e : ↥K ≃* ↥(conjSub g K) :=
      K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact d.twoGroup.of_equiv (QuotientGroup.congr _ _ e
      (CFSG.ComponentClassification.OddCore.equiv_invariant e))
  sylow := fun L hL P hP => Out.nonempty_equiv_q8'
    (Sec6Gen.isQuatSub_of_mem_RSet d.hyp (mem_RSet_of_isSylow2In hL hP))
    (by rw [d.hyp.omega3 L hL K (CoreAssembly.mem_conjClass_self K) P R hP d.hR, d.card8])

end TypeR

section Defs

@[expose] def FrameXCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
      ∀ ρ : G, ρ * z * ρ⁻¹ = z * t → ρ * t * ρ⁻¹ = z →
        ∀ L ∈ aStar (CoreAssembly.conjClass K) K,
          L ≤ sec20X (CoreAssembly.conjClass K) z K K' ⊔
            conjSub ρ⁻¹ (sec20X (CoreAssembly.conjClass K) z K K') ⊔ Subgroup.zpowers ρ

@[expose] def FrameAInvConj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
      ∀ (L : Subgroup G) (s : G), (∃ zK, AViol (CoreAssembly.conjClass K) K L zK s) ∨
          (∃ zK, AViol (CoreAssembly.conjClass K) K' L zK s) →
        ∃ x ∈ sec20X (CoreAssembly.conjClass K) z K K', x * t * x⁻¹ = s

@[expose] def Frame20ACentX' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameCore G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Frame K K' J S R R' W V z t →
      ∀ a : G, AConf3 S K K' J z a →
        a ∈ centralizerModOdd (S : Subgroup G)
          (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) →
        ∀ x ∈ sec20X (CoreAssembly.conjClass K) z K K',
          a * x * a⁻¹ * x⁻¹ ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K')

end Defs

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
