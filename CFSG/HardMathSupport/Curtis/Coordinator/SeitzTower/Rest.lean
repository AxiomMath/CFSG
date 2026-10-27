module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.ExcFG
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Suzuki
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.ReeG2
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.ReeF4
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Tits
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TrialityD4
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Symplectic
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TwistedE6
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Orthogonal
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TwistedA
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.E8

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open TauCeti CFSG.AGLEmbedding

theorem p1OffCharAlmostSimpleNonNormalAt_rest
    (d : ValidLieTypeIndex) (hA : ∀ (m : ℕ) (q : PrimePower), d.1 ≠ .A m q)
    (hE6 : ∀ q : PrimePower, d.1 ≠ .E6 q) (hE7 : ∀ q : PrimePower, d.1 ≠ .E7 q) :
    P1OffCharAlmostSimpleNonNormalAt d := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A m q => exact absurd rfl (hA m q)
  | twistedA n q => exact p1OffCharAlmostSimpleNonNormalAt_twistedA hv
  | B r q =>
    have hr : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1
      ((LieTypeIndex.valid_iff _).1 hv).1).1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact p1OffCharAlmostSimpleNonNormalAt_B_two hv
    · by_cases hq : q.p = 2
      · exact p1OffCharAlmostSimpleNonNormalAt_B_even hr3 hq hv
      · exact p1OffCharAlmostSimpleNonNormalAt_B_odd hv hr3 hq
  | C r q => exact p1OffCharAlmostSimpleNonNormalAt_C hv
  | D n q => exact p1OffCharAlmostSimpleNonNormalAt_D hv
  | twistedD n q => exact p1OffCharAlmostSimpleNonNormalAt_twistedD hv
  | E6 q => exact absurd rfl (hE6 q)
  | E7 q => exact absurd rfl (hE7 q)
  | E8 q => exact p1OffCharAlmostSimpleNonNormalAt_E8 hv
  | F4 q => exact p1OffCharAlmostSimpleNonNormalAt_F4 hv
  | G2 q => exact p1OffCharAlmostSimpleNonNormalAt_G2 hv
  | twistedE6 q => exact p1OffCharAlmostSimpleNonNormalAt_twistedE6 hv
  | trialityD4 q => exact p1OffCharAlmostSimpleNonNormalAt_trialityD4 hv
  | suzuki m => exact p1OffCharAlmostSimpleNonNormalAt_suzuki hv
  | reeG2 m => exact p1OffCharAlmostSimpleNonNormalAt_reeG2 hv
  | reeF4 m => exact p1OffCharAlmostSimpleNonNormalAt_reeF4 hv
  | tits => exact p1OffCharAlmostSimpleNonNormalAt_tits hv

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
