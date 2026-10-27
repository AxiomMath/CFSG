module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenE612
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M0

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace Disconnected.AschTight

namespace Sec7

theorem l6_12_mod (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (hP : Asc77.PartIHyp Ω)
    (htr : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (S : Sylow 2 G) :
    let M : Subgroup G := ⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧
      U ≤ (S : Subgroup G)}, U
    (∃ η ∈ etaG Ω, (∀ m ∈ M, ∀ U ∈ η, conjSub m U ∈ η) ∧
      (∀ η' ∈ etaG Ω, (∀ m ∈ M, ∀ U ∈ η', conjSub m U ∈ η') → η' = η) ∧
      ∀ g : G, (∀ U ∈ η, conjSub g U ≤ (S : Subgroup G)) → ∀ U ∈ η, conjSub g U ∈ η) ∨
    ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (S : Subgroup G) ∈ RSet Ω :=
  Q3.Q3T6.Gen612.l6_12_on hP.hyp (fun S => Sec6Gen.exists_invariant_mem_etaSet hP.hyp S)
    (fun _ ⟨_, hS, hinv⟩ =>
      (Sec6Gen.eta_abelian_of_cyc66 hP.hyp (Sec6Gen.cyc66 hP.hyp) hS hinv).1)
    (Sec6Gen.l6_11Gen G _ hP.hyp) htr S

end Sec7

end Disconnected.AschTight

end CFSG.ClassicalInvolution.Q8P

