module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf6Lift
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Lift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Tz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform

namespace TwinDisc


@[expose] def DStarExitQ8 (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), HypOmegaGen Φ →
    (∀ J ∈ Φ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) →
    (∀ J ∈ Φ, ∀ P : Subgroup X, IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup 2)) →
    classicalInvolutionOddCore X = ⊥ → (∀ J ∈ Φ, AEmpty Φ J) → omegaGen Φ = ⊤ →
    (∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) → TwinTriple Φ →
    (∃ K ∈ Φ, ∃ (z : X) (hz : IsUniqueInvolution K z),
      oddCoreImg (Subgroup.centralizer ({z} : Set X)) ≠ ⊥ ∨ TightInO2 z ∨
        ∃ (W : Subgroup X) (hKW : K ≤ W), IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : X) K) = W ∧
          Thm4Twin.F2.ExitSec W K hKW z hz) →
    T3.DStarConnected Φ

theorem dstarConnectedTwinQ8Below_of_exit {n : ℕ} (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hEx : DStarExitQ8 n) : DStarConnectedTwinQ8Below n := by
  intro X _ _ hlt Φ hΩ h2' hq hO hA hgen htrans htt
  by_cases hex : ∃ K ∈ Φ, ∃ (z : X) (hz : IsUniqueInvolution K z),
      oddCoreImg (Subgroup.centralizer ({z} : Set X)) ≠ ⊥ ∨ TightInO2 z ∨
        ∃ (W : Subgroup X) (hKW : K ≤ W), IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : X) K) = W ∧
          Thm4Twin.F2.ExitSec W K hKW z hz
  · exact hEx X hlt Φ hΩ h2' hq hO hA hgen htrans htt hex
  push Not at hex
  have hodd : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥ := fun K hK z hz => (hex K hK z hz).1
  have hno : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → ¬ TightInO2 z :=
    fun K hK z hz => (hex K hK z hz).2.1
  have h2 : ∀ K ∈ Φ, IsPGroup 2 K := fun K hK => by
    obtain ⟨z, hz⟩ := (hΩ.omega1 K hK).1
    exact isPGroup_of_oddCent hΩ hK hz (hodd K hK z hz) (h2' K hK)
  have hq8 : ∀ K ∈ Φ, Nonempty (↥K ≃* QuaternionGroup 2) := fun K hK => by
    have hKS : IsSylow2In K K := ⟨le_rfl, h2 K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    exact hq K hK K hKS
  have hl : HasLifts Φ := by
    intro K hK
    obtain ⟨z, hz⟩ := (hΩ.omega1 K hK).1
    rcases Thm4Twin.F2.exists_lift_or_exit (Thm1RTwinLiftSetEBelow.toSet (hP.twin rfl)) (tightBelowR_three_iff.mp hP.tbelow)
      hlt hO hΩ h2 hq8 hA hno hK hz with ⟨L', hL'⟩ | ⟨W, hKW, hWs, hWg, hexit⟩
    · exact ⟨L', z, hL'⟩
    · exact absurd hexit ((hex K hK z hz).2.2 W hKW hWs hWg)
  have hexs : ExactSylow Φ := ExactSylow.of_oddCoreIn_eq_bot fun J hJ L u h =>
    hodd J hJ u h.inv
  exact dstarConnected_of_lifts hcit hlt hΩ h2 hl hexs hO hgen htrans hA htt

structure TwinDiscInputsPf6 (n : ℕ) : Prop where
  thmE : TwinThmE n
  base : TwinDiscBase n
  c13Exc : Disc13NExc n
  c14Exc : Disc14NExc n
  c14AltExc : Disc14AltExc n
  normCent : DiscNormCent n
  thm4 : Thm4RTwinBelow 3 n
  cit : CIT3Below n
  pkg : TL4.TightBelowRPlus 3 n
  exit : DStarExitQ8 n

theorem TwinDiscInputsPf6.toPf5 {n : ℕ} (I : TwinDiscInputsPf6 n) : TwinDiscInputsPf5 n where
  thmE := I.thmE
  base := I.base
  c13Exc := I.c13Exc
  c14Exc := I.c14Exc
  c14AltExc := I.c14AltExc
  normCent := I.normCent
  thm4 := I.thm4
  model := dstarConnectedTwinQ8Below_of_exit I.cit I.pkg I.exit

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
