module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF2Lift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResF
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinResLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform

namespace Thm4Twin


@[expose] def Thm4TwinF.ExitModel (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ J L L₀ : Subgroup G, F2Config J L L₀ →
    ∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ (z : G)
      (hz : IsUniqueInvolution K z),
      (oddCoreImg (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ ∨
        ∃ (W : Subgroup G) (hKW : K ≤ W), IsSubnormal W ⊤ ∧
          (⨆ x : W, conjSub (x : G) K) = W ∧ F2.ExitSec W K hKW z hz) → False

theorem thm4TwinRes2F'Tw_of_exitModel {n : ℕ} (hT : Thm1RTwinLiftSetBelow n) (hB : TightBelow n)
    (h4 : Thm4BelowU 3 1 n) (hE : Thm4TwinF.ExitModel n) : Thm4TwinRes2F'Tw 3 n := by
  intro G _ _ hG J L hm hgen htw hno L₀ hL₀ hn hlay hfit hZ hC hmem
  have hc : F2Config J L L₀ := ⟨hm, hgen, htw, hno, hL₀, hn, hlay, hfit, hZ, hC, hmem⟩
  set Δ := CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L with hΔ
  have hodd : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
    intro K hK z hz
    by_contra hne
    exact hE G hG J L L₀ hc K hK z hz (Or.inl hne)
  have h2 : ∀ K ∈ Δ, IsPGroup 2 K := fun K hK => by
    obtain ⟨z, hz⟩ := (hm.hyp.hyp.omega1 K hK).1
    exact isPGroup_of_oddCent hm.hyp.hyp hK hz (hodd K hK z hz) (hm.hyp.twoGroup K hK)
  have hq8 : ∀ K ∈ Δ, Nonempty (↥K ≃* QuaternionGroup 2) := fun K hK => by
    have hKS : IsSylow2In K K := ⟨le_rfl, h2 K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    exact hm.hyp.quat K hK K hKS
  have hl : HasLifts Δ := by
    intro K hK
    obtain ⟨z, hz⟩ := (hm.hyp.hyp.omega1 K hK).1
    rcases F2.exists_lift_or_exit hT hB hG hm.hyp.odd hm.hyp.hyp h2 hq8 hm.hyp.aEmpty hno hK hz
      with ⟨L', hL'⟩ | ⟨W, hKW, hWs, hWg, hex⟩
    · exact ⟨L', z, hL'⟩
    · exact (hE G hG J L L₀ hc K hK z hz (Or.inr ⟨W, hKW, hWs, hWg, hex⟩)).elim
  exact hm.false_of_lifts h4 hG hodd hl

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
