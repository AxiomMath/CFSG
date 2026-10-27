module

import CFSG.Sporadic.ON
import CFSG.Sporadic.Fi22.Simple
import CFSG.Sporadic.Fi24.Simple
import CFSG.RankThree.PartOne.CTP.SporadicOrders
import CFSG.Monster.Existence.BabyOrder
import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
public import CFSG.Open.MonsterDefs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Fi23.Simple

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.Sporadic


theorem three_spor_order_nine
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    {L₀ : Type} [Group L₀] {s : TauCeti.SporadicName} (hs : P1ThreeSporList 3 s)
    (e : L₀ ≃* (TauCeti.CFSGIndex.sporadic s).Group) (h5 : ¬ 3 ^ 5 ∣ Nat.card L₀)
    (hA : 181440 ∣ Nat.card L₀) : s = .ONan ∧ Nat.card L₀ = 460815505920 := by
  obtain ⟨f⟩ := hbr s
  have hc : ∀ {N : ℕ}, Nat.card (NativeSporadic.Carrier s) = N → Nat.card L₀ = N :=
    fun hN => (Nat.card_congr (e.trans f.symm).toEquiv).trans hN
  have hMc : Nat.card (NativeSporadic.Carrier .M) = Open.monsterOrder :=
    (Nat.card_congr Bridge.Y443.commutatorMulEquiv.toEquiv).trans hMcard
  rcases hs with ⟨-, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl⟩ | ⟨h5', -⟩ | ⟨h7, -⟩ | ⟨h13, -⟩
  · exact absurd (by rw [hc J3.card_J3]; decide) h5
  · exact absurd (by rw [hc McL.card_McL]; decide) h5
  · exact absurd (by rw [hc Suz.card_Suz]; decide) h5
  · exact ⟨rfl, hc ON.card_ON⟩
  · exact absurd (by rw [hc Co1.card_Co1]; decide) h5
  · exact absurd (by rw [hc Co2.card_Co2]; decide) h5
  · exact absurd (by rw [hc Co3.card_Co3]; decide) h5
  · exact absurd (by rw [hc Fi22.card_Fi22]; decide) h5
  · exact absurd (by rw [hc Fi23.card_Fi23]; decide) h5
  · exact absurd (by rw [hc Fi24.card_Fi24prime]; decide) h5
  · exact absurd (by rw [hc HN.card_HN]; decide) h5
  · exact absurd (by rw [hc Ly.card_Ly]; decide) h5
  · exact absurd (by rw [hc RankThree.PartOne.CTP.card_Th]; decide) h5
  · exact absurd (by rw [hc Monster.Existence.card_nativeB]; decide) h5
  · exact absurd (by rw [hc hMc]; decide) h5
  · rw [hc Mathieu.card_M22] at hA
    exact absurd hA (by decide)
  · omega
  · omega
  · omega

end CFSG.AGLEmbedding
