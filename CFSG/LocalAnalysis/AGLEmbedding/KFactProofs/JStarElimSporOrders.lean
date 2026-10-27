module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
public import CFSG.Open.MonsterDefs
import CFSG.Sporadic.ON
import CFSG.Sporadic.Fi22.Simple
import CFSG.Sporadic.Fi24.Simple
import CFSG.RankThree.PartOne.CTP.SporadicOrders
import CFSG.Monster.Existence.BabyOrder
import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Fi23.Simple

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.Sporadic


theorem three_spor_order
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    {L₀ : Type} [Group L₀] {s : TauCeti.SporadicName} (hs : P1ThreeSporList 3 s)
    (e : L₀ ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    (s = .J3 ∧ Nat.card L₀ = 50232960) ∨ 3 ^ 6 ∣ Nat.card L₀ ∨
      (¬ 50232960 ∣ Nat.card L₀ ∧ ¬ 1056706560 ∣ Nat.card L₀) := by
  obtain ⟨f⟩ := hbr s
  have hc : ∀ {N : ℕ}, Nat.card (NativeSporadic.Carrier s) = N → Nat.card L₀ = N :=
    fun hN => (Nat.card_congr (e.trans f.symm).toEquiv).trans hN
  have hMc : Nat.card (NativeSporadic.Carrier .M) = Open.monsterOrder :=
    (Nat.card_congr Bridge.Y443.commutatorMulEquiv.toEquiv).trans hMcard
  rcases hs with ⟨-, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl⟩ | ⟨h5, -⟩ | ⟨h7, -⟩ | ⟨h13, -⟩
  · exact Or.inl ⟨rfl, hc J3.card_J3⟩
  · exact Or.inr (by rw [hc McL.card_McL]; decide)
  · exact Or.inr (by rw [hc Suz.card_Suz]; decide)
  · exact Or.inr (by rw [hc ON.card_ON]; decide)
  · exact Or.inr (by rw [hc Co1.card_Co1]; decide)
  · exact Or.inr (by rw [hc Co2.card_Co2]; decide)
  · exact Or.inr (by rw [hc Co3.card_Co3]; decide)
  · exact Or.inr (by rw [hc Fi22.card_Fi22]; decide)
  · exact Or.inr (by rw [hc Fi23.card_Fi23]; decide)
  · exact Or.inr (by rw [hc Fi24.card_Fi24prime]; decide)
  · exact Or.inr (by rw [hc HN.card_HN]; decide)
  · exact Or.inr (by rw [hc Ly.card_Ly]; decide)
  · exact Or.inr (by rw [hc RankThree.PartOne.CTP.card_Th]; decide)
  · exact Or.inr (by rw [hc Monster.Existence.card_nativeB]; decide)
  · exact Or.inr (by rw [hc hMc]; decide)
  · exact Or.inr (by rw [hc Mathieu.card_M22]; decide)
  · omega
  · omega
  · omega

theorem five_spor_order
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    {L₀ : Type} [Group L₀] {s : TauCeti.SporadicName} (hs : P1ThreeSporList 5 s)
    (e : L₀ ≃* (TauCeti.CFSGIndex.sporadic s).Group) : ¬ 331 ∣ Nat.card L₀ := by
  obtain ⟨f⟩ := hbr s
  have hc : ∀ {N : ℕ}, Nat.card (NativeSporadic.Carrier s) = N → Nat.card L₀ = N :=
    fun hN => (Nat.card_congr (e.trans f.symm).toEquiv).trans hN
  have hMc : Nat.card (NativeSporadic.Carrier .M) = Open.monsterOrder :=
    (Nat.card_congr Bridge.Y443.commutatorMulEquiv.toEquiv).trans hMcard
  rcases hs with ⟨h3, -⟩ | ⟨-, rfl | rfl | rfl | rfl | rfl⟩ | ⟨h7, -⟩ | ⟨h13, -⟩
  · omega
  · rw [hc Co1.card_Co1]; decide
  · rw [hc Ly.card_Ly]; decide
  · rw [hc HN.card_HN]; decide
  · rw [hc Monster.Existence.card_nativeB]; decide
  · rw [hc hMc]; decide
  · omega
  · omega

end CFSG.AGLEmbedding
