module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Heis
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders

public section

open CFSG.Open

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

open CFSG.Blueprint
open CFSG.AGLEmbedding (sporOrd)

@[expose] def SporCarrierOrders : Prop :=
  ∀ s : TauCeti.SporadicName, Nat.card (NativeSporadic.Carrier s) = sporOrd s

theorem Data.five_pow_three_dvd_card {K : Type} [Group K] [Finite K] {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (hD : Data K Q x J₁ J₂) : 5 ^ 3 ∣ Nat.card K := by
  obtain ⟨E, -, -, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5) (Q : Subgroup K)
  rw [hD.rank] at hcard
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card E

theorem i1434SporCase_of_tables (hord : SporCarrierOrders) (hnon : ∀ s : TauCeti.SporadicName, 5 ^ 3
    ∣ sporOrd s → HasNonabelianFiveSubgroup (NativeSporadic.Carrier s)) :
    I1434SporCase := by
  intro K _ _ ⟨s, ⟨e⟩⟩ Q x J₁ J₂ hD
  have hcard : Nat.card K = sporOrd s := (Nat.card_congr e.toEquiv).trans (hord s)
  have h5 : 5 ^ 3 ∣ sporOrd s := hcard ▸ hD.five_pow_three_dvd_card
  exact hD.false_of_hasNonabelianFiveSubgroup
    (HasNonabelianFiveSubgroup.of_mulEquiv e.symm (hnon s h5))

theorem five_pow_three_dvd_sporOrd_iff (s : TauCeti.SporadicName) :
    5 ^ 3 ∣ sporOrd s ↔ (s = .HS ∨ s = .McL ∨ s = .Ru ∨ s = .Co3 ∨ s = .Co2 ∨ s = .Th ∨
      s = .Co1 ∨ s = .HN ∨ s = .Ly ∨ s = .B ∨ s = .M) := by
  cases s <;> simp [sporOrd] <;> decide

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
