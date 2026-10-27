module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModMap
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QTRankInvProof

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

open Subgroup CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem invConj_J :
    InvConj (⊤ : Subgroup J) (Eg uJ 11) := by
  intro a _ ha
  by_cases h1 : a = 1
  · exact ⟨1, mem_top _, by simp [h1]⟩
  · have key : ∀ c : ℕ, IsConj (eta uJ 11 c) a →
        ∃ l ∈ (⊤ : Subgroup J), l * a * l⁻¹ ∈ Eg uJ 11 := by
      intro c hc
      obtain ⟨k, hk⟩ := isConj_iff.1 hc
      refine ⟨k⁻¹, mem_top _, ?_⟩
      have : k⁻¹ * a * k⁻¹⁻¹ = eta uJ 11 c := by rw [← hk]; group
      rw [this]
      exact eta_mem_Eg 11 le_rfl c
    rcases inv_conj_root j4Facts ha h1 with h | h
    · exact key 1 h
    · exact key 3 h

end CFSG.EvenSporadicStandard.J4Std.DataMod

namespace CFSG.EvenSporadicStandard.J4Std

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem invConj_J4
    {G : Type} [Group G]
    (ι : J →* G) (hι : Function.Injective ι) : InvConj ι.range ((Eg uJ 11).map ι) :=
  DataMod.invConj_map ι hι _ DataMod.invConj_J

end CFSG.EvenSporadicStandard.J4Std
