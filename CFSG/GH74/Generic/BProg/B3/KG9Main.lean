module

public import CFSG.GH74.Generic.BProg.B3.KG9Lift

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace KG531BP

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (GHOddLie)

theorem kg531BPairNine_proved : KG531BPairNine := by
  intro X _ _ M hM hGH hO t htM ht2 L₁ L₂ h₁ h₂ s hsL₁ hs2 hsZ htL₂ F _ _ h9 he₁ he₂
  classical
  obtain ⟨e₁⟩ := he₁
  obtain ⟨e₂⟩ := he₂
  by_cases htZ : (⟨t, htM⟩ : ↥M) ∈ center ↥M
  ·
    set K : Subgroup X := centralizer ({t} : Set X) ⊓ M
    have hKM : K ≤ M := inf_le_right
    have hKeq : K = M := by
      refine le_antisymm hKM fun m hm => Subgroup.mem_inf.2 ⟨?_, hm⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_center_iff.mp htZ ⟨m, hm⟩
      exact congrArg Subtype.val this
    have hKq : IsQuasisimple ↥K := by
      rw [hKeq]
      exact hM
    have hLM : ∀ L : Subgroup X, IsPCompIn 2 K L → pPrimeCoreOf 2 L = ⊥ := by
      intro L hL
      have htop := eq_top_of_pComponent_quasisimple hKq hL.2
      have hLK : L = K := by
        refine le_antisymm hL.1 fun k hk => ?_
        have : (⟨k, hk⟩ : ↥K) ∈ L.subgroupOf K := by
          rw [htop]
          exact Subgroup.mem_top _
        exact this
      rw [hLK, hKeq, pPrimeCoreOf, hO, Subgroup.map_bot]
    exact ⟨hLM L₁ h₁, hLM L₂ h₂⟩
  by_cases hodl : GHOddLie (↥M ⧸ center ↥M)
  · exact ⟨KG9.pPrimeCoreOf_eq_bot_of_oddLie hM hodl hO htM ht2 htZ h₁ h9 e₁,
      KG9.pPrimeCoreOf_eq_bot_of_oddLie hM hodl hO htM ht2 htZ h₂ h9 e₂⟩
  · exact (kg531BPairOther_proved X M hM hGH hodl hO t htM ht2 htZ L₁ L₂ h₁ h₂ s hsL₁ hs2 hsZ
      htL₂ F (by rw [h9]; exact ⟨4, rfl⟩) (by omega) ⟨e₁⟩ ⟨e₂⟩).elim

end KG531BP

end CFSG.GH74.Generic.BProg.B3
