module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Psi1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1HO2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1RegM

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_reg_data (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∃ (ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)) (lab : G → Fin 16)
      (P : Subgroup (Equiv.Perm (Fin 16))), Y7AReg c ψ lab P := by
  obtain ⟨ψ, lab, hψ⟩ := y7a_psi_data c hH hF
  obtain ⟨P, hPle, hPconj, hP2, hPcard, hPtrans, hPmax⟩ :=
    y7a_reg16_max ψ.range hψ.trans hψ.card (y7a_hO2 c hH ψ lab hψ)
  exact ⟨ψ, lab, P, ⟨hψ, hPle, hPconj, hP2, hPcard, hPtrans, hPmax⟩⟩

end CFSG.OddStandard.HigherRank.YamadaG23
