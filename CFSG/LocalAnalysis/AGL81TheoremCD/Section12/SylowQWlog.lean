module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenProof

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M Q H : Subgroup G} {p : ℕ}

theorem exists_sylow_QSet_of_twelveCtx
    (h : TwelveCtx G M p Q H)
    (hI : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineNineOneInput) :
    ∃ Q' : Subgroup G, Q ≤ Q' ∧ Q' ∈ CFSG.LocalAnalysis.RankThreeUC.AGL81C.QSet M p ∧
      CFSG.ABGLocalTools.IsSylowOf p Q' H := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨E₀, hE₀Q, hE₀, hE₀c, hΓ⟩ := h.exists_E_sq
  have hd := h.hypCGen hE₀Q hE₀ hE₀c hΓ
  have hU : NineNineOne M p := hI G M E₀ H E₀ p hd.toNineSettingGen hd.not_mem_sigmaM
  obtain ⟨P, hP, hQP⟩ := exists_isSylowOf_ge (le_inf h.Q_le_H h.Q_le_M) h.Q_isPGroup
  have hPH : CFSG.ABGLocalTools.IsSylowOf p P H :=
    (isSylowOf_of_NineNineOne h.maxLocal h.mem_QSet h.Q_le_H hd.not_mem_sigmaM hU hP).1
  exact ⟨P, hQP,
    ⟨h.p_prime, h.p_odd, hP.le.trans inf_le_right, hP.isPGroup,
      Or.inr ⟨E₀, hE₀Q.trans hQP, hE₀, hE₀c, hΓ⟩⟩,
    hPH⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
