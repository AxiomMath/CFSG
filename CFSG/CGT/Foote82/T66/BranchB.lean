module

public import CFSG.CGT.Foote82.T66.CitedBB
public import CFSG.CGT.Foote82.T66.BranchBBasic
import CFSG.CGT.Foote82.T66.BranchBAlt
import CFSG.CGT.Foote82.T66.BranchBOmega
public import CFSG.CGT.Foote82.T66.Steps

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

theorem lemma51 (hN : OmegaMinusSixNormalizer) (hG1 : OmegaMinusSixA6Centralizer) : Lemma51 := by
  intro V _ _ _ G L z hstd hrank v hv hv0 hns
  have h : BranchB.Hyp G L z v := ⟨hstd, hrank, hv, hv0, hns⟩
  rcases h.concl with h1 | ⟨n, k, hn, hk, eL, hheart⟩ | ⟨eL, hΩ⟩
  · exact absurd h1 h.map_L_ne_range
  · have hk1 := h.k_eq_one hn hk eL hheart
    subst hk1
    obtain ⟨ψ, hψ⟩ := h.caseIData hn eL hheart
    exact Or.inl ⟨_, n, ψ, hψ⟩
  · obtain ⟨ψ, hψ⟩ := h.caseIIData hN hG1 eL hΩ
    exact Or.inr ⟨_, ψ, hψ⟩

theorem caseMC1_of (h51 : Lemma51) (hA : BranchAFalse) (hI : CaseIFalse) (hII : CaseIIFalse) :
    CaseMC1 := by
  intro V _ _ _ G L s hstd hrank
  by_cases hall : ∀ v ∈ commSpace (Subgroup.zpowers s) ⊤, v ≠ 0 →
      G ⊓ vFix v ≤ Subgroup.normalizer (L : Set (GLV V))
  · exact hA V G L s hstd hrank hall
  · push Not at hall
    obtain ⟨v, hv, hv0, hnot⟩ := hall
    have hns : ¬ IsSubnormal L (G ⊓ vFix v) := fun hsub =>
      hnot (BranchB.le_normalizer_of_isSubnormal hstd hsub)
    rcases h51 V G L s hstd hrank v hv hv0 hns with ⟨H₁, n, ψ, hd⟩ | ⟨H₁, ψ, hd⟩
    · exact hI V G L s v H₁ n ψ hstd hrank hv hd
    · exact hII V G L s v H₁ ψ hstd hrank hv hd

end CFSG.CGT.Foote82
