module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Config
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Tight

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.EvenSmallLie

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_sylow_dvd_four_of_facts (h : StdHyp G L)
    (hZ : ∀ z ∈ center L, z ^ 2 = 1)
    (hout : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index ∣ 2)
    (hOF : OddFixFourth (L ⧸ center L)) (hFG : FoursGroupCondition L)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S ∣ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset := h.toStandardSetting
  have hS := hset.isCyclic_sylow S
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
  by_contra hne
  have hn3 : 3 ≤ n := by
    by_contra hlt
    apply hne
    rw [hn]
    interval_cases n <;> norm_num
  have hS4 : 4 ≤ Nat.card S := by
    rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hall : ∀ g : G, g ∉ normalizer (L : Set G) → ∀ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) →
      IsPGroup 2 P → Nat.card P ≤ 2
  · exact hset.false_of_forall_card_le_two hFG S hS4 hall
  · push Not at hall
    obtain ⟨g, hg, P, hP, hP2, hPcard⟩ := hall
    have hP4 : 4 ≤ Nat.card P := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP2
      rw [hm] at hPcard ⊢
      rcases m with _ | _ | m
      · norm_num at hPcard
      · norm_num at hPcard
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨g', hg', R, T, hRC, hR, hRcard, hTg, hTN, hT, hTcard, hRT⟩ :=
      exists_full_conj_centralized hset.standard S hS hg (hP.trans inf_le_left)
        (hP.trans inf_le_right) hP2 hP4
    obtain ⟨s, m, hm2, hmS, hs, hsT, hTcyc, hsN, hTC, hnorm⟩ :=
      h.exists_tight_cyclic S hS hS4 hg' hTg hTN hT hTcard
    have hmn : m = n := Nat.pow_right_injective le_rfl (hmS.symm.trans hn)
    exact h.false_of_tight_config_ge8 hZ hout hOF (by omega) hT hTcyc hsT hs hsN hTC hnorm

end CFSG.EvenSporadicStandard.TwoHS
