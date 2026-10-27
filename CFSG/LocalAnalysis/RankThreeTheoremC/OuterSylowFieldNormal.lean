module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowGlue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type*} [Group X]

theorem sylow_normal_of_normal_isCyclic_index [Finite X] {p : ℕ} [Fact p.Prime]
    (N : Subgroup X) [N.Normal] (hcyc : IsCyclic ↥N) (hcop : ¬ p ∣ N.index)
    (S : Sylow p X) : (S : Subgroup X).Normal := by
  haveI : IsCyclic ↥N := hcyc
  haveI : Finite (X ⧸ N) := (finite_iff_subgroup_quotient N).mp inferInstance |>.2
  let T : Subgroup (X ⧸ N) := (S : Subgroup X).map (QuotientGroup.mk' N)
  have hTp : IsPGroup p T := by
    simpa [T] using S.isPGroup'.map (QuotientGroup.mk' N)
  have hTcard : Nat.card T ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact T.card_subgroup_dvd_card
  haveI : Finite T := inferInstance
  have hT1 : Nat.card T = 1 := by
    obtain ⟨n, hn⟩ := hTp.exists_card_eq
    have hpT : ¬ p ∣ Nat.card T := fun h => hcop (h.trans hTcard)
    have hn0 : n = 0 := by
      by_contra h
      exact hpT (hn ▸ dvd_pow_self p h)
    rw [hn, hn0, pow_zero]
  have hTbot : T = ⊥ := T.eq_bot_of_card_eq hT1
  have hSN : (S : Subgroup X) ≤ N := by
    have h : (S : Subgroup X).map (QuotientGroup.mk' N) = ⊥ := hTbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  refine Subgroup.normal_iff_map_conj_eq.mpr ?_
  intro g
  let K : Subgroup X := (S : Subgroup X).map (MulAut.conj g)
  have hKS : Nat.card K = Nat.card (S : Subgroup X) := by
    dsimp [K]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hKN : K ≤ N := by
    change (S : Subgroup X).map (MulAut.conj g) ≤ N
    have h := Subgroup.map_mono (f := (MulAut.conj g : X →* X)) hSN
    simpa only [Subgroup.Normal.map_conj_eq N g] using h
  have hKsub : K.subgroupOf N = (S : Subgroup X).subgroupOf N := by
    refine IsCyclic.subgroup_eq_iff_card_eq.mpr ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv]
    exact hKS
  have hK : K = (S : Subgroup X) := by
    have h := hKsub
    rw [Subgroup.subgroupOf_inj] at h
    rwa [inf_eq_left.mpr hKN, inf_eq_left.mpr hSN] at h
  simpa [K] using hK

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
