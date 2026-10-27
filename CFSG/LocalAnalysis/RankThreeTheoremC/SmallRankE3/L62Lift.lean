module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Quotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.LiftHeart
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.ThreePart

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)

theorem l62_triData {H : Type} [Group H] [Finite H] (hH : primeComplementCore (G := H) 3 = ⊥)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3) {L : Subgroup H} (hL : IsComponentOf L ⊤)
    {g : H} (hg3 : ∃ n : ℕ, g ^ 3 ^ n = 1) (hgL : g ∉ normalizer (L : Set H)) :
    ∃ L₂ L₃ : Subgroup H, TriData L L₂ L₃ g := by
  obtain ⟨hne12, hne13, hne23⟩ := conj_three_distinct hg3 hgL
  have hc2 : IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ := isComponentOf_map_conj hL g
  have hc3 : IsComponentOf (L.map (MulAut.conj (g * g)).toMonoidHom) ⊤ :=
    isComponentOf_map_conj hL (g * g)
  have hc4 : IsComponentOf ((L.map (MulAut.conj (g * g)).toMonoidHom).map
      (MulAut.conj g).toMonoidHom) ⊤ := isComponentOf_map_conj hc3 g
  have hcyc2 : (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      L.map (MulAut.conj (g * g)).toMonoidHom := cc_map_conj_map L g g
  have hinj : ∀ A B : Subgroup H,
      A.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj g).toMonoidHom → A = B :=
    fun A B h => Subgroup.map_injective (MulAut.conj g).injective h
  have h4 : (L.map (MulAut.conj (g * g)).toMonoidHom).map (MulAut.conj g).toMonoidHom = L := by
    by_contra hne4
    refine no_four_components hH hrank hL hc2 hc3 hc4 hne12.symm hne13.symm (Ne.symm hne4)
      hne23.symm ?_ ?_
    · intro h24
      exact hne13 (hinj _ _ h24).symm
    · intro h34
      apply hne23
      apply hinj
      rw [hcyc2]
      exact h34.symm
  refine ⟨L.map (MulAut.conj g).toMonoidHom, L.map (MulAut.conj (g * g)).toMonoidHom, ?_⟩
  refine ⟨⟨Group.isPerfect_def.mpr hL.2.2.1, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩,
    ⟨Group.isPerfect_def.mpr hc2.2.2.1, hc2.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hc2.2.2⟩,
    ⟨Group.isPerfect_def.mpr hc3.2.2.1, hc3.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hc3.2.2⟩,
    ?_, ?_, ?_, rfl, hcyc2, h4,
    exists_order_three_component hH hL, exists_order_three_component hH hc2,
    exists_order_three_component hH hc3⟩
  · intro a ha b hb
    exact component_commute hL hc2 hne12.symm ha hb
  · intro a ha c hc
    exact component_commute hL hc3 hne13.symm ha hc
  · intro b hb c hc
    exact component_commute hc2 hc3 hne23.symm hb hc

theorem l62_liftQ {X : Type} [Group X] [Finite X] {g : Bar X} {L : Subgroup (Bar X)}
    (hL : IsComponentOf L ⊤) (hg3 : ∃ n : ℕ, g ^ 3 ^ n = 1)
    (hgL : g ∉ normalizer (L : Set (Bar X)))
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar X)) ≤ 3) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hqd : q ∣ Nat.card (↥L ⧸ Subgroup.center ↥L))
    (hqM : ¬ q ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (↥L ⧸ Subgroup.center ↥L))) :
    3 ≤ CFSG.Open.pRank q (⊤ : Subgroup X) := by
  have hH : primeComplementCore (G := Bar X) 3 = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.primeComplementCore_bar (G := X)
  obtain ⟨L₂, L₃, hT⟩ := l62_triData hH hrk hL hg3 hgL
  have hker : ¬ 3 ∣ Nat.card (barMk X).ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (primeComplementCore_coprime 3)
  obtain ⟨n, hn⟩ := hg3
  obtain ⟨s, hsg, m, hs⟩ :=
    exists_three_element_lift (barMk X) (QuotientGroup.mk'_surjective _) hker hn
  have hT' : TriData L L₂ L₃ (barMk X s) := by rw [hsg]; exact hT
  exact lift_heart (barMk X) (QuotientGroup.mk'_surjective _) hker s ⟨m, hs⟩ hT' hq hq5 hqd hqM

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
