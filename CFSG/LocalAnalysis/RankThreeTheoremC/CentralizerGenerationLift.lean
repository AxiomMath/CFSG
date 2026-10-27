module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem hasPrimeConstraint_of_quotient {p : ℕ} {H : Type*} [Group H] [Finite H]
    (h : HasPrimeConstraint (G := H ⧸ primeComplementCore (G := H) p) p) :
    HasPrimeConstraint (G := H) p := by
  obtain ⟨N', hN', hNp, hNc⟩ := h
  set B := primeComplementCore (G := H ⧸ primeComplementCore (G := H) p) p with hB
  have hB1 : B = ⊥ := primeComplementCore_quotient_eq_bot p
  set ρ : (H ⧸ primeComplementCore (G := H) p) →* _ ⧸ B := QuotientGroup.mk' B with hρ
  have hker : ρ.ker = ⊥ := by rw [hρ, QuotientGroup.ker_mk', hB1]
  have hsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective B
  have hpg : IsPGroup p ρ.ker := by rw [hker]; exact IsPGroup.of_bot
  refine ⟨N'.comap ρ, hN'.comap ρ, hNp.comap_of_ker_isPGroup ρ hpg, fun x hx => ?_⟩
  refine hNc ?_
  rw [mem_centralizer_iff]
  intro n' hn'
  obtain ⟨n, hn, rfl⟩ : n' ∈ (N'.comap ρ).map ρ := by
    rw [Subgroup.map_comap_eq_self_of_surjective hsurj]; exact hn'
  have := mem_centralizer_iff.1 hx n hn
  show ρ n * ρ x = ρ x * ρ n
  rw [← map_mul, ← map_mul, this]

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.isNonabelianPlane_map {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {P : Sylow p G} {M D : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hD : ¬ IsMulCommutative D) {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H)
    (O : Subgroup H) [O.Normal] (hO : p.Coprime (Nat.card O)) :
    IsNonabelianPlane p (((P : Subgroup G).subgroupOf H).map (QuotientGroup.mk' O))
      ((D.subgroupOf H).map (QuotientGroup.mk' O)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hDH : D ≤ H := hDP.trans hPH
  have hDHP : D.subgroupOf H ≤ (P : Subgroup G).subgroupOf H := fun x hx => hDP hx
  have hPp : IsPGroup p ((P : Subgroup G).subgroupOf H) := P.isPGroup'.comap_subtype
  have hrank : CFSG.Open.pRank p ((D.subgroupOf H).map (QuotientGroup.mk' O) ⊔
      (((P : Subgroup G).subgroupOf H).map (QuotientGroup.mk' O) ⊓ centralizer
        (((D.subgroupOf H).map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) : Set (H ⧸ O)))) ≤ 2 := by
    refine (pRank_map_sup_inf_centralizer_le_pRank hp O hO hPp hDHP).trans ?_
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp H.subtype
      H.subtype_injective]
    refine le_trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp ?_)
      hext.product_rank_eq.le
    rw [Subgroup.map_sup]
    refine sup_le_sup (map_subgroupOf_eq_of_le hDH).le ?_
    refine le_inf ?_ ?_
    · exact (Subgroup.map_mono inf_le_left).trans (map_subgroupOf_eq_of_le hPH).le
    · refine (Subgroup.map_mono inf_le_right).trans ?_
      refine (CFSG.AGLEmbedding.map_subtype_centralizer_le _).trans ?_
      rw [map_subgroupOf_eq_of_le hDH]
  refine ⟨Subgroup.map_mono hDHP, ?_, ?_, hrank⟩
  · intro hc
    apply hD
    rw [isMulCommutative_iff]
    intro a b
    have haH : (⟨a, hDH a.2⟩ : H) ∈ D.subgroupOf H := a.2
    have hbH : (⟨b, hDH b.2⟩ : H) ∈ D.subgroupOf H := b.2
    have hcomm := congrArg Subtype.val ((isMulCommutative_iff.mp hc)
      ⟨_, mem_map_of_mem (QuotientGroup.mk' O) haH⟩
      ⟨_, mem_map_of_mem (QuotientGroup.mk' O) hbH⟩)
    have hab := CFSG.AGLEmbedding.eq_of_mk_eq_of_isPGroup hp O hO hPp
      (mul_mem (hDHP haH) (hDHP hbH)) (mul_mem (hDHP hbH) (hDHP haH))
      (by rw [map_mul, map_mul]; exact hcomm)
    have hab' : (a : G) * b = b * a := congrArg Subtype.val hab
    exact Subtype.ext hab'
  · rintro _ ⟨d, hd, rfl⟩
    have hdp : (d : G) ^ p = 1 := (hext.pow_eq_one_and_commutator_mem hp hodd).1 d hd
    rw [← map_pow, show d ^ p = 1 from Subtype.ext hdp, map_one]

end CFSG.LocalAnalysis.RankThreeTheoremC
