module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoSteps
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineTwoOneEscape
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoDickson
import CFSG.HardMathSupport.Timmesfeld.SporadicRank.UpperBound
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {X : Type} [Group X] [Finite X] {p : ℕ}

private theorem pRank_le_of_sylow_inf [Fact p.Prime] (R : Sylow p X) {L : Subgroup X}
    (hL : L.IsSubnormal) {k : ℕ} (hk : CFSG.Open.pRank p ((R : Subgroup X) ⊓ L) ≤ k) :
    CFSG.Open.pRank p L ≤ k := by
  have hp : p.Prime := Fact.out
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hL
  have hTop : CFSG.Open.pRank p (⊤ : Subgroup L) ≤ k := by
    refine CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_sylow hp (T : Subgroup L)
      (Sylow.card_eq_multiplicity T) fun E hET hE => ?_
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hE)
    have hle : E.map L.subtype ≤ (R : Subgroup X) ⊓ L := hT ▸ Subgroup.map_mono hET
    have hcard : Nat.card (E.map L.subtype) = p ^ j := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hj]
    have hjk := (CFSG.SectionRank.le_pRank hp.one_lt hle
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _) hcard).trans hk
    rw [hj]
    exact Nat.pow_le_pow_right hp.pos hjk
  have e : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← e, CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp L.subtype
    L.subtype_injective]
  exact hTop

@[expose] def AGL81SevenFourTwoComp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → CatalogSimpleSections X →
    primeComplementCore (G := X) p = ⊥ → ∀ P : Sylow p X, 3 ≤ Open.pRank p (P : Subgroup X) →
    ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ IsCyclic ((P : Subgroup X) ⊓ L : Subgroup X) →
    CFSG.layer X ⊔ GLBWeakCore p (P : Subgroup X) = ⊤

theorem agl81SevenFourTwoComp_of (hSch : KFactCatalogSchreier) (h713 : SevenOneThreeRankTwo) :
    AGL81SevenFourTwoComp := by
  intro X _ _ p hp hp2 hX hcore P h3 L hL hnc
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hH
  set Y := CFSG.layer X ⊔ GLBWeakCore p (P : Subgroup X) with hYdef
  have hWY : GLBWeakCore p (P : Subgroup X) ≤ Y := le_sup_right
  have hEY : CFSG.layer X ≤ Y := le_sup_left
  have hPY : (P : Subgroup X) ≤ Y := (subgroup_le_weakCore_of_rank p hp _ h3).trans hWY
  obtain ⟨hEL, hQ2⟩ := layer_eq_of_component hp hp2 hcore P hH hL hnc
  haveI := CFSG.LocalCores.layer_characteristic (G := X)
  haveI hEn : (CFSG.layer X).Normal := inferInstance
  set Q : Subgroup X := (P : Subgroup X) ⊓ CFSG.layer X with hQdef
  have hQP : Q ≤ P := inf_le_left
  have hPQ : (P : Subgroup X) ≤ Subgroup.normalizer (Q : Set X) :=
    (le_inf Subgroup.le_normalizer Subgroup.le_normalizer_of_normal).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQ2' : Open.pRank p Q = 2 := by rw [hQdef, hEL]; exact hQ2
  have hQY : ¬ Subgroup.normalizer (Q : Set X) ≤ Y := fun h =>
    hH (top_le_iff.mp (le_of_frattini P (N := ⊤) (K := CFSG.layer X) le_top le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hEn]) hEY h))
  obtain ⟨D, hDQ, hQD, hD⟩ :=
    exists_extraspecial_of_not_normalizer_le hp hp2 P hPY hWY h3 hQP hPQ hQ2' hQY
  have hDP : D ≤ P := hDQ.trans hQP
  have hPD : (P : Subgroup X) ≤ Subgroup.normalizer (D : Set X) := hPQ.trans hQD
  have hDY : ¬ Subgroup.normalizer (D : Set X) ≤ Y := fun h => hQY (hQD.trans h)
  obtain ⟨E, hED, hE, hEc, hZE, hPE⟩ := exists_normal_elemAbelian_sq_le hp2 P hDP hPD hD
  have hNE : Subgroup.normalizer (E : Set X) ≤ Y :=
    normalizer_le_of_normal_elemAbelian_sq hp P hPY hWY h3 hE hEc (hED.trans hDP) hPE
  have hcyc := isCyclic_inf_centralizer_of_not_le hp hp2 P hWY hDP hD hDY
  obtain ⟨e⟩ := exists_coords hD
  have hker : (centerQuotientAction D e).ker.map (Subgroup.normalizer (D : Set X)).subtype ≤ Y :=
    (map_ker_centerQuotientAction_le e hED hZE).trans hNE
  have hDE : D ≤ CFSG.layer X := hDQ.trans inf_le_right
  rcases map_closure_orderOf_eq (centerQuotientAction D e) with hI | hI | hI
  · exact hDY (normalizer_le_of_isPGroup_map_closure P e hPD hWY hPY h3 hker
      (by rw [hI]; exact IsPGroup.of_bot))
  · exact hDY (normalizer_le_of_isPGroup_map_closure P e hPD hWY hPY h3 hker
      (IsPGroup.of_card (n := 1) (by rw [hI, pow_one])))
  · rcases (show p = 3 ∨ 5 ≤ p by
        have := hp.two_le
        have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
        omega) with rfl | hp5
    ·
      have h3' := pRank_le_three_of_not_le P e hPD hWY hker hDY
      have hLc : CFSG.IsComponent (CFSG.layer X) := by
        rw [hEL]; exact (CFSG.isComponent_iff_open L).mpr hL
      have hCY : Subgroup.centralizer (CFSG.layer X : Set X) ≤ Y :=
        ((Subgroup.centralizer_le fun u hu => hDE (hED hu)).trans
          (Subgroup.centralizer_le_normalizer _)).trans hNE
      have hL3 : Open.pRank 3 (CFSG.layer X) = 2 := by
        refine le_antisymm (pRank_le_of_sylow_inf P (Subgroup.Normal.isSubnormal hEn)
          (by rw [← hQdef, hQ2'])) ?_
        rw [← hQ2']
        exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three inf_le_right
      exact hH (top_le_iff.mp (top_le_of_three h713 hX P hLc inferInstance hL3 hEY hCY hWY h3 h3'))
    · exact hDY (normalizer_le_of_map_closure_eq_statedSL hSch hX hp5 hcore P e
        ((show CFSG.layer X = L from hEL) ▸ (CFSG.isComponent_iff_open L).mpr hL) hDE hEY hPD
        hWY h3 hcyc hker hI)


theorem agl81SevenFourTwo_of_comp (h : AGL81SevenFourTwoComp) : AGL81SevenFourTwo := by
  intro X _ _ p hp hp2 hX hcore P h3 hnc
  by_contra hH
  obtain ⟨hLc, -⟩ := isComponent_layer hp hp2 hcore P h3 hnc hH
  exact hH (h X p hp hp2 hX hcore P h3 (CFSG.layer X) ((CFSG.isComponent_iff_open _).mp hLc) hnc)

theorem agl81SevenFourTwo_of (hSch : KFactCatalogSchreier) (h713 : SevenOneThreeRankTwo) :
    AGL81SevenFourTwo :=
  agl81SevenFourTwo_of_comp (agl81SevenFourTwoComp_of hSch h713)

end CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo
