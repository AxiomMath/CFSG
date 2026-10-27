module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Constr
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Center

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem kd291_comp_data {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSp : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    {X : Type} [Group X] [Finite X] (P : Sylow p X) {x : X}
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections X) (hxP : x ∈ (P : Subgroup X))
    (hx1 : x ≠ 1) (hx5 : x ^ p = 1) (hP : Open.pRank p (P : Subgroup X) = 3)
    (hC : Open.pRank p (centralizer ({x} : Set X)) = 2)
    (hcomp : ∃ L : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf L ⊤ ∧
      ∀ K : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf K ⊤ → K = L) :
    ∃ L : Subgroup (X ⧸ primeComplementCore (G := X) p), L.Normal ∧
      CFSG.Open.IsQuasisimple ↥L ∧ IsPGroup p (center ↥L) ∧ center ↥L = ⊥ ∧ IsSimpleGroup ↥L ∧
      (∃ a b : ↥L, a * b ≠ b * a) ∧ IsCatalogGroup ↥L ∧
      centralizer (L : Set (X ⧸ primeComplementCore (G := X) p)) = ⊥ ∧
      (∀ z : X, z ∈ centralizer ((P : Subgroup X) : Set X) → z ∈ (P : Subgroup X) → z ^ p = 1 →
        (QuotientGroup.mk z : X ⧸ primeComplementCore (G := X) p) ∈ L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxo : orderOf x = p := orderOf_eq_prime hx5 hx1
  have hcatY : CFSG.AGLEmbedding.CatalogSimpleSections
      (X ⧸ primeComplementCore (G := X) p) := hcat.quotient _
  have hY1 : primeComplementCore (G := X ⧸ primeComplementCore (G := X) p) p = ⊥ :=
    primeComplementCore_quotient_eq_bot p
  have hY3 : Open.pRank p (⊤ : Subgroup (X ⧸ primeComplementCore (G := X) p)) = 3 :=
    kd291_pRank_quot hp P hP
  obtain ⟨Q, hQ⟩ := kd291_exists_sylow_map hp P
  have hxQ : (QuotientGroup.mk x : X ⧸ primeComplementCore (G := X) p) ∈
      (Q : Subgroup (X ⧸ primeComplementCore (G := X) p)) := by
    rw [hQ]
    exact Subgroup.mem_map_of_mem _ hxP
  have hxo' := kd291_orderOf_mk hp hxo
  have hC' := kd291_pRank_cent_quot hp hxo hC.le
  have hQrank : 3 ≤ Open.pRank p (Q : Subgroup (X ⧸ primeComplementCore (G := X) p)) := by
    rw [(CFSG.SectionRank.pRank_sylow Q).1, hY3]
  obtain ⟨w, hwQ, hwo, hwc, hwu⟩ := kd291_step0a hp Q hxQ hxo' hQrank hC'
  have hwN : ∀ N : Subgroup (X ⧸ primeComplementCore (G := X) p), N.Normal → N ≠ ⊥ → w ∈ N :=
    fun N hN hne => by
      haveI := hN
      exact kd291_step0b hp hY1 Q hwQ hwo hwc hwu N hne
  obtain ⟨L, hL, hLu⟩ := hcomp
  haveI hLn : L.Normal := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291.normal_of_unique hL hLu
  have hZp : IsPGroup p (center ↥L) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291.isPGroup_center hY1 hL
  have hZ : center ↥L = ⊥ := kd291_center_bot hp hp5 hGA hSp hcatY L hL hZp hY3.le
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLbot : L ≠ ⊥ := kd291_ne_bot_of_quasisimple L hq
  have hcen : centralizer (L : Set (X ⧸ primeComplementCore (G := X) p)) = ⊥ :=
    kd291_centralizer_bot L hLbot hZ hwo hp hwN
  have hsimple : IsSimpleGroup ↥L := kd291_simple_of_center_bot L hq hZ
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := kd291_nonabelian_of_quasisimple L hq
  have hLcat : IsCatalogGroup ↥L := hcatY.simple_subgroup L hsimple hnab
  refine ⟨L, hLn, hq, hZp, hZ, hsimple, hnab, hLcat, hcen, ?_⟩
  intro z hzC hzP hz5
  have hwL : w ∈ L := hwN L hLn hLbot
  have hzQ : (QuotientGroup.mk z : X ⧸ primeComplementCore (G := X) p) ∈
      (Q : Subgroup (X ⧸ primeComplementCore (G := X) p)) := by
    rw [hQ]
    exact Subgroup.mem_map_of_mem _ hzP
  have hzc : ∀ y ∈ (Q : Subgroup (X ⧸ primeComplementCore (G := X) p)),
      y * (QuotientGroup.mk z : X ⧸ primeComplementCore (G := X) p) =
        (QuotientGroup.mk z : X ⧸ primeComplementCore (G := X) p) * y := by
    intro y hy
    rw [hQ] at hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.1 hy
    have h := Subgroup.mem_centralizer_iff.1 hzC y' hy'
    change (QuotientGroup.mk y' : X ⧸ primeComplementCore (G := X) p) * QuotientGroup.mk z =
      QuotientGroup.mk z * QuotientGroup.mk y'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  have hz5' : (QuotientGroup.mk z : X ⧸ primeComplementCore (G := X) p) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hz5, QuotientGroup.mk_one]
  exact (Subgroup.zpowers_le.2 hwL) (hwu _ hzQ hzc hz5')

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
