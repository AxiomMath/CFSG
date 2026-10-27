module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111SizeMax
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeListOf
import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

structure KFactInputs (p : ℕ) (M H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  kgroup : CFSG.Open.IsKGroup (H ⧸ primeComplementCore (G := H) p)
  normal : K.Normal
  list : NineThreeListGroup p K
  rank : pRank p (centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) ≤ 1
  cent : centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≤ d1X0 p M H
  comp : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L ≤ K →
    ¬ L ≤ d1X0 p M H
  core : ∃ (R : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (E : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    E ≤ R ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      (if 3 ≤ pRank p (R : Subgroup (H ⧸ primeComplementCore (G := H) p))
        then GLBWeakCore p (R : Subgroup (H ⧸ primeComplementCore (G := H) p))
        else GLBCore p 1 E) ≤ d1X0 p M H

theorem kFactInputs_of_cfg (h9 : AGL81NineCompetitorQ G) (hS : Setting G) {p : ℕ}
    {P : Sylow p G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) : KFactInputs p M H K := by
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hk := hd.kbar
  subst hk
  set O := primeComplementCore (G := H) p with hOdef
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hne : d1KBar p M H ≠ ⊥ :=
    fun h => hd.not_le_X0 (by rw [h]; exact bot_le)
  have hkg : CFSG.Open.IsKGroup (H ⧸ O) := by
    haveI : IsSimpleGroup G := hS.simple
    exact (hS.kProper.isKGroup H (twoLocal_ne_top hS.nonab H hd.maxH.1)).quotient O
  have hlist := TenNineOneThree.nineThreeListGroup_of_cfg h9 hS hd
  have hnormal := d1KBar_normal_of_escape he hd.base hd.le_H hne
  have hrank : pRank p (centralizer (d1KBar p M H : Set (H ⧸ O))) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    have e1 : CFSG.Open.pRank p (d1PlusCore p H (d1KBar p M H)) =
        CFSG.Open.pRank p (centralizer (d1KBar p M H : Set (H ⧸ O))) := by
      unfold d1PlusCore
      rw [← pRank_map_mk_eq_pRank_map_subtype hp O hO,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)]
    rw [← e1]
    exact pRank_d1PlusCore_le_one_of_escape he hd.base hd.le_H hne
  have hcent := centralizer_d1KBar_le_d1X0_of_escape he hd.base hd.le_H hne
  have hcomp : ∀ L : Subgroup (H ⧸ O), IsComponentOf L ⊤ → L ≤ d1KBar p M H →
      ¬ L ≤ d1X0 p M H := by
    intro L hL hLK hLX
    have hKL : d1KBar p M H ≤ Subgroup.centralizer (L : Set (H ⧸ O)) := by
      refine iSup₂_le fun L' hL' => ?_
      by_cases hEq : L' = L
      · exact absurd (hEq ▸ hLX) hL'.2
      · intro x hx
        exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (commute_of_isComponentOf_ne hL'.1 hL hEq x hx y hy).symm
    have hcentL : L ≤ Subgroup.centralizer (L : Set (H ⧸ O)) := hLK.trans hKL
    exact CFSG.Fischer.Classification.Recognition.IsQuasisimple.not_le_of_comm hL.2.2
      (A := L) (fun x hx y hy =>
        (Subgroup.mem_centralizer_iff.mp (hcentL hx) y hy).symm) le_rfl
  obtain ⟨R, hBR, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hd.base hd.le_H
  set Rb : Sylow p (H ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (H ⧸ O)) = (R.subgroupOf H).map π := by
    rw [hRb, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  obtain ⟨E, hER, hEab, hEcard, hcore⟩ := cores_le_d1X0 he hd.base hBR hRM hR
  refine ⟨hp, he.ne_two, hkg, hnormal, hlist, hrank, hcent, hcomp, Rb, E, ?_, hEab, hEcard, ?_⟩
  · rw [hRbeq]
    exact hER
  · rw [hRbeq, CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hcore

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
