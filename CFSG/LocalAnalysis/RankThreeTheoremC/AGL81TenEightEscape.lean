module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenInputs
import CFSG.Fischer.Classification.Recognition.Basic
import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.ComponentsK
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectCoprimeLifts
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem kFactInputs_of_escape (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR2 : KFactNineThreeRankTwo) (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {B N : Subgroup G}
    (hB : IsAGLQ p M B) (hBN : B ≤ N) (hNtop : N ≠ ⊤) (hK : d1KBar p M N ≠ ⊥) :
    TenThirteen.KFactInputs p M N (d1KBar p M N) := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := N) p with hOdef
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  have hkg : CFSG.Open.IsKGroup (N ⧸ O) := (hS.kProper.isKGroup N hNtop).quotient O
  have hlist := nineThreeListGroup_d1KBar_of_escape h31 h75 hR2 hS hS.kProper he hB hBN hNtop hK
  have hnormal := d1KBar_normal_of_escape he hB hBN hK
  have hrank : pRank p (centralizer (d1KBar p M N : Set (N ⧸ O))) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    have e1 : CFSG.Open.pRank p (d1PlusCore p N (d1KBar p M N)) =
        CFSG.Open.pRank p (centralizer (d1KBar p M N : Set (N ⧸ O))) := by
      unfold d1PlusCore
      rw [← pRank_map_mk_eq_pRank_map_subtype hp O hO,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)]
    rw [← e1]
    exact pRank_d1PlusCore_le_one_of_escape he hB hBN hK
  have hcent := centralizer_d1KBar_le_d1X0_of_escape he hB hBN hK
  have hcomp : ∀ L : Subgroup (N ⧸ O), IsComponentOf L ⊤ → L ≤ d1KBar p M N →
      ¬ L ≤ d1X0 p M N := by
    intro L hL hLK hLX
    have hKL : d1KBar p M N ≤ Subgroup.centralizer (L : Set (N ⧸ O)) := by
      refine iSup₂_le fun L' hL' => ?_
      by_cases hEq : L' = L
      · exact absurd (hEq ▸ hLX) hL'.2
      · intro x hx
        exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (commute_of_isComponentOf_ne hL'.1 hL hEq x hx y hy).symm
    have hcentL : L ≤ Subgroup.centralizer (L : Set (N ⧸ O)) := hLK.trans hKL
    exact CFSG.Fischer.Classification.Recognition.IsQuasisimple.not_le_of_comm hL.2.2
      (A := L) (fun x hx y hy =>
        (Subgroup.mem_centralizer_iff.mp (hcentL hx) y hy).symm) le_rfl
  obtain ⟨R, hBR, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hB hBN
  set Rb : Sylow p (N ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (N ⧸ O)) = (R.subgroupOf N).map π := by
    rw [hRb, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  obtain ⟨E, hER, hEab, hEcard, hcore⟩ := cores_le_d1X0 he hB hBR hRM hR
  refine ⟨hp, he.ne_two, hkg, hnormal, hlist, hrank, hcent, hcomp, Rb, E, ?_, hEab, hEcard, ?_⟩
  · rw [hRbeq]
    exact hER
  · rw [hRbeq, CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hcore

theorem le_d1PlusCore_or_pair (hK342 : TenThirteen.KFactThreeFourTwo) {p : ℕ}
    {M N J : Subgroup G} (hin : TenThirteen.KFactInputs p M N (d1KBar p M N))
    (hJ : IsTwoPrimeComponent M J) (hJN : J ≤ N) :
    J ≤ d1PlusCore p N (d1KBar p M N) ∨
      ∃ iK iJ : TauCeti.CFSGIndex, TenThirteen.IsThreeFourPair p iK iJ ∧
        ∃ f : ↥J →* iJ.Group, Function.Surjective f := by
  set O := primeComplementCore (G := N) p with hOdef
  set π := QuotientGroup.mk' O with hπ
  set K := d1KBar p M N with hKdef
  let σ : ↥J →* N ⧸ O := π.comp (Subgroup.inclusion hJN)
  have hrange : σ.range = (J.subgroupOf N).map π := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range hJN]
  by_cases hc : σ.range ≤ Subgroup.centralizer (K : Set (N ⧸ O))
  · left
    intro x hx
    exact ⟨⟨x, hJN hx⟩, hc ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  right
  have hψker : IsPGroup 2 (CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub hJ.le).ker := by
    rw [CFSG.HardMathSupport.Cooperstein.Proving.ker_barMHomSub hJ.le]
    exact (pCoreOf_isPGroup 2 M).comap_of_injective J.subtype J.subtype_injective
  have hJperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ.perfect
  have hσX : σ.range ≤ d1X0 p M N := by
    rw [hrange]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr ⟨x.2, hJ.le (Subgroup.mem_subgroupOf.mp hx)⟩
  have hσsub : IsSubnormal σ.range (d1X0 p M N) := by
    have hsubN : IsSubnormal J (N ⊓ M) := CFSG.AGLEmbeddingD2.isSubnormal_of_le_of_isSubnormal
      hJ.subnormal (le_inf hJN hJ.le) inf_le_right
    have h2 := cfsg_isSubnormal_map π (cfsg_isSubnormal_comap N.subtype hsubN)
    rw [hrange]
    exact h2
  obtain ⟨R, E, hER, hEab, hEcard, hcore⟩ := hin.core
  obtain ⟨iK, iJ, hpair, -, f, hf, -⟩ := hK342 p (N ⧸ O) K (d1X0 p M N) E R ↥J ↥(barM M J) σ
    (CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub hJ.le)
    hin.prime hin.ne_two hin.kgroup hin.normal hin.list hin.rank hin.cent hin.comp hER hEab hEcard
    hcore hσX hσsub (Group.isPerfect_def.mp hJperf)
    (CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub_surjective hJ.le) hψker
    hJ.component.2.2 hc
  exact ⟨iK, iJ, hpair, f, hf⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
