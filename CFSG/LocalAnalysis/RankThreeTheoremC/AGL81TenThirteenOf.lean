module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenInputs
import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveOver
import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenReduce
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

variable (G) in
theorem agl81TenThirteenAt_of (hKA : KFactThreeFourOne) (hKB : KFactThreeFourTwo)
    (h9 : AGL81NineCompetitorQ G) (hPf : AGL81TenThirteenPerfect G)
    (hS3 : AGL81TenThirteenSolvThree G) : AGL81TenThirteenAt G := by
  intro hS p P M H Q K hpσ hd L hL I₀ hI₀
  have hin := kFactInputs_of_cfg h9 hS hd
  obtain ⟨R, E, hER, hE, hEc, hcore⟩ := hin.core
  have hLM : IsSubnormal L M := hL.subnormal
  have hI₀M : I₀ ≤ H ⊓ M := le_inf_of_cZero hLM hI₀
  have hI₀H : I₀ ≤ H := hI₀M.trans inf_le_left
  rcases hI₀.shape with ha | ⟨hO2, hb⟩
  ·
    left
    refine (oUpperTwo_le_self I₀).trans ?_
    by_contra hX
    set σ : ↥I₀ →* H ⧸ primeComplementCore (G := H) p :=
      (QuotientGroup.mk' (primeComplementCore (G := H) p)).comp (Subgroup.inclusion hI₀H)
      with hσ
    have hσrange : σ.range =
        (I₀.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
      rw [hσ]
      exact CFSG.AGLEmbeddingD2.range_mk_comp_inclusion hI₀H
    have hσY : σ.range ≤ d1X0 p M H := by
      rw [hσrange]
      exact map_mk_le_d1X0 hI₀M
    have hσsub : IsSubnormal σ.range (d1X0 p M H) := by
      rw [hσrange]
      exact isSubnormal_map_mk_d1X0 (isSubnormal_inf_of_cZero hLM hI₀)
    have hσC : ¬ σ.range ≤ centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
      intro h
      apply hX
      rw [hσrange] at h
      exact (map_mk_le_centralizer_iff (K := K) hI₀H).mp h
    have hperf : commutator ↥I₀ = ⊤ :=
      ((CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq I₀).mpr
        ha.perfect).commutator_eq_top
    set ψ : ↥I₀ →* ↥(barM I₀ I₀) :=
      CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub (le_rfl : I₀ ≤ I₀) with hψ
    have hψs : Function.Surjective ψ :=
      CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub_surjective (le_rfl : I₀ ≤ I₀)
    have hψk : IsPGroup 2 ψ.ker := by
      rw [hψ, CFSG.HardMathSupport.Cooperstein.Proving.ker_barMHomSub]
      intro g
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp g.2)
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) ⟨x, hx⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have hthis := congrArg (fun y => ((y : ↥I₀) : G)) (congrArg Subtype.val hk)
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hthis ⊢
      rw [← hxg]
      exact hthis
    have hQ : CFSG.Open.IsQuasisimple ↥(barM I₀ I₀) := ha.component.2.2
    obtain ⟨iK, iJ, hpair, hK, f, hfs, hker⟩ :=
      hKB p (H ⧸ primeComplementCore (G := H) p) K (d1X0 p M H) E R ↥I₀
        ↥(barM I₀ I₀) σ ψ hin.prime hin.ne_two hin.kgroup hin.normal hin.list hin.rank
        hin.cent hin.comp hER hE hEc hcore hσY hσsub hperf hψs hψk hQ hσC
    rw [hσ, comap_centralizer_eq_subgroupOf (K := K) hI₀H] at hker
    exact hPf hS p P M H Q K hpσ hd L hL I₀ hI₀ ha hX iK iJ hpair hK ⟨f, hfs, hker⟩
  ·
    by_cases hX : CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore p H K
    · left
      exact hX
    · by_cases hp3 : p = 3
      · subst hp3
        right
        exact ⟨rfl, hS3 hS hpσ P M H Q K hd L hL I₀ hI₀ hb hX⟩
      · exfalso
        have hOH : CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ H :=
          (oUpperTwo_le_self I₀).trans hI₀H
        set J : Subgroup (H ⧸ primeComplementCore (G := H) p) :=
          ((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map
            (QuotientGroup.mk' (primeComplementCore (G := H) p)) with hJ
        have hJY : J ≤ d1X0 p M H := by
          rw [hJ]
          exact map_mk_le_d1X0 ((oUpperTwo_le_self I₀).trans hI₀M)
        have hJsub : IsSubnormal J (d1X0 p M H) := by
          rw [hJ]
          exact isSubnormal_map_mk_d1X0 (isSubnormal_oUpperTwo_inf_of_cZero hLM hI₀)
        have hcube : ∀ x ∈ J,
            x ^ 3 ∈ centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
          intro x hx
          rw [hJ] at hx
          obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
          have hy' : (y : G) ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀ :=
            Subgroup.mem_subgroupOf.mp hy
          have hpow := pow_three_mem_d1PlusCore hd hLM hI₀ hO2 hb (y : G) hy'
          unfold d1PlusCore at hpow
          obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hpow
          have hz3 : z = y ^ 3 := Subtype.ext (by
            rw [SubmonoidClass.coe_pow]
            exact hzy)
          have hmap : QuotientGroup.mk' (primeComplementCore (G := H) p) (y ^ 3) =
              QuotientGroup.mk' (primeComplementCore (G := H) p) z := by
            rw [hz3]
          rw [← map_pow, hmap]
          simpa only [Subgroup.mem_comap] using hz
        have hAK := hKA p (H ⧸ primeComplementCore (G := H) p) K (d1X0 p M H) E J R
          hin.prime hin.ne_two hp3 hin.normal hin.list hin.rank hin.cent hin.comp
          hER hE hEc hcore hJY hJsub hcube
        rw [hJ] at hAK
        exact hX ((map_mk_le_centralizer_iff (K := K) hOH).mp hAK)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
