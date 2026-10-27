module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenThreeAll
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoCentral
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoList
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenFourteenTwoA5Lift
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteenList
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem perfectA5_of_d1KBar_ne_bot
    (hKL : KFactTenFourteenTwoA5)
    (hKF : RankOneCent.KFactTenFourteenNarrowGamma) (h31 : KFactThreeOne)
    (h75 : KFactSevenFive) (hR2 : KFactNineThreeRankTwo) (hS : Setting G) {p : ℕ}
    {P : Sylow p G} {M H₁ R₁ : Subgroup G} (he : D1Escape p P M H₁ R₁) {a : G}
    (hao : orderOf a = p) {U : Subgroup G} (hUC : U ≤ centralizer ({a} : Set G))
    (hUQ : IsAGLQ p M U) (hK : d1KBar p M (centralizer ({a} : Set G)) ≠ ⊥) {I : Subgroup G}
    (hI : IsTwoPrimeComponent (centralizer ({a} : Set G) ⊓ M) I) (hpI : p ∣ Nat.card I) :
    p = 5 ∧ Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5)) := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set N := centralizer ({a} : Set G) with hN
  have ha1 : a ≠ 1 := fun h => hp.one_lt.ne' (hao ▸ h ▸ orderOf_one)
  have hCtop := RankOneCent.centralizer_ne_top_of_setting hS ha1
  set O := primeComplementCore (G := N) p with hOdef
  set π := QuotientGroup.mk' O with hπ
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  obtain ⟨R, -, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hUQ hUC
  set Rb : Sylow p (N ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hRb
  have hRbeq : (Rb : Subgroup (N ⧸ O)) = (R.subgroupOf N).map π := by
    rw [hRb, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  have haN : a ∈ N := mem_centralizer_singleton_iff.mpr rfl
  set c : N ⧸ O := π ⟨a, haN⟩ with hc
  have hcZ : c ∈ center (N ⧸ O) := by
    refine mem_center_iff.mpr fun y => ?_
    induction y using QuotientGroup.induction_on with | H n => ?_
    rw [hc, hπ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp n.2)
  have hco : orderOf c = p := by
    have hap : (⟨a, haN⟩ : N) ^ p = 1 :=
      Subtype.ext (by simpa [hao] using pow_orderOf_eq_one a)
    have hcp : c ^ p = 1 := by rw [hc, ← map_pow, hap, map_one]
    refine orderOf_eq_prime hcp fun h1 => ?_
    have hmem : (⟨a, haN⟩ : N) ∈ O := by
      rw [← QuotientGroup.ker_mk' O]
      exact h1
    have hdvd : orderOf (⟨a, haN⟩ : N) ∣ Nat.card O :=
      Subgroup.orderOf_coe (⟨⟨a, haN⟩, hmem⟩ : O) ▸ orderOf_dvd_natCard _
    rw [show orderOf (⟨a, haN⟩ : N) = p by rw [← Subgroup.orderOf_coe]; exact hao] at hdvd
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hO hdvd)
  have hKn := d1KBar_normal_of_escape he hUQ hUC hK
  have hKX : ¬ d1KBar p M N ≤ d1X0 p M N := fun hle => by
    obtain ⟨L, hL', hLX⟩ := exists_component_of_d1KBar_ne_bot hK
    exact hLX ((le_iSup₂_of_le L ⟨hL', hLX⟩ le_rfl : L ≤ d1KBar p M N).trans hle)
  have hlist := RankOneCent.tenFourteenOneGroup_of_nineThreeList
    (RankOneCent.kFactTenFourteenNarrow_of_gamma hKF) hS he hao hUC hUQ hK
    (nineThreeListGroup_d1KBar_of_escape h31 h75 hR2 hS hS.kProper he hUQ hUC hCtop hK)
    (center_d1KBar_eq_bot_of_escape h31 hS.kProper he hUQ hUC hCtop hK)
  have hCK := centralizer_d1KBar_le_d1X0_of_escape he hUQ hUC hK
  have hIle : I ≤ N ⊓ M := hI.le
  have hIN : I ≤ N := hIle.trans inf_le_left
  have hIc : commutator I = ⊤ :=
    ((CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq I).mpr
      hI.perfect).commutator_eq_top
  set ψ := CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub hIle with hψ
  have hψs : Function.Surjective ψ :=
    CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub_surjective hIle
  have hk : IsPGroup 2 ψ.ker := by
    rw [hψ, CFSG.HardMathSupport.Cooperstein.Proving.ker_barMHomSub]
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp g.2)
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) ⟨x, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun y => ((y : ↥(N ⊓ M)) : G)) (congrArg Subtype.val hk)
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [← hxg]
    exact this
  have hQ : CFSG.Open.IsQuasisimple ↥(barM (N ⊓ M) I) := hI.component.2.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hjI := joinIrreducible_of_isQuasisimple hIc ψ hψs hQ hk
  set J := (I.subgroupOf N).map π with hJ
  set σ : I →* J := (π.comp (Subgroup.inclusion hIN)).codRestrict J
    (fun x => ⟨Subgroup.inclusion hIN x, x.2, rfl⟩) with hσ
  have hσs : Function.Surjective σ := by
    rintro ⟨y, n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩
  have hJY : J ≤ d1X0 p M N := Subgroup.map_mono fun _ hx => hIle hx
  have hJsub : IsSubnormal J (d1X0 p M N) := (hI.subnormal.comap N.subtype).map π
  have hJperf : ⁅J, J⁆ = J := by
    rw [hJ, ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hIN, hI.perfect]
  have hJC : ¬ J ≤ centralizer ((d1KBar p M N : Subgroup (N ⧸ O)) : Set (N ⧸ O)) := by
    intro hJC
    have hIP : I ≤ d1PlusCore p N (d1KBar p M N) := fun x hx =>
      ⟨⟨x, hIN hx⟩, hJC ⟨⟨x, hIN hx⟩, hx, rfl⟩, rfl⟩
    have haP : a ∈ d1PlusCore p N (d1KBar p M N) :=
      RankOneCent.mem_d1PlusCore_of_central haN
        (fun y hy => (mem_centralizer_singleton_iff.mp hy).symm) _
    have h2 := two_le_pRank_of_perfect_of_commute he.ne_two hIP hI.perfect hpI haP hao
      (fun x hx => (mem_centralizer_singleton_iff.mp (hIN hx)).symm)
    have h1 := pRank_d1PlusCore_le_one_of_escape he hUQ hUC hK
    omega
  have hrank : CFSG.Open.pRank p (Rb : Subgroup (N ⧸ O)) ≤ 3 := by
    rw [hRbeq, pRank_map_mk_eq_pRank_map_subtype hp O hO, Subgroup.map_subgroupOf_eq_of_le hR.le]
    exact ((CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hRM).trans
      (local_pRank_le_evenRank p hp he.ne_two M he.maxTwoLocal_M.1)).trans hS.rank.le
  obtain ⟨hp5, f, hfs, -⟩ := hKL p (N ⧸ O) (d1KBar p M N) (d1X0 p M N) J Rb c hp he.ne_two hKn
    hlist hKX hCK hcZ hco hrank (fun A hA hAe hAc h3 => by
      rw [hRbeq] at hA h3
      exact normalizer_le_d1X0_of_escape he hR.le hRM hR.isPGroup A hA hAe hAc h3)
    hJY hJsub hJperf (joinIrreducible_map σ hσs hjI) hJC
  exact ⟨hp5, nonempty_quotient_pCore_equiv_alt5 hIc ψ hψs hk hQ (f.comp σ) (hfs.comp hσs)⟩

variable (G) in
theorem agl81TenFourteenTwoPerfectA5_of
    (hKL : KFactTenFourteenTwoA5)
    (hKF : RankOneCent.KFactTenFourteenNarrowGamma) (h74 : AGL81SevenFourTwo)
    (hOut : KFactOutCyclic) (h31 : KFactThreeOne) (h75 : KFactSevenFive)
    (hR2 : KFactNineThreeRankTwo) : AGL81TenFourteenTwoPerfectA5 G := by
  intro hS p P M H₁ R₁ he a _ hao hC hU I hI hpI
  obtain ⟨U, hUC, hUQ⟩ := hU
  by_cases hK : d1KBar p M (centralizer ({a} : Set G)) = ⊥
  · exact absurd hpI
      (not_dvd_card_of_d1KBar_eq_bot h74 hOut hS he hao hC hUC hUQ hK hI.le hI.perfect)
  · exact perfectA5_of_d1KBar_ne_bot hKL hKF h31 h75 hR2 hS he hao hUC hUQ hK hI hpI

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo
