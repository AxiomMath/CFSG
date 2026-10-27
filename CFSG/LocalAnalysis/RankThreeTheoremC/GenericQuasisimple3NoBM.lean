module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericQuasisimple3
public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.RankThreeTheoremC.OddCentralPsl3
import CFSG.LocalAnalysis.RankThreeTheoremC.CentralOfRankLeThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open scoped MatrixGroups commutatorElement
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem notSecExcl3_of_noExcludedSection3 {G : Type} [Group G] (hno : NoExcludedSection3 G)
    {H : Subgroup G} {N : Subgroup H} [N.Normal] {L : Subgroup (H ⧸ N)}
    (hq : CFSG.Open.IsQuasisimple L) (hZ : center L = ⊥) : NotSecExcl3 ↥L :=
  notSecExcl3_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    (hno H N L hq)

theorem notBM_of_notSecExcl3 {K : Type} [Group K] (h : NotSecExcl3 K) : NotBM K :=
  ⟨h .B (by simp [sectionExcludedNames3]), h .M (by simp [sectionExcludedNames3])⟩

namespace GenericShadow

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {S : Sylow p Y} {z : Y} {Γ : Subgroup Y}

theorem isRankTwoSEGroup_of_not_isCyclic_noBM (h : GenericShadow p S z Γ)
    (hK4 : KF1On Y) (hK1 : StronglyEmbeddedRankTwoKFactNoBM) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hBM : NotBM ↥L)
    (hnc : ¬ IsCyclic ↥((S : Subgroup Y) ⊓ L)) : IsRankTwoSEGroup p ↥L := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hsimple, hnonab, hcat⟩ := h.simple_nonab_catalog hK4 hL
  obtain ⟨T, hT⟩ := h.exists_sylow_map_eq_inf hL
  have hrank : CFSG.Open.pRank p (T : Subgroup L) = 2 := by
    have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp L.subtype
      L.subtype_injective (T : Subgroup L)
    rw [hT] at hmap
    have hle := h.pRank_inf_le_two hK4 hL
    have hge : 2 ≤ CFSG.Open.pRank p ((S : Subgroup Y) ⊓ L) :=
      two_le_pRank_of_not_isCyclic hp h.ne_two (S.isPGroup'.to_inf_left) hnc
    omega
  exact hK1 L hsimple hnonab hcat hBM p hp h.ne_two T hrank
    (h.rankThreeGamma_ne_top hK4 hL T hT)

theorem exists_main_noBM (h : GenericShadow p S z Γ) (hK4 : KF1On Y)
    (hK1 : StronglyEmbeddedRankTwoKFactNoBM) (hK2 : StronglyEmbeddedCyclicOuterKFact)
    (hK3 : KFactOutCyclic) (hBM : ∀ L : Subgroup Y, IsComponentOf L ⊤ → NotBM ↥L) :
    ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ L.Normal ∧ (∀ L', IsComponentOf L' ⊤ → L' = L) ∧
      center L = ⊥ ∧ ¬ L ≤ Γ ∧ (IsRankTwoSEGroup p ↥L ∨ (p = 5 ∧ IsoLie ↥L (.suzuki 2))) := by
  obtain ⟨L, hL⟩ := h.exists_isComponentOf
  refine ⟨L, hL, h.normal_of_isComponentOf hL, fun L' hL' => h.eq_of_isComponentOf hL' hL,
    h.center_eq_bot hK4 hL, h.not_le_of_isComponentOf hL, ?_⟩
  by_cases hc : IsCyclic ↥((S : Subgroup Y) ⊓ L)
  · exact Or.inr (h.isoLie_suzuki_of_isCyclic hK4 hK2 hK3 hL hc)
  · exact Or.inl (h.isRankTwoSEGroup_of_not_isCyclic_noBM hK4 hK1 hL (hBM L hL) hc)

end GenericShadow

theorem gl83GenericLayer_of_inputs_redNoBM {G : Type} [Group G] [Finite G] (hS : Setting G)
    (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KF1At G)
    (R3 : GL83GenericPrimeThree G) (R2 : GL83GenericListExclusionRed G)
    (hno : NoExcludedSection3 G) : GL83GenericLayer G := by
  intro p hp P M hM hfail hIH x hgen
  have hp3 : p ≠ 3 := R3 p hp P M hM hfail hIH x hgen
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hp5 : 5 ≤ p := by
    have h2 := hprime.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hprime (by decide)
    omega
  refine ⟨hp5, ?_⟩
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨S, hSmap, hsh⟩ := exists_genericShadow hS hU0 hp hp5 hM hgen
  have hCtop : centralizer ({x} : Set G) ≠ ⊤ := fun htop => hS.normalizer_zpowers_ne_top
    hgen.2.1.2.1 (eq_top_iff.2 (htop ▸ centralizer_singleton_le_normalizer_zpowers x))
  have hK4 : KF1On (centralizer ({x} : Set G) ⧸
      primeComplementCore (G := centralizer ({x} : Set G)) p) :=
    fun q hq hq5 L hL hcat hpg hdvd => K4 q hq hq5 _ hCtop _ L hL hcat hpg hdvd
  have hBM : ∀ L : Subgroup (GenericReduced p x), IsComponentOf L ⊤ → NotBM ↥L :=
    fun L hL => notBM_of_notSecExcl3
      (notSecExcl3_of_noExcludedSection3 hno hL.2.2 (hsh.center_eq_bot hK4 hL))
  obtain ⟨Lb, hLbc, hLbn, huniq, hLbZ, hLbΓ, hLblist⟩ :=
    hsh.exists_main_noBM hK4 K1 K2 K3 hBM
  obtain ⟨hxP, ⟨hxM, hx1, hxp, hx3, hCM⟩, hsyl, hrk⟩ := hgen
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  have : Lb.Normal := hLbn
  have hLbperf : ⁅Lb, Lb⁆ = Lb := Subgroup.isPerfect_iff.mp ⟨hLbc.2.2.1⟩
  obtain ⟨hLsimple, -, -⟩ := hsh.simple_nonab_catalog hK4 hLbc
  have hLb_ne : Lb ≠ ⊥ := by
    intro h
    have := hLsimple.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot Lb).mp this h
  set J : Subgroup C := perfectCore (Lb.comap π) with hJ
  have hJn : J.Normal := normal_perfectCore _
  have hJperf : ⁅J, J⁆ = J := commutator_perfectCore _
  have hJmap : J.map π = Lb :=
    map_perfectCore_comap π (QuotientGroup.mk'_surjective O) Lb hLbperf
  set JG : Subgroup G := J.map C.subtype with hJG
  have hJGC : JG ≤ C := Subgroup.map_subtype_le J
  have hCJG : C ≤ normalizer (JG : Set G) := le_normalizer_map_subtype J
  have hJGperf : ⁅JG, JG⁆ = JG := commutator_map_subtype J hJperf
  have hsimple : IsSimpleGroup ↥(J.map π) := by rw [hJmap]; exact hLsimple
  have hnot : ¬ JG ≤ M := by
    intro hle
    apply hLbΓ
    have hJ' : J ≤ (C ⊓ M).subgroupOf C := fun j hj =>
      Subgroup.mem_subgroupOf.mpr ⟨j.2, hle ⟨j, hj, rfl⟩⟩
    rw [← hJmap]
    exact Subgroup.map_mono hJ'
  have hlt : rankThreePrimeCore p JG < JG :=
    rankThreePrimeCore_map_subtype_lt J (by rw [hJmap]; exact hLb_ne)
  obtain ⟨ψ, hψ, hψker⟩ := exists_surjective_ker_primeCore (p := p) (C := C) J
  have hlist : IsRankTwoSEGroup p ↥(J.map π) ∨ (p = 5 ∧ IsoLie ↥(J.map π) (.suzuki 2)) := by
    rcases hLblist with h | ⟨h5, h⟩
    · exact Or.inl (IsRankTwoSEGroup.of_mulEquiv (MulEquiv.subgroupCongr hJmap).symm h)
    · exact Or.inr ⟨h5, isoLie_of_mulEquiv (MulEquiv.subgroupCongr hJmap).symm h⟩
  have hFi22 : ¬ Nonempty (↥(J.map π) ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) := by
    rintro ⟨f⟩
    exact notSecExcl3_of_noExcludedSection3 hno hLbc.2.2 hLbZ .Fi22
      (by simp [sectionExcludedNames3]) ⟨(MulEquiv.subgroupCongr hJmap).symm.trans f⟩
  obtain ⟨hfact, ⟨ePSL0⟩⟩ := R2 p hp P M hM hfail hIH x
    ⟨hxP, ⟨hxM, hx1, hxp, hx3, hCM⟩, hsyl, hrk⟩ hp5 JG hJGC hCJG
    (Subgroup.isPerfect_iff.mpr hJGperf) hlt
    (fun N hN hn hON => eq_or_eq_of_normal J hsimple N hN hn hON) hnot (↥(J.map π)) ψ hψ hψker
    hlist hFi22
  obtain ⟨hOJ, hJO, hOcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p JG
  have hOM : rankThreePrimeCore p JG ≤ M := by
    have h1 : GLBPrimeCore p C ≤ M :=
      (glbPrimeCore_le_pPrimeCoreIn p C).trans (pPrimeCoreIn_centralizer_le hS hp hM hrk.ge)
    have h2 : GLBPrimeCore p C = O.map C.subtype := glbPrimeCore_eq_primeComplementCoreOf p C
    rw [rankThreePrimeCore_map_subtype]
    exact (Subgroup.map_mono inf_le_right).trans (h2 ▸ h1)
  have hOdd : Odd (Nat.card O) := by
    have h1 : ¬ 2 ∣ Nat.card (CFSG.ABGTheoremB.pPrimeCoreIn p C) :=
      odd_card_pPrimeCoreIn_of_not_le hS hD1 hp hM hrk.ge hCM
    have h2 : O.map C.subtype ≤ CFSG.ABGTheoremB.pPrimeCoreIn p C := by
      have := glbPrimeCore_le_pPrimeCoreIn p C
      rwa [glbPrimeCore_eq_primeComplementCoreOf] at this
    have hdvd : Nat.card O ∣ Nat.card (CFSG.ABGTheoremB.pPrimeCoreIn p C) := by
      have hcardO : Nat.card (O.map C.subtype) = Nat.card O :=
        Subgroup.card_map_of_injective C.subtype_injective
      exact hcardO ▸ Subgroup.card_dvd_of_le h2
    exact Odd.of_dvd_nat (Nat.odd_iff.mpr (by omega)) hdvd
  have hOJodd : Odd (Nat.card (rankThreePrimeCore p JG)) := by
    have hdvd : Nat.card (rankThreePrimeCore p JG) ∣ Nat.card O := by
      rw [rankThreePrimeCore_map_subtype]
      calc Nat.card ((J ⊓ O).map C.subtype) ∣ Nat.card (O.map C.subtype) :=
            Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_right)
        _ = Nat.card O := Subgroup.card_map_of_injective C.subtype_injective
    exact hOdd.of_dvd_nat hdvd
  have hrank : ∀ q : ℕ, q.Prime → ∀ E : Subgroup G, E ≤ rankThreePrimeCore p JG →
      IsElemAbelian q E → Nat.card E ≤ q ^ 3 := by
    intro q hq E hEO hE
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨k, hk⟩ := (elementary_isPGroup q E hE).exists_card_eq
    by_cases hq2 : q = 2
    · subst hq2
      have hEodd : Odd (Nat.card E) := hOJodd.of_dvd_nat (Subgroup.card_dvd_of_le hEO)
      have hk0 : k = 0 := by
        by_contra hk0
        rw [hk] at hEodd
        exact (Nat.not_even_iff_odd.mpr hEodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
      rw [hk, hk0]
      norm_num
    · have hkM := le_pRank_of_elemAbelian_card (hEO.trans hOM) hE hk
      have hloc := local_pRank_le_evenRank q hq hq2 M hM.1.1
      have hk3 : k ≤ 3 := by
        have := hS.rank
        omega
      rw [hk]
      exact Nat.pow_le_pow_right hq.pos hk3
  have hcent : ⁅JG, rankThreePrimeCore p JG⁆ = ⊥ :=
    central_of_rank_le_three_psl G p hp5 JG (rankThreePrimeCore p JG) hOJ hOJodd
      ((Nat.Prime.coprime_iff_not_dvd hprime).1 hOcop) hJGperf (↥(J.map π)) ψ hψ hψker
      ⟨ePSL0⟩ hrank
  have hO0 : rankThreePrimeCore p JG = ⊥ :=
    eq_bot_of_central_odd_subgroup_psl hp5 hOJ hcent hOJodd
      ((Nat.Prime.coprime_iff_not_dvd hprime).1 hOcop) hJGperf ψ hψker ePSL0
  have hRQ : rankThreePrimeCore p JG ≤ centralizer (JG : Set G) := by
    rw [hO0]
    exact bot_le
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_center J (by rw [hJmap]; exact hLbZ) hRQ
  let e' : ↥JG ⧸ center ↥JG ≃* ↥Lb := e.trans (MulEquiv.subgroupCongr hJmap)
  have : IsSimpleGroup ↥Lb := hLsimple
  have hquasi : CFSG.Open.IsQuasisimple ↥JG :=
    ⟨(Group.isPerfect_def).mp (Subgroup.isPerfect_iff.mpr hJGperf), e'.isSimpleGroup⟩
  have hcomp : IsComponentOf JG C :=
    ⟨hJGC, IsSubnormal.step hJGC (normal_subgroupOf_map_subtype J) (IsSubnormal.refl C), hquasi⟩
  have hlayer : rankThreeLayer C = JG := by
    apply le_antisymm
    · exact sSup_le fun K hK => le_map_perfectCore_of_isComponentOf hOdd Lb huniq hK
    · exact le_sSup hcomp
  have hker0 : ψ.ker = ⊥ := by rw [hψker, hO0, Subgroup.bot_subgroupOf]
  let eJ : ↥JG ≃* ↥(J.map π) :=
    MulEquiv.ofBijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).mp hker0, hψ⟩
  exact ⟨hfact, 2, le_rfl, ⟨(MulEquiv.subgroupCongr hlayer).trans (eJ.trans ePSL0)⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
