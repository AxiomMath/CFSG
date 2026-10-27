module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenEightB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O82

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (gnV gnC gnImg)

variable {G : Type} [Group G] [Finite G]

private structure CoreSetup (M : Subgroup G) where
  K : Subgroup (threeStar M)
  R : Subgroup ↥M
  hK : CFSG.IsComponent K
  hKsimple : IsSimpleGroup K
  hKnonab : ∃ a b : K, a * b ≠ b * a
  hKnormal : K.Normal
  huniq : ∀ K' : Subgroup (threeStar M), CFSG.IsComponent K' → K' = K
  hcent : Subgroup.centralizer (K : Set (threeStar M)) = ⊥
  hRcomp : CFSG.IsPComponent 3 R
  hRmap : R.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) = K
  hLle : R.map M.subtype ≤ M
  hLsub : (R.map M.subtype).subgroupOf M = R
  hLnormal : ((R.map M.subtype).subgroupOf M).Normal
  hLbar : threeStarImg M (R.map M.subtype) = K

private structure CoreCore {M : Subgroup G} (S : CoreSetup M) where
  residual : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
    ↥(S.R.map M.subtype) = ⊤
  core_eq : (CFSG.pPrimeCore 3 ↥(S.R.map M.subtype)).map
      (S.R.map M.subtype).subtype =
    S.R.map M.subtype ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M

private structure CoreQuotient {M : Subgroup G} (S : CoreSetup M) (C : CoreCore S) where
  f : ↥(S.R.map M.subtype) →* S.K
  hfker : f.ker = CFSG.pPrimeCore 3 ↥(S.R.map M.subtype)
  hfsurj : Function.Surjective f
  hval : ∀ x : ↥(S.R.map M.subtype),
    (f x : threeStar M) = (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))
      ⟨(x : G), S.hLle x.2⟩
  hKsimple : IsSimpleGroup S.K
  simple : IsSimpleGroup (threeStar (S.R.map M.subtype))
  nonabelian : ∃ a b : threeStar (S.R.map M.subtype), a * b ≠ b * a
  img_equiv : Nonempty (↥(threeStarImg M (S.R.map M.subtype)) ≃*
    threeStar (S.R.map M.subtype))
  centralizer_img : Subgroup.centralizer
    (threeStarImg M (S.R.map M.subtype) : Set (threeStar M)) = ⊥

private noncomputable def exists_coreSetup
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h2 : CFSG.pCore 3 (threeStar M) = ⊥) : CoreSetup M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := threeStar M
  let π : ↥M →* X := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)
  let hdata := c.exists_unique_component h142 h2
  let K : Subgroup (threeStar M) := Classical.choose hdata
  have hK : CFSG.IsComponent K := (Classical.choose_spec hdata).1
  have hKn : K.Normal := (Classical.choose_spec hdata).2.1
  have huniq : ∀ K' : Subgroup (threeStar M), CFSG.IsComponent K' → K' = K :=
    (Classical.choose_spec hdata).2.2.1
  have hcent : Subgroup.centralizer (K : Set (threeStar M)) = ⊥ :=
    (Classical.choose_spec hdata).2.2.2
  have hKfacts := c.component_facts h2 hK
  let R : Subgroup ↥M :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.canonicalPrimeLift 3 K
  have hRcomp : CFSG.IsPComponent 3 R :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 3 K hK).1
  have hRmap : R.map π = K :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 3 K hK).2
  have hR_eq : R = (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
      ↥(Subgroup.comap π K)).map (Subgroup.comap π K).subtype :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.closure_pElements_eq_map_primeResidual 3 _
  haveI : (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
      ↥(Subgroup.comap π K)).Characteristic :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_characteristic 3 _
  have hRnormal : R.Normal := by
    rw [hR_eq]
    exact ConjAct.normal_of_characteristic_of_normal
  have hLle : R.map M.subtype ≤ M := Subgroup.map_subtype_le R
  have hLsub : (R.map M.subtype).subgroupOf M = R := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
  have hLnormal : ((R.map M.subtype).subgroupOf M).Normal := by
    rw [hLsub]
    exact hRnormal
  have hLbar : threeStarImg M (R.map M.subtype) = K := by
    rw [threeStarImg, hLsub, hRmap]
  exact ⟨K, R, hK, hKfacts.1, hKfacts.2.1, hKn, huniq, hcent, hRcomp, hRmap, hLle, hLsub,
    hLnormal, hLbar⟩

private noncomputable def coreCore_of_setup {M : Subgroup G} (S : CoreSetup M) : CoreCore S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRsub : S.R.IsSubnormal := S.hRcomp.choose_spec.2.1
  have hRres : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3 ↥S.R = ⊤ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent 3 S.R
      S.hRcomp
  let e : ↥S.R ≃* ↥(S.R.map M.subtype) :=
    S.R.equivMapOfInjective M.subtype M.subtype_injective
  have hLres : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual 3
      ↥(S.R.map M.subtype) = ⊤ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_top_of_equiv 3 e hRres
  let D : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  have hRcore : CFSG.pPrimeCore 3 ↥S.R = D.subgroupOf S.R :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.primeCore_subnormal_intersection
      3 S.R hRsub
  have hcore : (CFSG.pPrimeCore 3 ↥(S.R.map M.subtype)).map
      (S.R.map M.subtype).subtype =
      S.R.map M.subtype ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
    have h1 : (CFSG.pPrimeCore 3 ↥(S.R.map M.subtype)).map
        (S.R.map M.subtype).subtype =
        ((CFSG.pPrimeCore 3 ↥S.R).map S.R.subtype).map M.subtype := by
      rw [← CFSG.pPrimeCore_map_iso 3 e, Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [h1, hRcore, Subgroup.subgroupOf_map_subtype,
      Subgroup.map_inf _ _ M.subtype M.subtype_injective, inf_comm]
    rfl
  exact ⟨hLres, hcore⟩

private noncomputable def coreQuotient_of_setup {M : Subgroup G} (S : CoreSetup M)
    (C : CoreCore S) : CoreQuotient S C := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let L : Subgroup G := S.R.map M.subtype
  let π : ↥M →* threeStar M := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)
  let f : ↥L →* S.K :=
    (π.comp (Subgroup.inclusion S.hLle)).codRestrict S.K fun x => by
      have hx : π (Subgroup.inclusion S.hLle x) ∈ threeStarImg M L :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr x.2)
      rwa [S.hLbar] at hx
  have hfker : f.ker = CFSG.pPrimeCore 3 ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : π (Subgroup.inclusion S.hLle x) = 1 := congrArg Subtype.val hx
      have hxD : (x : G) ∈ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
        rw [CFSG.inSubgroup]
        exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion S.hLle x,
          (QuotientGroup.eq_one_iff _).mp hx', rfl⟩
      have hxinf : (x : G) ∈ L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := ⟨x.2, hxD⟩
      rw [← C.core_eq] at hxinf
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxinf
      have hyx' : y = x := Subtype.ext hyx
      rwa [hyx'] at hy
    · intro hx
      have hxinf : (x : G) ∈ L ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
        rw [← C.core_eq]
        exact Subgroup.mem_map_of_mem L.subtype hx
      obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hxinf.2
      have hπd : π d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
      apply Subtype.ext
      change π (Subgroup.inclusion S.hLle x) = 1
      have hincl : Subgroup.inclusion S.hLle x = d := Subtype.ext (by simpa using hdx.symm)
      rw [hincl, hπd]
  have hfsurj : Function.Surjective f := by
    intro y
    have hy : (y : threeStar M) ∈ threeStarImg M L := by rw [S.hLbar]; exact y.2
    obtain ⟨x, hx, hxval⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext ?_⟩
    exact hxval
  let eStar : threeStar L ≃* S.K :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfsurj)
  have hKsimple : IsSimpleGroup S.K := S.hKsimple
  have hLsimple : IsSimpleGroup (threeStar L) := (eStar.isSimpleGroup_congr).2 hKsimple
  have hLnonab : ∃ a b : threeStar L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := S.hKnonab
    exact ⟨eStar.symm a, eStar.symm b, fun h => hab (by simpa using congrArg eStar h)⟩
  have himg : Nonempty (↥(threeStarImg M L) ≃* threeStar L) :=
    ⟨(MulEquiv.subgroupCongr S.hLbar).trans eStar.symm⟩
  have hcentL : Subgroup.centralizer (threeStarImg M L : Set (threeStar M)) = ⊥ := by
    rw [S.hLbar]
    exact S.hcent
  exact ⟨f, hfker, hfsurj, (fun x => rfl), hKsimple, hLsimple, hLnonab, himg, hcentL⟩

private theorem core_dichotomy {M : Subgroup G} (S : CoreSetup M) (C : CoreCore S)
    (Q : CoreQuotient S C) :
    ∀ N : Subgroup G, N ≤ S.R.map M.subtype → (N.subgroupOf (S.R.map M.subtype)).Normal →
      N ≤ CFSG.inSubgroup (CFSG.pPrimeCore 3) M ∨ N = S.R.map M.subtype := by
  classical
  intro N hNL hNnormal
  let L : Subgroup G := S.R.map M.subtype
  let NbarK : Subgroup S.K := (N.subgroupOf L).map Q.f
  have hNbarKnormal : NbarK.Normal := Subgroup.Normal.map hNnormal Q.f Q.hfsurj
  rcases Q.hKsimple.eq_bot_or_eq_top_of_normal NbarK with hbot | htop
  · left
    intro x hxN
    have hxL : x ∈ L := hNL hxN
    have hxsub : (⟨x, hxL⟩ : ↥L) ∈ N.subgroupOf L := hxN
    have hfx : Q.f ⟨x, hxL⟩ = 1 := by
      have hmem : Q.f ⟨x, hxL⟩ ∈ NbarK := Subgroup.mem_map_of_mem Q.f hxsub
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hx' : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ⟨x, S.hLle hxL⟩ = 1 := by
      rw [← Q.hval ⟨x, hxL⟩]
      exact congrArg Subtype.val hfx
    rw [CFSG.inSubgroup]
    exact Subgroup.mem_map.mpr ⟨⟨x, S.hLle hxL⟩,
      (QuotientGroup.eq_one_iff _).mp hx', rfl⟩
  · right
    have hsurjN : Function.Surjective (Q.f.domRestrict (N.subgroupOf L)) := by
      intro y
      have hy : y ∈ NbarK := by rw [htop]; exact Subgroup.mem_top y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, hxy⟩
    have hfker_card : Nat.Coprime 3 (Nat.card Q.f.ker) := by
      rw [Q.hfker]
      exact CFSG.pPrimeCore_coprime_card
    have hcop :=
      CFSG.ComponentClassification.CatalogueBPrimeJoin.coprime_index_of_surjective_restriction
        3 Q.f Q.hfsurj hfker_card (N.subgroupOf L) hsurjN
    have hleRes :=
      CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index
        3 (N.subgroupOf L) hcop
    have htopN : (⊤ : Subgroup ↥L) ≤ N.subgroupOf L := by
      rw [← C.residual]
      exact hleRes
    have hLN : L ≤ N := Subgroup.subgroupOf_eq_top.mp (top_unique htopN)
    exact le_antisymm hNL hLN

private theorem core_centralizing {M : Subgroup G} (S : CoreSetup M) :
    ∀ U : Subgroup G, U ≤ M → U ≤ Subgroup.normalizer (S.R.map M.subtype : Set G) →
      ⁅U, S.R.map M.subtype⁆ ≤ CFSG.inSubgroup (CFSG.pPrimeCore 3) M →
      U ≤ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
  classical
  intro U hUM _ hcomm u hu
  let L : Subgroup G := S.R.map M.subtype
  let π : ↥M →* threeStar M := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)
  let uM : ↥M := ⟨u, hUM hu⟩
  have hcentral : π uM ∈ Subgroup.centralizer (S.K : Set (threeStar M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyL : y ∈ threeStarImg M L := by rw [S.hLbar]; exact hy
    obtain ⟨l, hl, hlval⟩ := Subgroup.mem_map.mp hyL
    let lL : ↥L := ⟨l, Subgroup.mem_subgroupOf.mp hl⟩
    have hcommD : ⁅u, (lL : G)⁆ ∈ CFSG.inSubgroup (CFSG.pPrimeCore 3) M :=
      hcomm (Subgroup.commutator_mem_commutator hu lL.2)
    have hcommM : ⁅uM, l⁆ ∈ CFSG.pPrimeCore 3 ↥M := by
      have hmap : M.subtype ⁅uM, l⁆ = ⁅u, (lL : G)⁆ := by rfl
      rw [CFSG.inSubgroup] at hcommD
      obtain ⟨d, hd, hdeq⟩ := Subgroup.mem_map.mp hcommD
      have heq : ⁅uM, l⁆ = d := Subtype.ext (hmap.trans hdeq.symm)
      rwa [heq]
    have hcommX : ⁅π uM, π l⁆ = 1 := by
      have h1 : π ⁅uM, l⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcommM
      simpa [commutatorElement_def, map_mul, map_inv] using h1
    have hc := commutatorElement_eq_one_iff_mul_comm.mp hcommX
    rw [hlval] at hc
    exact hc.symm
  have hπu_bot : π uM ∈ (⊥ : Subgroup (threeStar M)) := by
    rw [← S.hcent]
    exact hcentral
  have hπu : π uM = 1 := Subgroup.mem_bot.mp hπu_bot
  have hD : uM ∈ CFSG.pPrimeCore 3 ↥M := (QuotientGroup.eq_one_iff uM).mp hπu
  rw [CFSG.inSubgroup]
  exact Subgroup.mem_map.mpr ⟨uM, hD, rfl⟩

theorem CaseOneCtx.exists_fourteenEightCore
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h2 : CFSG.pCore 3 (threeStar M) = ⊥) :
    ∃ L : Subgroup G, FourteenEightCore M L := by
  let S := exists_coreSetup c h142 h2
  let C := coreCore_of_setup S
  let Q := coreQuotient_of_setup S C
  exact ⟨S.R.map M.subtype, ⟨S.hLle, S.hLnormal, C.residual, C.core_eq, Q.simple, Q.nonabelian,
    core_dichotomy S C Q, core_centralizing S, Q.centralizer_img, Q.img_equiv⟩⟩

private theorem pRank_pPrimeCore_le_one {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (h1 : ∀ q ∈ sigmaSet G M,
      CFSG.Open.pRank q (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ≤ 1)
    (hpM : p ∈ sigmaSet G M) :
    CFSG.Open.pRank p (⊤ : Subgroup (CFSG.pPrimeCore 3 ↥M)) ≤ 1 := by
  have hp1 : 1 < p := hp.one_lt
  let eD : ↥(CFSG.pPrimeCore 3 ↥M) ≃*
      ↥(CFSG.inSubgroup (CFSG.pPrimeCore 3) M) :=
    (CFSG.pPrimeCore 3 ↥M).equivMapOfInjective M.subtype M.subtype_injective
  calc CFSG.Open.pRank p (⊤ : Subgroup (CFSG.pPrimeCore 3 ↥M))
      = CFSG.Open.pRank p (⊤ : Subgroup ↥(CFSG.inSubgroup (CFSG.pPrimeCore 3) M)) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eD
    _ = CFSG.Open.pRank p (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
    _ ≤ 1 := h1 p hpM

private theorem two_le_pRank_quotient_of_pCore_le {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hm : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥M))
    (hD : CFSG.Open.pRank p (⊤ : Subgroup (CFSG.pPrimeCore 3 ↥M)) ≤ 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (threeStar M)) := by
  have hineq := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_top_le_add_of_normal
    (G := ↥M) hp (CFSG.pPrimeCore 3 ↥M)
  have hineq' : CFSG.Open.pRank p (⊤ : Subgroup ↥M) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (CFSG.pPrimeCore 3 ↥M)) +
        CFSG.Open.pRank p (⊤ : Subgroup (threeStar M)) := hineq
  omega

private theorem exists_pElement_not_mem_of_pRank {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {Lbar : Subgroup X}
    (hm : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    (hL : CFSG.Open.pRank p Lbar ≤ 1) :
    ∃ x : X, (∃ k : ℕ, orderOf x = p ^ k) ∧ x ∉ Lbar := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcover
  push Not at hcover
  obtain ⟨E, -, hEea, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup X)
  have hEbar : E ≤ Lbar := by
    intro x hx
    obtain ⟨k, hk⟩ := hEea.isPGroup.exists_orderOf_eq_pow ⟨x, hx⟩
    exact hcover x ⟨k, by simpa using hk⟩
  have hle := CFSG.SectionRank.le_pRank hp.one_lt hEbar hEea hEcard
  omega

private theorem stronglyPEmbedded_and_perfect_of_caseOneCtx {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) {L : Subgroup G} (hL : FourteenEightCore M L)
    {p : ℕ} (hp : p ∈ sigmaSet G M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p M ∧ commutator G = ⊤ := by
  haveI : IsSimpleGroup (threeStar L) := hL.simple
  have hqStar : CFSG.IsQuasisimple (threeStar L) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hL.nonabelian).1
  have hp_prime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp_odd : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp1 : 1 < p := hp_prime.one_lt
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : IsSimpleGroup G := c.choice.cstar.simple
  haveI : IsSimpleGroup (threeStar L) := hL.simple
  have hns : ¬ Group.IsSolvable ↥M := by
    intro hsol
    letI : Group.IsSolvable ↥M := hsol
    haveI : Group.IsSolvable ↥(L.subgroupOf M) := inferInstance
    have hLsol : Group.IsSolvable ↥L :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hL.L_le).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hL.L_le).surjective
    letI : Group.IsSolvable ↥L := hLsol
    have hStarSol : Group.IsSolvable (threeStar L) :=
      Group.isSolvable_of_surjective
        (f := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥L))
        (QuotientGroup.mk'_surjective _)
    letI : Group.IsPerfect (threeStar L) := hqStar.1
    exact Group.IsPerfect.not_isSolvable (threeStar L) hStarSol
  have hp3 : p ≠ 3 := fun h3 => c.choice.hypCGen.not_mem_sigmaSet (h3 ▸ hp)
  obtain ⟨P, hPM, hΓ⟩ :=
    exists_sylow_gamma_one_le_of_cstar c.choice.cstar c.choice.maxLocal hp hp3 hns
  have hmG : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
    (c.choice.cstar.three_le_pRank_of_mem_sigmaSet c.choice.maxLocal hp).trans
      (CFSG.SectionRank.pRank_mono hp1 le_top)
  obtain ⟨E, -, _, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup G)
  have hpG : p ∣ Nat.card G := by
    have h1 : p ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self p (by omega : CFSG.Open.pRank p (⊤ : Subgroup G) ≠ 0)
    exact h1.trans (Subgroup.card_subgroup_dvd_card E)
  have hPne : (P : Subgroup G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hpG
  have hMne : M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top c.choice.cstar.nonab M
      c.choice.maxLocal.1
  have hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M :=
    (CFSG.LocalAnalysis.RankThreeUC.gamma_one_le_iff_isStronglyPEmbedded hPM hMne hPne).mp hΓ
  have hperf : commutator G = ⊤ :=
    CFSG.LocalAnalysis.RankThreeUC.commutator_eq_top_of_standing c.choice.cstar.nonab
  exact ⟨hstrong, hperf⟩

private theorem quotient_component_data {M L : Subgroup G} {p : ℕ} (hp1 : 1 < p)
    (hL : FourteenEightCore M L)
    (hnot : ¬ 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (threeStar L))) :
    CFSG.Open.IsQuasisimple ↥(threeStarImg M L) ∧
      CFSG.Open.pRank p (threeStarImg M L) ≤ 1 := by
  haveI : IsSimpleGroup (threeStar L) := hL.simple
  have hqStar : CFSG.IsQuasisimple (threeStar L) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hL.nonabelian).1
  obtain ⟨eLbar⟩ := hL.img_equiv
  have hqLbar : CFSG.IsQuasisimple ↥(threeStarImg M L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eLbar.symm hqStar
  have hquasi : CFSG.Open.IsQuasisimple ↥(threeStarImg M L) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hqLbar)
  have hrank : CFSG.Open.pRank p (threeStarImg M L) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (threeStarImg M L),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eLbar]
    omega
  exact ⟨hquasi, hrank⟩

theorem CaseOneCtx.fourteenEight_five
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T)
    (h1 : ∀ p ∈ sigmaSet G M,
      CFSG.Open.pRank p (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ≤ 1)
    (h7145 : CFSG.LocalAnalysis.RankThreeUC.S15.K7145) {L : Subgroup G}
    (hL : FourteenEightCore M L) :
    ∀ p ∈ sigmaSet G M, 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (threeStar L)) := by
  classical
  intro p hp
  have hp_prime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp_odd : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp1 : 1 < p := hp_prime.one_lt
  haveI : Fact p.Prime := ⟨hp_prime⟩
  by_contra hnot
  let X := threeStar M
  let Lbar : Subgroup X := threeStarImg M L
  have hLbar_normal : Lbar.Normal := by
    rw [show Lbar = threeStarImg M L from rfl, threeStarImg]
    exact hL.L_normal.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨hquasi, hrankLbar⟩ := quotient_component_data hp1 hL hnot
  have hmM : 3 ≤ CFSG.Open.pRank p M :=
    c.choice.cstar.three_le_pRank_of_mem_sigmaSet c.choice.maxLocal hp
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup M] at hmM
  have hDle : CFSG.Open.pRank p (⊤ : Subgroup (CFSG.pPrimeCore 3 ↥M)) ≤ 1 :=
    pRank_pPrimeCore_le_one hp_prime h1 hp
  have hmbar : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    two_le_pRank_quotient_of_pCore_le hp_prime hmM hDle
  obtain ⟨x, hxpow, hxout⟩ := exists_pElement_not_mem_of_pRank hp_prime hmbar hrankLbar
  haveI : IsSimpleGroup G := c.choice.cstar.simple
  have hMne : M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top c.choice.cstar.nonab M
      c.choice.maxLocal.1
  have hKGroup : CFSG.Open.IsKGroup X :=
    (c.choice.cstar.kProper.isKGroup M hMne).quotient (CFSG.pPrimeCore 3 ↥M)
  have hxout' : x ∉ Lbar ⊔ Subgroup.centralizer (Lbar : Set X) := by
    rwa [hL.centralizer_img, sup_bot_eq]
  obtain ⟨N, hNnormal, hNindex⟩ :=
    h7145 X hKGroup p hp_prime hp_odd Lbar hLbar_normal hquasi hrankLbar x hxpow hxout'
  obtain ⟨hstrong, hperf⟩ :=
    stronglyPEmbedded_and_perfect_of_caseOneCtx c hL hp
  let Npre : Subgroup ↥M := N.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))
  haveI : Npre.Normal := hNnormal.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))
  have hNpre_index : Npre.index = p := by
    rw [Subgroup.index_comap_of_surjective _
      (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥M))]
    exact hNindex
  exact CFSG.LocalAnalysis.RankThreeUC.S15.no_normal_index_p_of_strong
    (G := G) hperf hp_prime hstrong Npre hNpre_index

theorem CaseOneCtx.exists_fourteenEightData
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h1 : ∀ p ∈ sigmaSet G M,
      CFSG.Open.pRank p (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ≤ 1)
    (h2 : CFSG.pCore 3 (threeStar M) = ⊥)
    (h7145 : CFSG.LocalAnalysis.RankThreeUC.S15.K7145) :
    ∃ L : Subgroup G, FourteenEightData M L := by
  obtain ⟨L, hL⟩ := c.exists_fourteenEightCore h142 h2
  exact ⟨L, ⟨hL, c.fourteenEight_five h1 h7145 hL⟩⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
