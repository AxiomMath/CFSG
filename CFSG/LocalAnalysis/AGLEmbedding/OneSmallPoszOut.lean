module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosz
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeK
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.Walter.AStar.Basic
import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

open scoped commutatorElement

private theorem pRank_le_one_of_isCyclic_subgroup {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {C : Subgroup X} (hC : IsCyclic C) : Open.pRank p C ≤ 1 :=
  CFSG.SectionRank.pRank_le_one_of_isCyclic hp hC

namespace ReducedNongeneration

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem isSolvable_inf_of_not_mem (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∉ K) (hβ : KFactBeta)
    (hKO : KFactOneLie) (hΓ : KFactOneLieBorelSolvable) :
    Group.IsSolvable (X₀.subgroupOf K) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hZ, hcycC, hfacts⟩ := h.rankOneLieAutFacts_of_not_mem hR4 hX hz hzp hK hKn hzK hβ
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have hsimple : IsSimpleGroup K := e.isSimpleGroup
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hX.isCatalogGroup_center_quotient hK)
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hAut : 3 ≤ Open.pRank p (⊤ : Subgroup (MulAut K)) := by
    have hineq := pRank_le_pRank_inf_centralizer_add_pRank_map_conjNormal hp K (R : Subgroup X)
    have h1 := pRank_le_one_of_isCyclic_subgroup hp hcycC
    have h2 := pRank_mono p hp
      (le_top : (R : Subgroup X).map (MulAut.conjNormal (H := K)) ≤ ⊤)
    omega
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hTc => by
    have := pRank_mulAut_le_two_of_kOutRankLeOne hp hZ
      (fun B hB => card_le_of_isElemAbelian_of_isCyclic_sylow T hTc hB) hfacts.1
    omega
  have hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X) := fun hc => hTnc (by
    rw [← hT] at hc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm (MulEquiv.surjective _))
  obtain ⟨hN, hKX₀⟩ := (h.center_eq_bot_and_rankOne_of_not_mem hz hzp hK hzK).2 hnc
  have hΓne := h.glbCore_ne_top_of_rankOne hN hKX₀ hT
  have hbig : ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by omega
  have hF := hKO K hsimple hnonab hcat p hp h.ne_two T hTnc hΓne hbig
  obtain ⟨hmax, -, -⟩ := hF.uPrime T hΓne
  have hΓX₀ := glbCore_map_le_of_normalizer_le hp hT hN
  have hΓsub : GLBCore p 1 (T : Subgroup K) ≤ X₀.subgroupOf K := fun k hk => hΓX₀ ⟨k, hk, rfl⟩
  have hY : X₀.subgroupOf K = GLBCore p 1 (T : Subgroup K) := by
    rcases hmax _ hΓsub with h' | h'
    · exact h'
    · exact absurd (fun x hx => (show (⟨x, hx⟩ : K) ∈ X₀.subgroupOf K from
        h' ▸ Subgroup.mem_top _)) hKX₀
  rw [hY]
  exact hΓ K hsimple hnonab hcat p hp h.ne_two T hTnc hΓne hbig

end ReducedNongeneration

section Posz

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

theorem exists_surjective_of_mem_pCorePreimage (hp : p.Prime) (hp2 : p ≠ 2) {z : G}
    (hzY : z ∈ pCorePreimage p M) (hzp : orderOf z = p) {S LB : Subgroup G}
    (hLB : IsWeakSBlock M S LB) :
    ∃ φ : (Subgroup.centralizer ({z} : Set G) ⊓ ((barM M LB).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype : Subgroup G) →* barM M LB,
      Function.Surjective φ := by
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  set πM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  obtain ⟨eM, heO, heM⟩ := hzY
  replace heM : (eM : G) = z := heM
  have hcomm : ∀ x ∈ barM M LB, x * πM eM = πM eM * x := by
    intro x hx
    have h1 := Subgroup.commutator_mem_commutator (CFSG.pCore_le_fitting _ p heO)
      (CFSG.LocalCores.component_le_layer ((CFSG.isComponent_iff_open _).mpr hLB.component) hx)
    rw [CFSG.LocalCores.fitting_layer_commute, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  set W : Subgroup G :=
    Subgroup.centralizer ({z} : Set G) ⊓ ((barM M LB).comap πM).map M.subtype
  have hWM : W ≤ M := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hφ₀ : ∀ w : W, πM (Subgroup.inclusion hWM w) ∈ barM M LB := by
    rintro ⟨w, -, m, hm, rfl⟩
    exact hm
  refine ⟨(πM.comp (Subgroup.inclusion hWM)).codRestrict _ hφ₀, ?_⟩
  have heMp : orderOf eM = p := by rw [← Subgroup.orderOf_coe, heM, hzp]
  intro x
  have hcop : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k
  obtain ⟨g, hg, hgx⟩ := exists_mem_centralizer_mk_eq hp _ hcop
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, heMp, pow_one]))
    (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x x.2))
  have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [← heM]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
  have hgL : g ∈ (barM M LB).comap πM := by
    rw [Subgroup.mem_comap, hgx]
    exact x.2
  exact ⟨⟨g, hgC, g, hgL, rfl⟩, Subtype.ext hgx⟩

end Posz

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_posz_out (hUP : KFactUPrimeSmall) (hUE : KFactUPrimeExc)
    (hKS : KFactOneSmall) (hK5 : KFactL34Local) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) (hLa : D1SmallLa p M H Rbar K)
    (hF : ¬ (p = 5 ∧ IsFi22 K)) (hV0 : d1MapPCore p M H ≠ ⊥)
    (hVK : d1MapPCore p M H ⊓ K = ⊥) {z : G} (hz : D1SmallCZElt p H R K z)
    (hout : D1CzOutside p z) : False := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h3, hVC⟩ := hd.phaseThree_and_le_of_posz hUP hUE hKS hK5 h84 hD2 hLa hF hVK
  obtain ⟨hzP, hzY, hCM⟩ := hd.posz_mem h3 h84 hD2 hV0 hVC hz
  have hzp : orderOf z = p := hz.2.1
  obtain ⟨Pbar, KC, hRC⟩ :=
    exists_d1ReducedCentralizer hd.cfg.glob hd.cfg.loc hd.cfg.ext.sylow_le hzP hzp hCM
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzpbar⟩ := hRC.center ⟨z, hzC⟩ rfl
  have := hRC.normal
  have hsolv := hRC.red.isSolvable_inf_of_not_mem hRC.four_le_pRank hRC.catalog hzZ hzpbar
    hRC.comp hRC.normal (hout KC hRC.comp) hβ hKO hΓ
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzP x hx)
  have hP4 := betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P
  have hcoreM : GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M :=
    intersecting_local_primeCore_le p hp P hd.cfg.ext.sylow_le hd.cfg.ext.weakCore_le
      ((show 3 ≤ Open.pRank p (P : Subgroup G) by omega).trans
        (PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf hPC hd.cfg.ext.sylow_le)))
  have hRP : R ≠ (P : Subgroup G) := fun hRP' => by
    have h3R := hd.pRank_R
    rw [hRP'] at h3R
    omega
  have hodd := odd_card_of_twoLocals_le hp P.isPGroup' hPC hCM (glbPrimeCore_le p _)
    (glbPrimeCore_normal p _) (glbPrimeCore_coprime p _) hcoreM
    fun T hT hT1 hPT => hd.cfg.ext.normalizer_le_of_sylow_le hRP hT hT1 hPT
  obtain ⟨LB, hLB⟩ := h3.exists_weakSBlock h84 hD2
  set W : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ ((barM M LB).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype
  obtain ⟨φ₁, hφ₁⟩ := exists_surjective_of_mem_pCorePreimage hp hp2 hzY hzp hLB
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := inf_le_left
  have hWM : W ≤ M := inf_le_right.trans (Subgroup.map_subtype_le _)
  set Q := ↥(barM M LB) ⧸ Subgroup.center ↥(barM M LB)
  have hQs : IsSimpleGroup Q := hLB.component.2.2.2
  have hQn := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
    hLB.component.2.2
  have : Group.IsPerfect ↥(barM M LB) := ⟨hLB.component.2.2.1⟩
  set φ : W →* Q := (QuotientGroup.mk' (Subgroup.center ↥(barM M LB))).comp φ₁
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hφ₁
  set D : Subgroup W := perfectCore (⊤ : Subgroup W)
  have hDperf : ⁅D, D⁆ = D := perfectCore_perfect _
  have hDφ : D.map φ = ⊤ := by
    rw [map_perfectCore, Subgroup.map_top_of_surjective φ hφ]
    exact perfectCore_eq_self_of_perfect
      (by rw [← commutator_def]; exact (Group.IsPerfect.instQuotientSubgroup).commutator_eq_top)
  set ρ : W →* D1CzQuot p z := (QuotientGroup.mk' _).comp (Subgroup.inclusion hWC)
  have hDK : D.map ρ ≤ KC := hRC.le_of_isPerfect hSch
    (Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hDperf]))
  have hDX : D.map ρ ≤ ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' _) := by
    rintro _ ⟨w, -, rfl⟩
    exact ⟨Subgroup.inclusion hWC w, ⟨(w : W).2.1, hWM (w : W).2⟩, rfl⟩
  have hDbot : D.map ρ = ⊥ := by
    by_contra hne
    have : Nontrivial (D.map ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect (D.map ρ) :=
      Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hDperf])
    have hsD : Group.IsSolvable (D.map ρ) := by
      have hle : (D.map ρ).subgroupOf KC ≤
          (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
            (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' _)).subgroupOf KC :=
        fun x hx => hDX hx
      have h1 : Group.IsSolvable (((D.map ρ).subgroupOf KC).subgroupOf
          ((((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
            (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' _)).subgroupOf KC)) :=
        inferInstance
      have h2 : Group.IsSolvable ((D.map ρ).subgroupOf KC) :=
        Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
          (MulEquiv.surjective _)
      exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hDK).toMonoidHom)
        (MulEquiv.surjective _)
    exact Group.IsPerfect.not_isSolvable (D.map ρ) hsD
  have hDker : ∀ d ∈ D, Subgroup.inclusion hWC d ∈
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p := by
    intro d hd
    have h1 : ρ d ∈ D.map ρ := Subgroup.mem_map_of_mem _ hd
    rw [hDbot, Subgroup.mem_bot] at h1
    rw [← QuotientGroup.ker_mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p),
      MonoidHom.mem_ker]
    exact h1
  let ψ : D →* primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p :=
    { toFun := fun d => ⟨Subgroup.inclusion hWC d, hDker d d.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b hab => by
    have h1 := congrArg (fun x : primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p =>
      ((x : Subgroup.centralizer ({z} : Set G)) : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hDO := Subgroup.card_dvd_of_injective ψ hψ
  have hOcard : Nat.card (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) =
      Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) := by
    rw [← glbPrimeCore_subgroupOf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (glbPrimeCore_le p _)).toEquiv
  have hQD : Nat.card Q ∣ Nat.card D := by
    have h1 := Subgroup.card_map_dvd D φ
    rw [hDφ, Subgroup.card_top] at h1
    exact h1
  have hDodd : Odd (Nat.card D) := Odd.of_dvd_nat (by rw [hOcard]; exact hodd) hDO
  exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hDodd hQD))
    (CFSG.Walter.even_card_of_isSimpleGroup hQn)

end Config

theorem stmtSmallPoszOut_of (hUP : KFactUPrimeSmall) (hUE : KFactUPrimeExc)
    (hKS : KFactOneSmall) (hK5 : KFactL34Local) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) : StmtSmallPoszOut := by
  intro G _ _ p P M H R Rbar K hd hLa hF hV0 hVK z hz hout
  exact hd.false_of_posz_out hUP hUE hKS hK5 hβ hKO hΓ hSch h84 hD2 hLa hF hV0 hVK hz hout

end CFSG.AGLEmbedding
