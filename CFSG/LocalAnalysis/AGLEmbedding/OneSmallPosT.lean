module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosTAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneLiePerfect
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorus
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorusFamilies
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockClose
import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section PosT

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem coprime_card_of_perfect_of_comp (hcfg : D1ComponentConfig p P M H R Rbar)
    (hcomp : IsComponentOf K ⊤)
    (hnc : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)))
    (hz : ∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
      z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    (hI : D1SmallIa p H K) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (hUP : KFactUPrime p K) (hout : Group.IsSolvable (Outer K))
    (hs : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)))
    {U : Subgroup G} (hU : U ≤ H ⊓ M) (hUp : ⁅U, U⁆ = U) : p.Coprime (Nat.card U) := by
  have hp := hcfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set X₀ := ((H ⊓ M).subgroupOf H).map π
  have hKn : K.Normal := hcfg.red.normal_of_rankOne hcomp hnc
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
  obtain ⟨hN, hKX₀⟩ := hcfg.red.rankOne_principle hcomp hnc hzR hzK hzp hzc
  have hne := hcfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT₁
  have hΓX : (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype ≤ X₀ :=
    glbCore_map_le_of_normalizer_le hp hT₁ hN
  have hcomap : X₀.comap K.subtype = GLBCore p 1 (T₁ : Subgroup K) := by
    rcases (hUP T₁ hne).1 (X₀.comap K.subtype) (Subgroup.map_le_iff_le_comap.mp hΓX) with h | h
    · exact h
    · exact absurd (fun k hk => (Subgroup.mem_comap.mp (h.ge (Subgroup.mem_top ⟨k, hk⟩)) :)) hKX₀
  have hKX : K ⊓ X₀ = (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype := by
    rw [← hcomap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  have hKXs : Group.IsSolvable (K ⊓ X₀ : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hKX]
    exact Group.isSolvable_of_surjective (f := ((GLBCore p 1 (T₁ : Subgroup K)).equivMapOfInjective
      K.subtype K.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  set Ub := (U.subgroupOf H).map π
  have hUH : U ≤ H := hU.trans inf_le_left
  have hUb : ⁅Ub, Ub⁆ = Ub := by
    have h1 : ⁅U.subgroupOf H, U.subgroupOf H⁆ = U.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUH, hUp]
    rw [← Subgroup.map_commutator, h1]
  have hUbX : Ub ≤ X₀ := Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.mpr
    (hU (Subgroup.mem_subgroupOf.mp hu))
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  have hUbKC : Ub ≤ K ⊔ C :=
    le_sup_centralizer_of_isPerfect (Subgroup.isPerfect_iff.mpr hUb) hout
  have hCX : C ≤ X₀ := hcfg.red.centralizer_le_of_rankOne hnc hzR hzK hzp hzc
  have hCn : C.Normal := Subgroup.normal_centralizer
  set φ := QuotientGroup.mk' C
  have hφ : Ub.map φ ≤ (K ⊓ X₀).map φ := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨k, hk, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hUbKC hu)
    have hkX : k ∈ X₀ := by
      have := X₀.mul_mem (hUbX hu) (X₀.inv_mem (hCX hc))
      simpa using this
    refine ⟨k, ⟨hk, hkX⟩, ?_⟩
    have hc1 : φ c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    change φ k = φ (k * c)
    rw [map_mul, hc1, mul_one]
  have hsolφ : Group.IsSolvable ((K ⊓ X₀).map φ) :=
    Group.isSolvable_of_surjective (φ.subgroupMap_surjective (K ⊓ X₀))
  have hsolU : Group.IsSolvable (Ub.map φ) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hφ)
  have hUbφ : Ub.map φ = ⊥ := by
    by_contra hne'
    have : Nontrivial (Ub.map φ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne'
    have : Group.IsPerfect (Ub.map φ) :=
      Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hUb])
    exact Group.IsPerfect.not_isSolvable _ hsolU
  have hUbC : Ub ≤ C := by
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hUbφ
  have hUb1 : Ub = ⊥ := hcfg.red.eq_bot_of_le_centralizer_of_perfect hcomp hKX₀ hI hUbC hUb
  have hUN : U ≤ GLBPrimeCore p H := by
    intro u hu
    have h1 : π ⟨u, hUH hu⟩ ∈ Ub := ⟨⟨u, hUH hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hUb1, Subgroup.mem_bot] at h1
    exact (mk'_primeComplementCore_eq_one_iff p _).mp h1
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hUN) (glbPrimeCore_coprime p H)


open CFSG.ComponentClassification.OuterAutomorphisms in
theorem D1OneSmallData.coprime_card_of_perfect (hd : D1OneSmallData p P M H R Rbar K)
    (hI : D1SmallIa p H K) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (hUP : KFactUPrime p K) (hout : Group.IsSolvable (Outer K))
    (hs : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)))
    {U : Subgroup G} (hU : U ≤ H ⊓ M) (hUp : ⁅U, U⁆ = U) : p.Coprime (Nat.card U) :=
  coprime_card_of_perfect_of_comp hd.cfg hd.comp hd.noncyclic hd.z hI hT₁ hUP hout hs hU hUp
theorem D1OneSmallData.false_of_mem_nclIn_commutator (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hKin : KFactTwoGenInner)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hp5 : 5 ≤ p) (hd : D1OneSmallData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → p.Coprime (Nat.card U))
    {z : G} (hzR : z ∈ R) (hzN : z ∈ d1PlusCore p H K) (hzp : orderOf z = p)
    (hzJ : z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆) : False := by
  have hzS : z ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 H (hd.cfg.ext.le_H hzR)
  have hzq : z ^ p ^ 1 = 1 := by rw [pow_one, ← hzp]; exact pow_orderOf_eq_one z
  obtain ⟨L, hL, -, V, hV, hVp, hpV⟩ := h3.exists_component_of_not_mem h84 h85 h86 h93 hD2 hKin
    hKP hC3 hK5 hp5 (hd.mem_nclIn_twoCore h3 h84 hD2 hY hzJ) hzS hzq
    (hd.not_mem_pCorePreimage hWK hzR hzN hzp)
  have hLK : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ H ⊓ M := by
    rw [h3.normalizer_twoCore_H]
    exact inf_le_inf_left H hL.le
  exact (Nat.Prime.coprime_iff_not_dvd hd.cfg.red.prime).mp
    (coprime_card_of_le_barM_of_perfect inf_le_right hperf (hV.trans (barM_mono hLK)) hVp) hpV

theorem D1OneSmallData.exists_oneLieFacts (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hd : D1OneSmallData p P M H R Rbar K) (hp5 : 5 ≤ p)
    (hfam : IsSmallLinTwo p K ∨ IsSmallUnitary p K) :
    ∃ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype =
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧
      OneLieFacts p K T₁ ∧ Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)) ∧
      D1PhaseThree p P M H R := by
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  have hF := hK7 K p hd.cfg.red.prime hp5 hfam T₁
  exact ⟨T₁, hT₁, hF, hK8 K p hd.cfg.red.prime hp5 hfam T₁,
    hd.cfg.toPhaseThree_of_rankOne hd.comp hd.noncyclic hd.z hF.uPrime⟩

theorem D1OneSmallData.centralizer_d1MapPCore_le (hKU2 : KFactUnitarySylowStructure)
    (hd : D1OneSmallData p P M H R Rbar K) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (hF : OneLieFacts p K T₁)
    (hVT : d1MapPCore p M H ⊓
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ≠ ⊥)
    (hNV : K ⊓ Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      Subgroup.normalizer ((d1MapPCore p M H ⊓
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)))
    (hZ : ¬ D1SmallPosZ p M H Rbar K) :
    Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
  have : Fact p.Prime := ⟨hd.cfg.red.prime⟩
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  have hcent : Subgroup.centralizer ((d1MapPCore p M H ⊓
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rcases centralizer_le_sup_of_oneLieFacts hd.center T₁ hF (hT₁ ▸ inf_le_right) hVT
        (hT₁ ▸ hNV) with h | ⟨h1, h2⟩
    · rwa [hT₁] at h
    · refine absurd ⟨by rw [h1, hT₁], ?_⟩ hZ
      rw [← hT₁, ← map_subtype_centerOf]
      exact fun h => center_ne_of_unitary_of_kFact hKU2 hd.cfg.red.ne_two T₁ h2
        (Subgroup.map_injective K.subtype_injective h)
  exact (Subgroup.centralizer_le inf_le_left).trans hcent

theorem D1OneSmallData.false_of_posT (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hKU2 : KFactUnitarySylowStructure)
    (hd : D1OneSmallData p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K))) (hVK : d1MapPCore p M H ⊓ K ≠ ⊥)
    (hVC : d1MapPCore p M H ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥)
    (hI : D1SmallIa p H K) (hp5 : 5 ≤ p) (hfam : IsSmallLinTwo p K ∨ IsSmallUnitary p K)
    (hZ : ¬ D1SmallPosZ p M H Rbar K) : False := by
  obtain ⟨T₁, hT₁, hF, hs, h3⟩ := hd.exists_oneLieFacts hK7 hK8 hp5 hfam
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨hWp, hWR, hWn, -, hWiff⟩ := hd.d1MapPCore_facts h3 h84 hD2
  obtain ⟨hVT, hNV⟩ := hd.inf_ne_bot_and_normalizer_le h3 h84 hD2 hVK
  have hY := hWiff.mpr hVT
  have hCW := hd.centralizer_d1MapPCore_le hKU2 hT₁ hF hVT hNV hZ
  have hWK : d1MapPCore p M H ≤ K := (le_of_inf_centralizer_eq_bot hd.cfg.red.prime hd.center
    T₁ hT₁ hF hWp (le_sup_of_oneLieFacts hd.center T₁ hT₁ hF hWp hWR hWn) hWn hVC).trans
      inf_le_right
  obtain ⟨z, hzR, hzp, hzH, hzc⟩ := hd.exists_czElt
  have hzN : z ∈ d1PlusCore p H K := ⟨⟨z, hzH⟩, hzc, rfl⟩
  exact hd.false_of_mem_nclIn_commutator h3 h84 h85 h86 h93 hD2 hKin hKP hC3 hK5 hp5 hY hWK
    (fun U hU hUp => hd.coprime_card_of_perfect hI hT₁ hF.uPrime hF.outer_solvable hs hU hUp)
    hzR hzN hzp (hd.mem_nclIn_commutator h3 h84 hCGT hD2 huniq hY hCW hzR hzN hzp)

end PosT

theorem stmtSmallPosT_of (hK7 : KFactOneLieSmallLie) (hK8 : KFactSmallBorelSolvable)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hCGT : AschbacherLocalCGTBlock) (hKU2 : KFactUnitarySylowStructure) : StmtSmallPosT := by
  intro G _ _ p P M H R Rbar K hd huniq _ hVK hVC hI hp5 hfam hZ
  exact hd.false_of_posT hK7 hK8 hKin hKP hC3 hK5 h84 h85 h86 h93 hD2 hCGT hKU2 huniq hVK hVC
    hI hp5 hfam hZ

end CFSG.AGLEmbedding
