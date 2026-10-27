module

public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoTheoremZ
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneLiePerfect
import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockClose
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

private theorem eq_bot_of_commutator_eq_of_isSolvable {Y : Type*} [Group Y] {J : Subgroup Y}
    (hJ : ⁅J, J⁆ = J) (hs : Group.IsSolvable J) : J = ⊥ := by
  have : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJ
  obtain ⟨n, hn⟩ := hs.solvable
  rw [Group.IsPerfect.derivedSeries_eq_top] at hn
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : J) ∈ (⊤ : Subgroup J) := Subgroup.mem_top _
  rw [hn, Subgroup.mem_bot] at h1
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.coprime_card_of_perfect (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier) (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₁ : IsComponentOf L₁ ⊤)
    (huL : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁)
    {U : Subgroup G} (hU : U ≤ H ⊓ M) (hUp : ⁅U, U⁆ = U) : p.Coprime (Nat.card U) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set X₀ := ((H ⊓ M).subgroupOf H).map π
  set C := Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) p))
  have hL₁X₀ : ¬ L₁ ≤ X₀ := by
    obtain ⟨L, hL, hLX₀⟩ := hd.exists_not_le hAut
    rwa [huL L hL] at hLX₀
  have hiso := hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
      hd.cfg.catalog) hS hd.cyclic hd.rank hL₁
    hL₁X₀
  have hL₁n : L₁.Normal := ⟨fun n hn g => huL _
    ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L₁).mpr hL₁) ▸
      (⟨n, hn, rfl⟩ : g * n * g⁻¹ ∈ L₁.map (MulAut.conj g).toMonoidHom)⟩
  obtain ⟨hsimple, hnonab, hcat, -⟩ :=
    hd.cfg.red.isSimpleGroup_of_isCyclic hd.cfg.catalog hL₁ (hd.cyclic L₁ hL₁)
  obtain ⟨hUP, -, hloc⟩ := hKL p L₁ hiso
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL₁.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨t, ht, htp, -⟩ :=
    exists_mem_sylow_inf_component hp hd.cfg.red.ne_two hd.cfg.red.core_eq_bot Rbar hL₁
  have hN : ∀ V : Subgroup (H ⧸ primeComplementCore (G := H) p),
      V ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁ → V ≠ ⊥ →
        L₁ ⊓ Subgroup.normalizer (V : Set (H ⧸ primeComplementCore (G := H) p)) ≤ X₀ :=
    fun V hV hV1 => (inf_le_inf_left L₁ (normalizer_le_normalizer_of_isCyclic hp
      (hd.cyclic L₁ hL₁) (Rbar.isPGroup'.to_le inf_le_left) (Subgroup.zpowers_le.mpr ht)
      (by rw [Nat.card_zpowers, htp]) hV hV1)).trans
      (hd.cfg.red.inf_normalizer_zpowers_le_of_aut (hAut _ _ _ _ hd.cfg.red hd.cfg.catalog)
          hd.cyclic hd.rank hL₁ ht htp)
  have hΓX : (GLBCore p 1 (T : Subgroup L₁)).map L₁.subtype ≤ X₀ :=
    glbCore_map_le_of_normalizer_le hp hT hN
  have hne : GLBCore p 1 (T : Subgroup L₁) ≠ ⊤ := fun htop =>
    hL₁X₀ fun x hx => hΓX ⟨⟨x, hx⟩, htop ▸ Subgroup.mem_top _, rfl⟩
  have hcomap : X₀.comap L₁.subtype = GLBCore p 1 (T : Subgroup L₁) := by
    rcases (hUP T hne).1 (X₀.comap L₁.subtype) (Subgroup.map_le_iff_le_comap.mp hΓX) with h | h
    · exact h
    · exact absurd (fun k hk => (Subgroup.mem_comap.mp (h.ge (Subgroup.mem_top ⟨k, hk⟩)) :))
        hL₁X₀
  have hKX : L₁ ⊓ X₀ = (GLBCore p 1 (T : Subgroup L₁)).map L₁.subtype := by
    rw [← hcomap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  have hKXs : Group.IsSolvable (L₁ ⊓ X₀ : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hKX]
    have := (hloc T).2.2
    exact Group.isSolvable_of_surjective (f := ((GLBCore p 1 (T : Subgroup L₁)).equivMapOfInjective
      L₁.subtype L₁.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  obtain ⟨zb, hzbO, hzbp, -⟩ := exists_mem_centralizer_orderOf_eq CFSG.pCore_isPGroup
    (hd.cfg.red.pCore_ne_bot_of_unique_of_aut (hAut _ _ _ _ hd.cfg.red hd.cfg.catalog) hd.cyclic
        hd.rank hL₁ huL)
  have hCX : C ≤ X₀ := hd.cfg.red.centralizer_le_of_pCore hL₁ (hd.cyclic L₁ hL₁) hzbO hzbp
  set Ub := (U.subgroupOf H).map π
  have hUH : U ≤ H := hU.trans inf_le_left
  have hUb : ⁅Ub, Ub⁆ = Ub := by
    have h1 : ⁅U.subgroupOf H, U.subgroupOf H⁆ = U.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUH, hUp]
    rw [← Subgroup.map_commutator, h1]
  have hUbX : Ub ≤ X₀ := Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.mpr
    (hU (Subgroup.mem_subgroupOf.mp hu))
  have hUbKC : Ub ≤ L₁ ⊔ C :=
    le_sup_centralizer_of_isPerfect (Subgroup.isPerfect_iff.mpr hUb) (hSch L₁ hsimple hnonab hcat)
  have hCn : C.Normal := Subgroup.normal_centralizer
  set φ := QuotientGroup.mk' C
  have hφ : Ub.map φ ≤ (L₁ ⊓ X₀).map φ := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨k, hk, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hUbKC hu)
    have hkX : k ∈ X₀ := by
      have := X₀.mul_mem (hUbX hu) (X₀.inv_mem (hCX hc))
      simpa using this
    refine ⟨k, ⟨hk, hkX⟩, ?_⟩
    have hc1 : φ c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    change φ k = φ (k * c)
    rw [map_mul, hc1, mul_one]
  have hsolU : Group.IsSolvable (Ub.map φ) :=
    have : Group.IsSolvable ((L₁ ⊓ X₀).map φ) :=
      Group.isSolvable_of_surjective (φ.subgroupMap_surjective (L₁ ⊓ X₀))
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hφ)
  have hUbφ : Ub.map φ = ⊥ := eq_bot_of_commutator_eq_of_isSolvable
    (by rw [← Subgroup.map_commutator, hUb]) hsolU
  have hUbC : Ub ≤ C := by
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hUbφ
  have hUb1 : Ub = ⊥ := hd.cfg.red.eq_bot_of_le_centralizer_of_perfect hL₁ hL₁X₀ huL hUbC hUb
  have hUN : U ≤ GLBPrimeCore p H := by
    intro u hu
    have h1 : π ⟨u, hUH hu⟩ ∈ Ub := ⟨⟨u, hUH hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [hUb1, Subgroup.mem_bot] at h1
    exact (mk'_primeComplementCore_eq_one_iff p _).mp h1
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hUN) (glbPrimeCore_coprime p H)

theorem D1CaseTwoDataAt.false_of_zz_prime (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hd : D1CaseTwoDataAt p P M H R Rbar) (hp5 : 5 ≤ p)
    {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₁ : IsComponentOf L₁ ⊤)
    (huL : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥)
    (hA : d1MapPCore p M H ⊓ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥)
    {z : H} (hzp : orderOf z = p)
    (hzO : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      CFSG.pCore p (H ⧸ primeComplementCore (G := H) p))
    (hzS : (z : G) ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆) : False := by
  have hp := hd.cfg.red.prime
  have h3 := hd.toPhaseThree hAut hS hKL
  have hzT : (z : G) ∈ nclIn M (pCoreOf 2 H) :=
    nclIn_le ((hd.commutator_nclIn_le hAut hS hKL h84 hD2 fun L hL => huL L hL ▸ hmeet).trans
      (le_nclIn h3.twoCore_le)) (nclIn_le_self M _) (le_normalizer_nclIn M _) hzS
  have hzN : (z : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 H z.2
  have hzG : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe, hzp]
  have hzq : (z : G) ^ p ^ 1 = 1 := by
    rw [pow_one, ← hzG]
    exact pow_orderOf_eq_one _
  have hzY : (z : G) ∉ pCorePreimage p M := by
    intro hzY
    have h1 : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
        d1MapPCore p M H ⊓ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) :=
      ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hzY), hzO⟩
    rw [hA, Subgroup.mem_bot] at h1
    have hpN := Subgroup.orderOf_dvd_natCard _ ((mk'_primeComplementCore_eq_one_iff p z).mp h1)
    rw [hzG] at hpN
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime p H) hpN
  obtain ⟨L, hL, -, V, hV, hVp, hpV⟩ := h3.exists_component_of_not_mem h84 h85 h86 h93 hD2 hKin
    hKP hC3 hK5 hp5 hzT hzN hzq hzY
  have hLK : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ H ⊓ M := by
    rw [h3.normalizer_twoCore_H]
    exact inf_le_inf_left H hL.le
  have hcop := coprime_card_of_le_barM_of_perfect inf_le_right
    (fun U hU hUp => hd.coprime_card_of_perfect hAut hS hKL hSch hL₁ huL hU hUp)
    (hV.trans (barM_mono hLK)) hVp
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop hpV

theorem D1CaseTwoData.false_of_zz_prime (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hd : D1CaseTwoData p P M H R Rbar) (hp5 : 5 ≤ p)
    {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₁ : IsComponentOf L₁ ⊤)
    (huL : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥)
    (hA : d1MapPCore p M H ⊓ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥)
    {z : H} (hzp : orderOf z = p)
    (hzO : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      CFSG.pCore p (H ⧸ primeComplementCore (G := H) p))
    (hzS : (z : G) ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆) : False :=
  D1CaseTwoDataAt.false_of_zz_prime (hAut := (kFactCycAut_of_kFactBeta hβ)) (hS := hS) (hKL := hKL)
    (hSch := hSch) (h84 := h84) (h85 := h85) (h86 := h86) (h93 := h93) (hD2 := hD2) (hKin := hKin)
    (hKP := hKP) (hC3 := hC3) (hK5 := hK5) (hd := hd.toAt) (hp5 := hp5) (hL₁ := hL₁) (huL := huL)
    (hmeet := hmeet) (hA := hA) (hzp := hzp) (hzO := hzO) (hzS := hzS)

end Data

theorem d1CaseTwoZZ_of_zzThree (hβ : KFactBeta) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hKin : KFactTwoGenInner)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hz3 : D1CaseTwoZZThree) : D1CaseTwoZZ := by
  intro G _ _ p P M H R Rbar hd huniq L₁ hL₁ huL hmeet hA hW z hzR hzp hzO hzS
  by_cases hp3 : p = 3
  · subst hp3
    exact hz3 G P M H R Rbar hd huniq L₁ hL₁ huL hmeet hA hW z hzR hzp hzO hzS
  · exact hd.false_of_zz_prime hβ hS hKL hSch h84 h85 h86 h93 hD2 hKin hKP hC3 hK5
      (hd.cfg.red.prime.five_le_of_ne_two_of_ne_three hd.cfg.red.ne_two hp3) hL₁ huL hmeet hA hzp hzO
      hzS

end CFSG.AGLEmbedding
