module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEVK
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarData
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPShape

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseTwoNormalForm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
      D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) →
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
        (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H → False

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.exists_cand_of_le (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) {N : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hNR : N ≤ (Rbar : Subgroup _))
    (hNn : (Rbar : Subgroup _) ≤
      Subgroup.normalizer (N : Set (H ⧸ primeComplementCore (G := H) p)))
    (hN1 : N ≠ ⊥)
    (hNL : N ≤ Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))) :
    ∃ z : H, D1CaseTwoCand p M H R z := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set Rb := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) with hRb
  set N' : Subgroup Rb := N.subgroupOf Rb with hN'
  have : N'.Normal := by
    refine ⟨fun a ha g => ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hNn g.2) a).mp ha
  have hN'1 : N' ≠ ⊥ := by
    intro h
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNR hx⟩ : Rb) ∈ N' := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  have : Group.IsNilpotent Rb := Rbar.isPGroup'.isNilpotent
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'1
  have hpg : IsPGroup p (N' ⊓ Subgroup.center Rb : Subgroup Rb) :=
    Rbar.isPGroup'.to_subgroup _
  obtain ⟨c, hcmem, hcp, -⟩ := exists_mem_centralizer_orderOf_eq hpg hZ
  have hcR : (c : H ⧸ primeComplementCore (G := H) p) ∈ (Rbar : Subgroup _) := c.2
  rw [hd.cfg.rbar] at hcR
  obtain ⟨r, hrR, hrc⟩ := hcR
  have hO := primeComplementCore_coprime (G := H) p
  have hRO : ∀ s : H, (s : G) ∈ R → s ∈ primeComplementCore (G := H) p → s = 1 := by
    intro s hs hsO
    obtain ⟨k, hk⟩ := hd.cfg.ext.isPGroup ⟨s, hs⟩
    have h1 : orderOf s ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : orderOf s ∣ Nat.card (primeComplementCore (G := H) p) :=
      Subgroup.orderOf_dvd_natCard _ hsO
    have h3 : orderOf s = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.coprime_dvd_right h2 hO).symm.pow_right k) h1
    exact orderOf_eq_one_iff.mp h3
  have hrR' : ((r : H) : G) ∈ R := hrR
  have hc1 : (c : H ⧸ primeComplementCore (G := H) p) ≠ 1 := by
    intro h
    have : orderOf (c : H ⧸ primeComplementCore (G := H) p) = p := by
      rw [Subgroup.orderOf_coe, hcp]
    rw [h, orderOf_one] at this
    exact hp.one_lt.ne this
  have hro : orderOf ((r : H) : G) = p := by
    rw [Subgroup.orderOf_coe]
    apply orderOf_eq_prime
    · apply hRO
      · rw [Subgroup.coe_pow]
        exact R.pow_mem hrR' p
      · rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow,
          show QuotientGroup.mk' (primeComplementCore (G := H) p) (r : H) = c from hrc]
        have : orderOf (c : H ⧸ primeComplementCore (G := H) p) = p := by
          rw [Subgroup.orderOf_coe, hcp]
        exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
    · intro h
      apply hc1
      rw [← hrc]
      show QuotientGroup.mk' _ (r : H) = 1
      rw [h, map_one]
  have hRr : R ≤ Subgroup.centralizer ({((r : H) : G)} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsH : s ∈ H := hd.cfg.ext.le_H hs
    have hsc : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨s, hsH⟩ * c =
        c * QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨s, hsH⟩ := by
      have hsR : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨s, hsH⟩ ∈
          (Rbar : Subgroup _) := by
        rw [hd.cfg.rbar]
        exact ⟨⟨s, hsH⟩, hs, rfl⟩
      have := Subgroup.mem_center_iff.mp hcmem.2 ⟨_, hsR⟩
      exact congrArg Subtype.val this
    rw [← hrc] at hsc
    have hcomm : (⟨s, hsH⟩ : H) * r * (⟨s, hsH⟩ : H)⁻¹ * (r : H)⁻¹ = 1 := by
      apply hRO
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact R.mul_mem (R.mul_mem (R.mul_mem hs hrR') (R.inv_mem hs)) (R.inv_mem hrR')
      · rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
        simp only [map_mul, map_inv]
        rw [hsc]
        group
    have := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
    calc s * (r : G) = s * r * s⁻¹ * (r : G)⁻¹ * (r * s) := by group
      _ = r * s := by rw [this, one_mul]
  refine ⟨r, L, hL, hLX, hrR', hro, hRr, ?_⟩
  rw [hrc]
  exact hNL hcmem.1

theorem D1CaseTwoDataAt.exists_cand (hAut : KFactCycAut) (hd : D1CaseTwoDataAt p P M H R Rbar) :
    ∃ z : H, D1CaseTwoCand p M H R z := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, hL, hLX⟩ := hd.exists_not_le hAut
  by_cases hex : ∃ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₂ ⊤ ∧
      L₂ ≠ L
  · obtain ⟨L₂, hL₂, hne⟩ := hex
    refine D1CaseTwoDataAt.exists_cand_of_le hd hL hLX (N := (Rbar : Subgroup _) ⊓ L₂) inf_le_left
      ?_ ?_ ?_
    · intro r hr
      have hrN := hd.cfg.red.sylow_le_normalizer_component hL₂ hr
      set Rb := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) with hRb
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxR, hxL⟩
        exact ⟨Rb.mul_mem (Rb.mul_mem hr hxR) (Rb.inv_mem hr),
          (Subgroup.mem_normalizer_iff.mp hrN x).mp hxL⟩
      · rintro ⟨hxR, hxL⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hrN x).mpr hxL⟩
        have := Rb.mul_mem (Rb.mul_mem (Rb.inv_mem hr) hxR) hr
        simpa [mul_assoc] using this
    · obtain ⟨t, htRL, htp, -⟩ := exists_mem_sylow_inf_component hp hd.cfg.red.ne_two
        hd.cfg.red.core_eq_bot Rbar hL₂
      intro hbot
      rw [hbot, Subgroup.mem_bot] at htRL
      rw [htRL, orderOf_one] at htp
      exact hp.one_lt.ne htp
    · exact inf_le_right.trans (le_centralizer_of_component_ne hL₂ hL hne)
  · push Not at hex
    have hO1 := hd.cfg.red.pCore_ne_bot_of_unique_of_aut (hAut _ _ _ _ hd.cfg.red hd.cfg.catalog)
        hd.cyclic hd.rank hL hex
    have hOn : (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p)).Normal := CFSG.pCore_normal
    refine D1CaseTwoDataAt.exists_cand_of_le hd hL hLX
      (N := CFSG.pCore p (H ⧸ primeComplementCore (G := H) p))
      (CFSG.pCore_isPGroup.le_sylow_of_normal Rbar) ?_ hO1 ?_
    · rw [Subgroup.normalizer_eq_top]
      exact le_top
    · have hF : CFSG.fittingSubgroup (H ⧸ primeComplementCore (G := H) p) =
          CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) :=
        CFSG.Fitting_eq_pcore _ p hd.cfg.red.core_eq_bot
      have hKl : L ≤ CFSG.layer (H ⧸ primeComplementCore (G := H) p) :=
        le_sSup (show L ∈ {K : Subgroup (H ⧸ primeComplementCore (G := H) p) |
          CFSG.IsComponent K} from (CFSG.isComponent_iff_open L).mpr hL)
      have hc := CFSG.LocalCores.fitting_layer_commute (G := H ⧸ primeComplementCore (G := H) p)
      rw [hF] at hc
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
        (Subgroup.centralizer_le hKl)

theorem D1CaseTwoDataAt.vz_ne_bot (hd : D1CaseTwoDataAt p P M H R Rbar) {z : G}
    (hRz : R ≤ Subgroup.centralizer ({z} : Set G))
    (hQO : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))
    (hne : pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≠ ⊥) :
    pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) ≠ ⊥ := by
  set O := GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) with hO
  have hOM : O ≤ M := intersecting_local_primeCore_le p hd.cfg.red.prime P hd.cfg.ext.sylow_le
    hd.cfg.ext.weakCore_le (hd.cfg.ext.three_le_pRank.trans
      (pRank_mono p hd.cfg.red.prime (le_inf hRz hd.cfg.ext.le_M)))
  have hle : pCoreOf 2 M ⊓ O ≤ pCoreOf 2 O := by
    refine normal_pGroup_le_pCoreOf 2 _ O inf_le_right ?_
      ((RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le inf_le_left)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro o ho
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxQ, hxO⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M (hOM ho))
        x).mp hxQ, O.mul_mem (O.mul_mem ho hxO) (O.inv_mem ho)⟩
    · rintro ⟨hxQ, hxO⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M (hOM ho))
        x).mpr hxQ, ?_⟩
      have h := O.mul_mem (O.mul_mem (O.inv_mem ho) hxO) ho
      simpa [mul_assoc] using h
  intro hbot
  apply hne
  rw [eq_bot_iff]
  intro x hx
  have hxO : x ∈ pCoreOf 2 M ⊓ O := ⟨hx.1, hQO hx⟩
  have := hle hxO
  rw [hbot] at this
  exact this

theorem D1CaseTwoDataAt.false_of_nf_of (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo) (hd : D1CaseTwoDataAt p P M H R Rbar)
    (hnosp : D1CaseTwoNoSP p M H R) (hEV : D1CaseTwoAllOutEV p M H R)
    (hstar : ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
      D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) → ∀ Hs : Subgroup G,
      GLBIsMaxTwoLocal Hs → Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ Hs →
      False) : False := by
  obtain ⟨z, hz⟩ := hd.exists_cand hAut
  obtain ⟨hout, hB0, hQ, hEven⟩ := hEV z hz
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := id hz
  have hnSP := hnosp L hL hLX z hzR hzp hRz hzL
  have hshape := hd.czShape hAut hS hL2 hInv hSch hSyl hNo2 hz hnSP hout
  have hV := hd.vz_ne_bot hRz hshape.2 hQ
  have hloc : IsTwoLocal (Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G))) : Set G)) :=
    ⟨_, hV, RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _, rfl⟩
  obtain ⟨Hs, hLHs, hHs⟩ := exists_maximal_twoLocal hloc
  exact hstar z hz hnSP hout hB0 hQ hEven
    (hd.exists_kaxis_of_cand hAut hS hL2 hInv hSch hSyl hnosp hEV hz) Hs hHs hLHs

theorem D1CaseTwoData.false_of_nf (hβ : KFactBeta) (hα : KFactAlphaW) (hS : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hNo2 : KFactCaseTwoNoTwo)
    (hKO : LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner) (h3 : D1CaseThree)
    (hNF : D1CaseTwoNormalForm) (hd : D1CaseTwoData p P M H R Rbar)
    (hnosp : D1CaseTwoNoSP p M H R) (hEV : D1CaseTwoAllOutEV p M H R) : False :=
  hd.toAt.false_of_nf_of (kFactCycAut_of_kFactBeta hβ) hS hL2
    (kFactCaseTwoInvIn_of_kFactCaseTwoInv hInv) hSch hSyl hNo2 hnosp hEV
    fun z hz hnSP hout hB0 hQ hEven hKax Hs hHs hLHs => by
      obtain ⟨Rbars, hds, hzHs, hzs⟩ := D1CaseTwoData.caseTwoData_star hβ hα hS hInv hSch hSyl
        hKO h3 hd hz hnSP hout hB0 hHs hLHs
      exact hNF G p P M Hs R Rbars hds ⟨z, hzHs⟩ hzs hnSP hout hB0 hQ hEven hKax hLHs

section Residues

variable (hβ : KFactBeta) (hα : KFactAlphaW) (hS : KFactSeitzCyc) (hL2 : KFactCaseTwoLocal)
  (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier) (hSyl : KFactCaseTwoSylow)
  (hNo2 : KFactCaseTwoNoTwo) (hKO : LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner)
  (h3 : D1CaseThree) (hNF : D1CaseTwoNormalForm)

include hβ hα hS hL2 hInv hSch hSyl hNo2 hKO h3 hNF

theorem d1CaseTwoPosZeroEV_of_nf : D1CaseTwoPosZeroEV := by
  intro G _ _ p P M H R Rbar hd hnosp hEV _ _
  exact D1CaseTwoData.false_of_nf hβ hα hS hL2 hInv hSch hSyl hNo2 hKO h3 hNF hd hnosp hEV

theorem d1CaseTwoNTwoAResEV_of_nf : D1CaseTwoNTwoAResEV := by
  intro G _ _ p P M H R Rbar hd hnosp hEV _ _ _ _ _ _ _ _ _
  exact D1CaseTwoData.false_of_nf hβ hα hS hL2 hInv hSch hSyl hNo2 hKO h3 hNF hd hnosp hEV

theorem d1CaseTwoZZThreeEV_of_nf : D1CaseTwoZZThreeEV := by
  intro G _ _ P M H R Rbar hd hnosp hEV _ _ _ _ _ _ _ _ _ _ _ _
  exact D1CaseTwoData.false_of_nf hβ hα hS hL2 hInv hSch hSyl hNo2 hKO h3 hNF hd hnosp hEV

end Residues

end CFSG.AGLEmbedding
