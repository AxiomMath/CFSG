module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePPrime
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeOdd
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSP
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeSplit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.mem_primeCore_cz_of_mk_mem (hβ : KFactBeta) (hKO : KFactOneLie)
    (hd : D1OneSmallData 3 P M H R Rbar K) {z : G} (hz : D1SmallCZElt 3 H R K z)
    (hSP : D1CzSP 3 z) (hout : D1CzOutside 3 z) {g : G}
    (hgC : g ∈ Subgroup.centralizer ({z} : Set G)) (hgM : g ∈ M)
    (hg : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hgM⟩ ∈
      primeComplementCore (G := ↥M ⧸ CFSG.pCore 2 ↥M) 3) :
    (⟨g, hgC⟩ : Subgroup.centralizer ({z} : Set G)) ∈
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hzR, -, -, -⟩ := id hz
  obtain ⟨P', Pbar, KC, -, -, hRP', hRC⟩ := hd.exists_reducedCentralizer hz hSP
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCdef
  set Oz : Subgroup C := primeComplementCore (G := C) 3 with hOz
  set ρ : C →* C ⧸ Oz := QuotientGroup.mk' Oz with hρ
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzp3⟩ := hRC.center ⟨z, hzC⟩ rfl
  have hzK : ρ ⟨z, hzC⟩ ∉ KC := hout KC hRC.comp
  obtain ⟨hKCs, hKCna, hKCc, hAut, T, hTnc, hΓT⟩ := hRC.red.exists_sylow_of_not_mem
    hRC.four_le_pRank hRC.catalog hzZ hzp3 hRC.comp hRC.normal hzK hβ
  have hUK : KFactUPrime 3 KC :=
    (hKO KC hKCs hKCna hKCc 3 hp (by decide) T hTnc hΓT (by omega)).uPrime
  obtain ⟨T', hT'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Pbar
    hRC.normal.isSubnormal
  have hnc : ¬ IsCyclic ((Pbar : Subgroup (C ⧸ Oz)) ⊓ KC : Subgroup (C ⧸ Oz)) := by
    intro hc
    apply hTnc
    rw [← hT'] at hc
    have e1 : (T : Subgroup KC) ≃* (T' : Subgroup KC) := Sylow.equiv T T'
    have e2 : (T' : Subgroup KC) ≃* ((T' : Subgroup KC).map KC.subtype) :=
      Subgroup.equivMapOfInjective _ _ KC.subtype_injective
    exact isCyclic_of_surjective (e1.trans e2).symm.toMonoidHom (MulEquiv.surjective _)
  have hzRb : ρ ⟨z, hzC⟩ ∈ (Pbar : Subgroup (C ⧸ Oz)) := by
    rw [hRC.sylow_eq]
    exact ⟨⟨z, hzC⟩, hRP' hzR, rfl⟩
  have hzcen : ρ ⟨z, hzC⟩ ∈ Subgroup.centralizer (KC : Set (C ⧸ Oz)) :=
    Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hzZ g
  have hU' := hRC.red.primeComplementCore_eq_bot_of_uPrimeHyp
    (hRC.red.uPrimeHyp_of_rankOne hRC.comp hnc hzRb hzK hzp3 hzcen hUK)
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmkM
  set X₀ : Subgroup (C ⧸ Oz) := ((C ⊓ M).subgroupOf C).map ρ with hX₀
  set N3 : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :=
    primeComplementCore (G := ↥M ⧸ CFSG.pCore 2 ↥M) 3 with hN3
  set Yh : Subgroup G := (N3.comap mkM).map M.subtype with hYh
  have hYhM : Yh ≤ M := Subgroup.map_subtype_le _
  have hcop2 : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr (by decide)).pow_right k
  have hYh3 : ∀ y ∈ Yh, Nat.Coprime 3 (orderOf y) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : Nat.Coprime 3 (orderOf (mkM y)) :=
      (primeComplementCore_coprime 3).coprime_dvd_right (Subgroup.orderOf_dvd_natCard N3 hy)
    have h2 : y ^ orderOf (mkM y) ∈ CFSG.pCore 2 ↥M :=
      (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact pow_orderOf_eq_one _)
    have h3 := Subgroup.orderOf_dvd_natCard _ h2
    have h4 : orderOf y ∣ orderOf (mkM y) * orderOf (y ^ orderOf (mkM y)) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    exact Nat.Coprime.coprime_dvd_right h4 (Nat.Coprime.mul_right h1 (hcop2.coprime_dvd_right h3))
  set Yt : Subgroup (C ⧸ Oz) := ((C ⊓ Yh).subgroupOf C).map ρ with hYt
  have hYtX : Yt ≤ X₀ := Subgroup.map_mono fun y hy => ⟨y.2, hYhM hy.2⟩
  have hYt3 : Nat.Coprime 3 (Nat.card Yt) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h
    obtain ⟨y, hy, hyw⟩ := w.2
    have h1 : orderOf (w : C ⧸ Oz) ∣ orderOf y := hyw ▸ orderOf_map_dvd ρ y
    rw [Subgroup.orderOf_coe, hw] at h1
    have h2 : Nat.Coprime 3 (orderOf y) := by
      rw [← Subgroup.orderOf_coe]
      exact hYh3 _ hy.2
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp h2 h1
  have hYtn : (Yt.subgroupOf X₀).Normal := by
    constructor
    intro w hw x
    obtain ⟨c, hc, hcx⟩ := x.2
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_subgroupOf.mp hw
    refine Subgroup.mem_subgroupOf.mpr ⟨c * y * c⁻¹, ⟨(c * y * c⁻¹).2, ?_⟩, ?_⟩
    · have hcM : (c : G) ∈ M := (Subgroup.mem_subgroupOf.mp hc).2
      obtain ⟨y', hy', hy'y⟩ := hy.2
      have hn : (N3.comap mkM).Normal := Subgroup.Normal.comap inferInstance mkM
      refine ⟨⟨c, hcM⟩ * y' * ⟨c, hcM⟩⁻¹, hn.conj_mem y' hy' ⟨c, hcM⟩, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hy'y ⊢
      rw [hy'y]
    · simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hcx, hyw]
  have hYt1 : Yt.subgroupOf X₀ ≤ primeComplementCore (G := X₀) 3 :=
    normal_coprime_le_primeComplementCore 3 _ hYtn
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYtX).toEquiv]; exact hYt3)
  rw [hU'] at hYt1
  have hgY : g ∈ Yh := ⟨⟨g, hgM⟩, hg, rfl⟩
  have hρg : ρ ⟨g, hgC⟩ = 1 := by
    have h1 : ρ ⟨g, hgC⟩ ∈ Yt := ⟨⟨g, hgC⟩, ⟨hgC, hgY⟩, rfl⟩
    have h2 : (⟨ρ ⟨g, hgC⟩, hYtX h1⟩ : X₀) ∈ Yt.subgroupOf X₀ := h1
    exact congrArg Subtype.val (Subgroup.mem_bot.mp (hYt1 h2))
  exact (QuotientGroup.eq_one_iff _).mp hρg

theorem D1OneSmallData.false_of_component_le_primeCore_three (hβ : KFactBeta)
    (hKO : KFactOneLie) (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier)
    (hKP : KFactPPrimeCompInvolutionP) (hd : D1OneSmallData 3 P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt 3 H R K z) (hSP : D1CzSP 3 z) (hout : D1CzOutside 3 z)
    {L : Subgroup G} (hL2 : IsTwoPrimeComponent M L) (hLN : L ≤ GLBPrimeCore 3 H) : False := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hzR, hzp, hzH, -⟩ := id hz
  have hzM : z ∈ M := hd.cfg.ext.le_M hzR
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmkM
  set zb := mkM ⟨z, hzM⟩ with hzb
  have hz3 : z ^ 3 = 1 := by rw [← hzp]; exact pow_orderOf_eq_one z
  have hzbp : zb ^ 3 = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hZ := fun (W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (hWp : ⁅W, W⁆ = W)
      (hWz : W ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M))) =>
    hd.eq_bot_of_perfect_le_centralizer hβ hKO hΓ hSch hz hSP hout hzM hWp hWz
  set Lb := barM M L with hLb
  have hLbC : IsComponentOf Lb ⊤ := hL2.component
  have hLbc : CFSG.IsComponent Lb := (CFSG.isComponent_iff_open Lb).mpr hLbC
  have h3L : Nat.Coprime 3 (Nat.card Lb) := by
    have hcop : Nat.Coprime 3 (Nat.card L) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLN) (glbPrimeCore_coprime 3 H)
    have hdvd : Nat.card Lb ∣ Nat.card L := by
      have := Subgroup.card_map_dvd (L.subgroupOf M) mkM
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL2.le).toEquiv] at this
    exact Nat.Coprime.coprime_dvd_right hdvd hcop
  have hzN : zb ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    by_contra hn
    obtain ⟨W, hWp, hWz, hW1⟩ := exists_perfect_diag hLbc hzbp hn
    exact hW1 (hZ W hWp hWz)
  have hzC : zb ∉ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro hc
    have hLz : Lb ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc l hl)
    have hLbp : ⁅Lb, Lb⁆ = Lb := by
      have h := congrArg (Subgroup.map Lb.subtype) hLbC.2.2.1
      rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
    exact ne_bot_of_component hLbC (hZ Lb hLbp hLz)
  have hMtop : M ≠ ⊤ := fun hM => hd.cfg.ext.not_le (hM ▸ le_top)
  have hcat : IsCatalogGroup (↥Lb ⧸ Subgroup.center ↥Lb) :=
    ((catalogSimpleSections_of_isKProper hd.cfg.glob.kProper M hMtop).quotient
      _).isCatalogGroup_center_quotient hLbC
  have hidx : ¬ 3 ∣ (Subgroup.center Lb).index := fun h =>
    (Nat.Prime.coprime_iff_not_dvd hp).mp h3L (h.trans (Subgroup.index_dvd_card _))
  obtain ⟨j, hjL, hj1, hj2, hjz, -⟩ := hKP (↥M ⧸ CFSG.pCore 2 ↥M) 3 hp (by decide) Lb hLbc hcat
    hidx ⊥ zb bot_le (fun a ha => by rw [Subgroup.mem_bot.mp ha, one_pow]; exact one_mem _)
    hzN hzbp (fun t ht => by rw [Subgroup.mem_bot.mp ht]; simp) hzC
  have hcop2 : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr (by decide)).pow_right k
  have hzMp : orderOf (⟨z, hzM⟩ : M) = 3 := (Subgroup.orderOf_coe _).symm.trans hzp
  obtain ⟨g, hg, hgj⟩ := exists_mem_centralizer_mk_eq hp (CFSG.pCore 2 ↥M) hcop2
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzMp, pow_one]))
    (x := j) (Subgroup.mem_centralizer_singleton_iff.mpr hjz)
  have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
  have hLN3 : Lb ≤ primeComplementCore (G := ↥M ⧸ CFSG.pCore 2 ↥M) 3 :=
    le_primeComplementCore_three_of_subnormal hLbc.2 h3L
  have hgO := hd.mem_primeCore_cz_of_mk_mem hβ hKO hz hSP hout hgC g.2
    (show mkM ⟨(g : G), g.2⟩ ∈ primeComplementCore (G := ↥M ⧸ CFSG.pCore 2 ↥M) 3 by
      rw [show (⟨(g : G), g.2⟩ : M) = g from rfl, hgj]; exact hLN3 hjL)
  obtain ⟨-, -, -, -, hodd⟩ := hd.odd_card_primeCore_cz hz hSP
  have hOcard : Nat.card (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3) =
      Nat.card (GLBPrimeCore 3 (Subgroup.centralizer ({z} : Set G))) := by
    rw [← glbPrimeCore_subgroupOf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (glbPrimeCore_le 3 _)).toEquiv
  have h1 : orderOf (⟨g, hgC⟩ : Subgroup.centralizer ({z} : Set G)) ∣
      Nat.card (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3) :=
    Subgroup.orderOf_dvd_natCard _ hgO
  have h2 : orderOf j ∣ orderOf g := hgj ▸ orderOf_map_dvd mkM g
  have hj2' : orderOf j = 2 := orderOf_eq_prime hj2 hj1
  have h3 : orderOf (⟨g, hgC⟩ : Subgroup.centralizer ({z} : Set G)) = orderOf g := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe g]
  rw [hj2', ← h3] at h2
  rw [hOcard] at h1
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans h1))

theorem d1SmallSPLZeroIbThreeComps_of_blocks (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier)
    (hKP : KFactPPrimeCompInvolutionP) (hB : D1SmallSPLZeroIbThreeBlocks) :
    D1SmallSPLZeroIbThreeComps := by
  intro G _ _ P M H R Rbar K hd huniq z hz hspl hSP hout hV hnIa hOp hXL L hL2 hor
  rcases hor with hw | hle
  · exact hB G P M H R Rbar K hd huniq z hz hspl hSP hout hV hnIa hOp hXL L hw
  · exact (D1OneSmallData.false_of_component_le_primeCore_three hβ hKO hΓ hSch hKP hd hz hSP
      hout hL2 hle).elim

theorem d1SmallSPLZeroIbThreeCore_of_blocks (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier)
    (hKS : KFactSPLInvolveScalar) (hKP : KFactPPrimeCompInvolutionP)
    (hB : D1SmallSPLZeroIbThreeBlocks) : D1SmallSPLZeroIbThreeCore :=
  d1SmallSPLZeroIbThreeCore_of_comps hβ hSch hKS
    (d1SmallSPLZeroIbThreeComps_of_blocks hβ hKO hΓ hSch hKP hB)

end CFSG.AGLEmbedding
