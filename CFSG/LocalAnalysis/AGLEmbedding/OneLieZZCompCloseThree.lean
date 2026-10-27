module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZCompCloseDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMData
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideCore
import CFSG.LocalAnalysis.AGLEmbedding.OneLiePerfect
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJ
import CFSG.LocalAnalysis.AGLEmbedding.UPrimeComponents
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_mem_eq_commutator_of_isCyclic {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {O : Subgroup Y} (hOc : IsCyclic O) (hOp : IsPGroup p O)
    {g : Y} (hgO : g ∈ Subgroup.normalizer (O : Set Y)) {a : Y} (haO : a ∈ O)
    (hap : orderOf a = p) (hga : g * a * g⁻¹ = a⁻¹) {o : Y} (ho : o ∈ O) :
    ∃ x ∈ O, o = x * g * x⁻¹ * g⁻¹ := by
  have hp : p.Prime := Fact.out
  have hcO : ∀ x ∈ O, g * x⁻¹ * g⁻¹ ∈ O := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hgO x⁻¹).mp (O.inv_mem hx)
  have hfix : ∀ w ∈ O, g * w = w * g → w = 1 := by
    intro w hwO hwg
    by_contra hw1
    have hBp : IsPGroup p (Subgroup.zpowers w) := hOp.to_le (Subgroup.zpowers_le.mpr hwO)
    have hB1 : Subgroup.zpowers w ≠ ⊥ := fun h => hw1 (by
      have := Subgroup.mem_zpowers w
      rwa [h, Subgroup.mem_bot] at this)
    obtain ⟨k, hk⟩ := hBp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hB1 (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
    obtain ⟨⟨b, hb⟩, hbp⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers w) p
      (hk ▸ dvd_pow_self p hk0)
    rw [Subgroup.orderOf_mk] at hbp
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hbg : g * w ^ m = w ^ m * g := ((Commute.zpow_right hwg m) : _)
    have heq : Subgroup.zpowers (w ^ m) = Subgroup.zpowers a :=
      eq_of_le_of_card_eq_of_isCyclic hOc (Subgroup.zpowers_le.mpr (O.zpow_mem hwO m))
        (Subgroup.zpowers_le.mpr haO) (by rw [Nat.card_zpowers, Nat.card_zpowers, hbp, hap])
    have haw : a ∈ Subgroup.zpowers (w ^ m) := heq ▸ Subgroup.mem_zpowers a
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp haw
    have hag : g * (w ^ m) ^ n = (w ^ m) ^ n * g := (Commute.zpow_right hbg n : _)
    have h1 : (w ^ m) ^ n = ((w ^ m) ^ n)⁻¹ := by
      rw [← hga, hag, mul_inv_cancel_right]
    have h2 : ((w ^ m) ^ n) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel _
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hap] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    have := hp.two_le
    omega
  let f : O → O := fun x => ⟨x * (g * (x : Y)⁻¹ * g⁻¹), O.mul_mem x.2 (hcO x x.2)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : (x : Y) * (g * (x : Y)⁻¹ * g⁻¹) = y * (g * (y : Y)⁻¹ * g⁻¹) :=
      congrArg Subtype.val hxy
    have h2 : (x : Y) * g * (x : Y)⁻¹ = y * g * (y : Y)⁻¹ := by
      have := congrArg (· * g) h1
      simpa [mul_assoc] using this
    have hw : g * ((y : Y)⁻¹ * x) = ((y : Y)⁻¹ * x) * g := by
      calc g * ((y : Y)⁻¹ * x) = (y : Y)⁻¹ * (y * g * (y : Y)⁻¹) * x := by group
        _ = (y : Y)⁻¹ * (x * g * (x : Y)⁻¹) * x := by rw [h2]
        _ = ((y : Y)⁻¹ * x) * g := by group
    have := hfix _ (O.mul_mem (O.inv_mem y.2) x.2) hw
    rw [inv_mul_eq_one] at this
    exact Subtype.ext this.symm
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨o, ho⟩
  refine ⟨x, x.2, ?_⟩
  have h := congrArg Subtype.val hx
  simp only [f] at h
  rw [← h]
  group

section ThreeSlice

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneLieData.inf_d1PlusCore_le_of_mem (hd : D1OneLieData p P M H R Rbar K)
    (hI : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    {V : Subgroup G} (hVN : V ≤ d1PlusCore p H K)
    (hNV : d1PlusCore p H K ≤ Subgroup.normalizer (V : Set G)) {a g : G} (haV : a ∈ V)
    (hgV : g ∈ V) (hap : orderOf a = p) (hga : g * a * g⁻¹ * a ∈ GLBPrimeCore p H) :
    R ⊓ d1PlusCore p H K ≤ V := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨hNHM, hHN, hON⟩ := hd.d1PlusCore_facts
  have hNH : d1PlusCore p H K ≤ H := hNHM.trans inf_le_left
  set C := Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) with hC
  set O := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ C with hO
  obtain ⟨z₀, hz₀R, hz₀K, hz₀p, hz₀c⟩ := hd.z
  obtain ⟨-, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hz₀R hz₀K hz₀p hz₀c
  have hOp : IsPGroup p O := Rbar.isPGroup'.to_le inf_le_left
  have hOc : IsCyclic O := hd.cfg.red.isCyclic_of_le_centralizer hd.comp hKX₀ hOp inf_le_right
  have hcomm : O ≤ Subgroup.centralizer (O : Set (H ⧸ primeComplementCore (G := H) p)) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr
      ⟨⟨fun x y => (IsCyclic.commGroup (α := O)).mul_comm x y⟩⟩
  have hcoreO : CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) ≤ O :=
    le_inf (IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup Rbar)
      (pCore_le_centralizer_component p hd.comp)
  have hOcore : O ≤ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) := by
    refine le_pCore_of_le_centralizer_components hOp (fun L hL => (hI L hL) ▸ inf_le_right)
      fun l hl => ?_
    by_cases hlp : l = p
    · subst hlp
      exact hcomm.trans (Subgroup.centralizer_le hcoreO)
    · have : Fact l.Prime := ⟨hl⟩
      have hbot : CFSG.pCore l (H ⧸ primeComplementCore (G := H) p) = ⊥ := by
        refine le_bot_iff.mp (hd.cfg.red.core_eq_bot ▸
          normal_coprime_le_primeComplementCore p _ CFSG.pCore_normal ?_)
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := l)
          (G := H ⧸ primeComplementCore (G := H) p)).exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp hl).mpr (Ne.symm hlp))
      rw [hbot]
      intro x _
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  have hOeq : O = CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) := le_antisymm hOcore hcoreO
  have hOn : O.Normal := hOeq ▸ CFSG.pCore_normal
  have haH : a ∈ H := hNH (hVN haV)
  have hgH : g ∈ H := hNH (hVN hgV)
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hmkC : ∀ x (hx : x ∈ d1PlusCore p H K), π ⟨x, hNH hx⟩ ∈ C := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  have ha1 : π ⟨a, haH⟩ ≠ 1 := by
    intro h1
    have haN : a ∈ GLBPrimeCore p H := (mk'_primeComplementCore_eq_one_iff p _).mp h1
    have hdvd := Subgroup.orderOf_dvd_natCard _ haN
    rw [hap] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime p H) hdvd
  have hap' : orderOf (π ⟨a, haH⟩) = p := by
    refine orderOf_eq_prime ?_ ha1
    rw [← map_pow]
    have : (⟨a, haH⟩ : H) ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ← hap,
      pow_orderOf_eq_one, Subgroup.coe_one])
    rw [this, map_one]
  have haO : π ⟨a, haH⟩ ∈ O := by
    have hzp : IsPGroup p (Subgroup.zpowers (π ⟨a, haH⟩)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hap', pow_one])
    obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
    obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq (H ⧸ primeComplementCore (G := H) p) Rbar Q
    have hmem : π ⟨a, haH⟩ ∈ ((c • Rbar : Sylow p _) : Subgroup _) := hQ (Subgroup.mem_zpowers _)
    rw [coe_smul_sylow_eq_map_conj] at hmem
    obtain ⟨y, hyR, hyc⟩ := hmem
    have hyC : y ∈ C := by
      have e : y = c⁻¹ * π ⟨a, haH⟩ * c⁻¹⁻¹ := by
        rw [← hyc]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e]
      exact (inferInstance : C.Normal).conj_mem _ (hmkC a (hVN haV)) c⁻¹
    have hyO : y ∈ O := ⟨hyR, hyC⟩
    rw [← hyc]
    exact hOn.conj_mem y hyO c
  have hgO : π ⟨g, hgH⟩ ∈ Subgroup.normalizer (O : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hOn]
    exact Subgroup.mem_top _
  have hga' : π ⟨g, hgH⟩ * π ⟨a, haH⟩ * (π ⟨g, hgH⟩)⁻¹ = (π ⟨a, haH⟩)⁻¹ := by
    have h1 : π (⟨g, hgH⟩ * ⟨a, haH⟩ * (⟨g, hgH⟩ : H)⁻¹ * ⟨a, haH⟩) = 1 :=
      (mk'_primeComplementCore_eq_one_iff p _).mpr hga
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hOV : O ≤ (V.subgroupOf H).map π := by
    intro o ho
    obtain ⟨x, hxO, rfl⟩ := exists_mem_eq_commutator_of_isCyclic hd.cfg.red.ne_two hOc hOp hgO
      haO hap' hga' ho
    have hxC : x ∈ C := hxO.2
    obtain ⟨n, hn, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := H) p) x
    have hnN : (n : G) ∈ d1PlusCore p H K := ⟨n, hxC, rfl⟩
    have hngV : (n : G) * g * (n : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hNV hnN) g).mp hgV
    have e : π n * π ⟨g, hgH⟩ * (π n)⁻¹ * (π ⟨g, hgH⟩)⁻¹ =
        π (n * ⟨g, hgH⟩ * n⁻¹ * (⟨g, hgH⟩ : H)⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [e]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ?_)
    simpa using V.mul_mem hngV (V.inv_mem hgV)
  intro r ⟨hrR, hrN⟩
  have hrH : r ∈ H := hNH hrN
  have hrO : π ⟨r, hrH⟩ ∈ O := by
    refine ⟨?_, hmkC r hrN⟩
    rw [hd.cfg.rbar]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hrR)
  obtain ⟨v, hv, hvr⟩ := hOV hrO
  have hn : (v : G)⁻¹ * r ∈ GLBPrimeCore p H :=
    (mk'_primeComplementCore_eq_one_iff p (v⁻¹ * ⟨r, hrH⟩)).mp
      (by rw [map_mul, map_inv, hvr, inv_mul_cancel])
  have hrsup : r ∈ V ⊔ GLBPrimeCore p H := by
    have e : r = v * ((v : G)⁻¹ * r) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hv) hn
  have hVsup : V ⊔ GLBPrimeCore p H ≤ Subgroup.normalizer (V : Set G) :=
    sup_le Subgroup.le_normalizer (hON.trans hNV)
  have hrp : IsPGroup p (Subgroup.zpowers r) :=
    hd.cfg.ext.isPGroup.to_le (Subgroup.zpowers_le.mpr hrR)
  exact le_of_le_sup_of_coprime_card_of_le (Subgroup.zpowers_le.mpr hrsup) le_sup_left
    le_sup_right ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hVsup) hrp
    (glbPrimeCore_coprime p H).symm (Subgroup.zpowers_le.mpr hrsup) (Subgroup.mem_zpowers r)

theorem D1OneLieData.card_inf_d1PlusCore_le_three (hK : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hExp3 : KFactBlockSylowThreeExp) (hd : D1OneLieData p P M H R Rbar K)
    (hI : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K)
    (hp3 : p = 3) {B : Subgroup G} (hBw : IsWeakSBlock M (pCoreOf 2 H) B)
    (hRB : R ⊓ d1PlusCore p H K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ B)
    (hBN : Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ B ≤ d1PlusCore p H K) :
    Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) ≤ 3 := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := hd.toPhaseThree hK
  set S := pCoreOf 2 H with hS
  set N := d1PlusCore p H K with hNdef
  set V := Subgroup.normalizer (S : Set G) ⊓ B with hV
  obtain ⟨hNHM, hHN, -⟩ := hd.d1PlusCore_facts
  have hNH : N ≤ H := hNHM.trans inf_le_left
  have hRNp : IsPGroup p (R ⊓ N : Subgroup G) := hd.cfg.ext.isPGroup.to_le inf_le_left
  have hRN3 : IsPGroup 3 (R ⊓ N : Subgroup G) := hp3 ▸ hRNp
  have hRNc : IsCyclic (R ⊓ N : Subgroup G) := hd.isCyclic_of_le_d1PlusCore inf_le_right hRNp
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p (R ⊓ N) N :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hd.cfg.ext.isSylow hNH hHN
  obtain ⟨-, -, hndvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hsyl
  have hidxV : ¬ 3 ∣ (R ⊓ N).relIndex V := by
    intro h
    apply hndvd
    rw [hp3, ← Subgroup.relIndex_mul_relIndex _ _ _ hRB hBN]
    exact Dvd.dvd.mul_right h _
  have hVM : V ≤ M := inf_le_right.trans hBw.le
  set A := barM M (R ⊓ N) with hA
  set PB := barM M V with hPB
  have hAPB : A ≤ PB := barM_mono hRB
  have hcopQ : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hAcard : Nat.card A = Nat.card (R ⊓ N : Subgroup G) := by
    rw [hA, barM, card_map_mk_of_isPGroup Nat.prime_three _ hcopQ
      (show IsPGroup 3 ((R ⊓ N).subgroupOf M) from hRN3.comap_subtype),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hRB.trans hVM)).toEquiv]
  have hAp : IsPGroup 3 A := (hRN3.comap_subtype).map _
  have : IsCyclic ((R ⊓ N).subgroupOf M) := isCyclic_of_surjective
    (Subgroup.subgroupOfEquivOfLe (hRB.trans hVM)).symm.toMonoidHom (MulEquiv.surjective _)
  have hAc : IsCyclic A := isCyclic_of_surjective _
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).subgroupMap_surjective ((R ⊓ N).subgroupOf M))
  have hidx : ¬ 3 ∣ (A.subgroupOf PB).index := by
    change ¬ 3 ∣ A.relIndex PB
    intro h
    apply hidxV
    have h1 : A.relIndex PB = ((A.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))).relIndex
        (V.subgroupOf M) := by
      rw [Subgroup.relIndex_comap]
      rfl
    have h2 : ((A.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))).relIndex (V.subgroupOf M) ∣
        ((R ⊓ N).subgroupOf M).relIndex (V.subgroupOf M) :=
      Subgroup.relIndex_dvd_of_le_left _ (Subgroup.le_comap_map _ _)
    rw [Subgroup.relIndex_subgroupOf hVM] at h2
    exact (h1 ▸ h).trans h2
  let Q₃ : Sylow 3 PB := (show IsPGroup 3 (A.subgroupOf PB) from hAp.comap_subtype).toSylow hidx
  have hQc : IsCyclic (Q₃ : Subgroup PB) := by
    change IsCyclic (A.subgroupOf PB)
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAPB).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hperf : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y) := by
    intro Y hY hYY
    have hYHM : Y ≤ H ⊓ M := by
      rw [h3.normalizer_twoCore_H] at hY
      exact hY.trans (inf_comm M H).le
    exact hp3 ▸ hd.coprime_card_of_perfect hK hΓ hI hYHM hYY
  have hle := hExp3 G M S B h3.isKGroup.1 h3.asc81bHyp hBw
    (h93 G M S B h3.isKGroup.1 h3.asc81bHyp hBw) (h3.nineThree_not_one h85 hD2 hBw).1
    (h3.not_isSylowTwoOf_inf h85 hD2 hBw) hperf Q₃ hQc
  have hQcard : Nat.card (Q₃ : Subgroup PB) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAPB).toEquiv
  rw [← hAcard, ← hQcard]
  exact hle

end ThreeSlice

end CFSG.AGLEmbedding
