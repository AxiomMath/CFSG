module

public import CFSG.GH74.GLS.C3.Layer1.Th2BalGlobal
public import CFSG.GH74.GLS.IVK.Proofs2.C3RankAdd
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.TwoThin
  CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance
  CFSG.GH74.GLS.Th2.Bal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_pRank_le_four (hG4 : pRank 2 G ≤ 4) {b : G} (hb2 : orderOf b = 2)
    {B : Subgroup G} (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hbB : b ∈ B)
    {J : Subgroup G} (hJ : IsPCompIn 2 (centralizer ({b} : Set G)) J) (hJcen : CenterlessBar J)
    (hJ2 : 2 ≤ pRank 2 ↥J) {β : G} (hβ : β ∈ B) : β ∈ normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hβJ
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hβb' : β * b = b * β := hBc β hβ b hbB
  have hβC : β ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.2 hβb'
  have hJ' : IsPCompIn 2 (centralizer ({b} : Set G)) (cj β J) := by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hJ β
    rwa [C3.Layer1.Thm1.map_conj_eq_self_of_mem hβC] at this
  have hne : cj β J ≠ J := fun h => hβJ (mem_normalizer_of_cj_eq h)
  have hle : cj β J ≤ centralizerSection J (pPrimeCoreOf 2 J) :=
    Stage1.Thm2.Recip.le_cSec_of_ne hJ' hJ hne
  obtain ⟨E₀, hE₀J, hE₀el, hE₀rk⟩ := exists_elemAbelian_pRank J
  have hEβel : CFSG.IsElementaryAbelian 2 ↥(cj β E₀) := isElementaryAbelian_cj β hE₀el
  have hEβrk : pRank 2 ↥(cj β E₀) = pRank 2 ↥J := by rw [pRank_cj, hE₀rk]
  have hEβJ' : cj β E₀ ≤ cj β J := Subgroup.map_mono hE₀J
  have hEβle : cj β E₀ ≤ centralizerSection J (pPrimeCoreOf 2 J) := hEβJ'.trans hle
  have hbJc : ∀ k ∈ J, b * k = k * b := fun k hk => (mem_centralizer_singleton_iff.1 (hJ.1 hk)).symm
  have hbEc : ∀ e ∈ cj β E₀, b * e = e * b := fun e he =>
    (mem_centralizer_singleton_iff.1 (hJ'.1 (hEβJ' he))).symm
  have hbEβ : b ∉ cj β E₀ := by
    intro hbE
    rw [mem_cj_iff] at hbE
    have hβb : β⁻¹ * b * β = b := by
      calc β⁻¹ * b * β = β⁻¹ * (b * β) := by group
        _ = β⁻¹ * (β * b) := by rw [hβb']
        _ = b := by group
    rw [hβb] at hbE
    have hbJ : b ∈ J := hE₀J hbE
    have hbO : b ∈ pPrimeCoreOf 2 J := by
      refine mem_pPrimeCoreOf_of_commutators hJcen hbJ (fun k hk => ?_)
      have : ⁅k, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hbJc k hk).symm
      rw [this]
      exact one_mem _
    have hodd : Odd (orderOf b) :=
      Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd J) (Subgroup.orderOf_dvd_natCard _ hbO)
    rw [hb2] at hodd
    exact absurd hodd (by decide)
  have hcd : CommDisj (zpowers b) (cj β E₀) := by
    refine ⟨fun p hp q hq => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hp
      exact (Commute.zpow_left (show Commute b q from hbEc q hq) m).eq
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two hb2 hz.1 with h0 | h0
      · simp [h0]
      · exact absurd (h0 ▸ hz.2) hbEβ
  have hbel := Th2.isElementaryAbelian_zpowers_of_orderOf_two hb2
  have hW₀el : CFSG.IsElementaryAbelian 2 ↥(zpowers b ⊔ cj β E₀) :=
    hcd.isElementaryAbelian_sup' hbel hEβel le_rfl le_rfl
  have hW₀rk : pRank 2 ↥(zpowers b ⊔ cj β E₀) = 1 + pRank 2 ↥J := by
    rw [hcd.pRank_sup hbel hEβel le_rfl le_rfl, Th2.pRank_zpowers_of_orderOf_two hb2, hEβrk]
  have hbcs : b ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
    C3.Layer1.Back.mem_centralizerSection_of_centralizes hbJc (TwoThin.pPrimeCoreOf_le J)
  have hW₀cs : zpowers b ⊔ cj β E₀ ≤ centralizerSection J (pPrimeCoreOf 2 J) :=
    sup_le (zpowers_le.2 hbcs) hEβle
  have hW₀2 : IsPGroup 2 ↥(zpowers b ⊔ cj β E₀) := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨S₀, hS₀J, hS₀p, hS₀card, hS₀norm⟩ :=
    IVK.Proofs2.exists_normalized_sylow_two J (zpowers b ⊔ cj β E₀) hW₀2 (fun w hw => (hW₀cs hw).1)
  have hSyl : IsSylowOf 2 S₀ J := isSylowOf_of_card hS₀J hS₀card.symm
  have hS₀W : ∀ e ∈ S₀, ∀ w ∈ zpowers b ⊔ cj β E₀, e * w = w * e := by
    intro e he w hw
    have h1 : ⁅e, w⁆ ∈ pPrimeCoreOf 2 J := (hW₀cs hw).2.2 e (hS₀J he)
    have h2 : ⁅e, w⁆ ∈ S₀ := by
      have := hS₀norm w hw e⁻¹ (S₀.inv_mem he)
      rw [commutatorElement_def]
      have e1 : e * w * e⁻¹ * w⁻¹ = e * (w * e⁻¹ * w⁻¹) := by group
      rw [e1]
      exact S₀.mul_mem he this
    have h3 : ⁅e, w⁆ ∈ S₀ ⊓ pPrimeCoreOf 2 J := ⟨h2, h1⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot J hS₀p, Subgroup.mem_bot] at h3
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  obtain ⟨E', hE'S, hE'el, hE'rk⟩ := exists_elemAbelian_pRank S₀
  have hE'rk' : pRank 2 ↥E' = pRank 2 ↥J := by rw [hE'rk, Th2.pRank_eq_of_isSylowOf hSyl]
  have hcd2 : CommDisj E' (zpowers b ⊔ cj β E₀) := by
    refine ⟨fun p hp q hq => hS₀W p (hE'S hp) q hq, ?_⟩
    refine eq_bot_iff.2 fun u hu => ?_
    obtain ⟨huE, huW⟩ := hu
    have huS : u ∈ S₀ := hE'S huE
    have huJ : u ∈ J := hS₀J huS
    have huO : u ∈ pPrimeCoreOf 2 J :=
      mem_pPrimeCoreOf_of_commutators hJcen huJ (fun k hk => (hW₀cs huW).2.2 k hk)
    have h3 : u ∈ S₀ ⊓ pPrimeCoreOf 2 J := ⟨huS, huO⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot J hS₀p] at h3
    exact h3
  have hrk := hcd2.pRank_sup hE'el hW₀el le_rfl le_rfl
  have h4 := pRank_le_top' (E' ⊔ (zpowers b ⊔ cj β E₀))
  omega

structure ObsData (B : Subgroup G) (a : G) (J D : Subgroup G) : Prop where
  a_mem : a ∈ B
  a_ne : a ≠ 1
  comp : IsPCompIn 2 (centralizer ({a} : Set G)) J
  D_le : D ≤ B
  D_card : 4 ≤ Nat.card ↥D
  D_norm : ∀ d ∈ D, d ∈ normalizer (J : Set G)
  D_faith : ∀ d ∈ D, d ≠ 1 → d ∉ centralizerSection J (pPrimeCoreOf 2 J)
  X_norm : ∀ x ∈ ⁅AG D ⊓ centralizer ({a} : Set G), B⁆, x ∈ normalizer (J : Set G)
  X_move : ∃ x ∈ ⁅AG D ⊓ centralizer ({a} : Set G), B⁆, x ∉ centralizerSection J (pPrimeCoreOf 2 J)

theorem mem_normalizer_of_piBar {a : G} {J : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J) {L : Subgroup (CentralizerBar a)}
    (hLJ : (J.subgroupOf (centralizer ({a} : Set G))).map (piBar a) = L)
    {x : G} (hx : x ∈ centralizer ({a} : Set G))
    (hxL : conjSub (piBar a ⟨x, hx⟩) L = L) : x ∈ normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({a} : Set G) with hH
  have hJH : J ≤ H := hJ.1
  have hnorm : piBar a ⟨x, hx⟩ ∈
      normalizer (((J.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) : Subgroup _) : Set _) := by
    rw [hLJ]
    exact mem_normalizer_of_conjSub_eq hxL
  have hn' := CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hJ.2 hnorm
  have h2 : (⟨x, hx⟩ : ↥H) ∈ normalizer ((J.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      x ∈ normalizer (J : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hJH]
    rfl
  exact h2.mp hn'

theorem piBar_centralizes_of_mem_cSec {a : G} {J : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J) {L : Subgroup (CentralizerBar a)}
    (hLJ : (J.subgroupOf (centralizer ({a} : Set G))).map (piBar a) = L)
    {x : G} (hx : x ∈ centralizer ({a} : Set G))
    (hxs : x ∈ centralizerSection J (pPrimeCoreOf 2 J)) :
    ∀ y ∈ L, piBar a ⟨x, hx⟩ * y = y * piBar a ⟨x, hx⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({a} : Set G) with hH
  intro y hy
  rw [← hLJ] at hy
  obtain ⟨j₀, hj₀, rfl⟩ := hy
  have hjJ : (j₀ : G) ∈ J := Subgroup.mem_subgroupOf.mp hj₀
  have hcomm : ⁅(j₀ : G), x⁆ ∈ pPrimeCoreOf 2 J := hxs.2.2 _ hjJ
  have hO : ⁅(j₀ : G), x⁆ ∈ pPrimeCoreOf 2 H := pPrimeCoreOf_le_of_pCompIn hJ hcomm
  obtain ⟨o, ho, hoe⟩ := hO
  have hoeq : o = ⁅j₀, ⟨x, hx⟩⁆ := Subtype.ext hoe
  have h1 : piBar a ⁅j₀, ⟨x, hx⟩⁆ = 1 := by
    rw [piBar_eq_one_iff, ← hoeq]
    exact ho
  rw [map_commutatorElement] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

@[expose] def WeakBalAt (B : Subgroup G) (a : G) : Prop :=
  ∀ D : Subgroup G, IsE 2 B D → ∀ c ∈ AG D ⊓ centralizer ({a} : Set G), ∀ b ∈ B,
    ⁅c, b⁆ ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G))

omit [Finite G] in
theorem isWeakKBal_two_iff {B : Subgroup G} :
    IsWeakKBal 2 B ↔ ∀ a ∈ B, a ≠ 1 → WeakBalAt B a :=
  ⟨fun h a ha ha1 D hD => h D hD a ha ha1, fun h D hD a ha ha1 => h a ha ha1 D hD⟩

theorem exists_obsData_at {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B) {a : G}
    (haB : a ∈ B) (ha1 : a ≠ 1) (hnot : ¬ WeakBalAt B a) :
    ∃ (J D : Subgroup G), ObsData B a J D ∧
      ∃ L : Subgroup (CentralizerBar a), IsComponent L ∧
        L = (J.subgroupOf (centralizer ({a} : Set G))).map (piBar a) ∧
        ¬ IsLocallyKBalanced 2 (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  unfold WeakBalAt at hnot
  push Not at hnot
  obtain ⟨D, hD, c₁, hc₁, b, hbB, hcb⟩ := hnot
  obtain ⟨hDB, hDel, hDrk⟩ := hD
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  set H := centralizer ({a} : Set G) with hH
  have hBH : B ≤ H := fun x hx => mem_centralizer_singleton_iff.mpr (hBc x hx a haB)
  have hDH : D ≤ H := fun d hd => hBH (hDB hd)
  have hDk : 2 ^ 2 ≤ Nat.card D := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hDel]
    exact Nat.pow_le_pow_right (by norm_num) hDrk
  set Y : Subgroup G := AG D ⊓ H with hYdef
  have hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
    fun d hd hd1 => inf_le_left.trans (iInf₂_le d ⟨hd, hd1⟩)
  set W : Subgroup (CentralizerBar a) := (Y.subgroupOf H).map (piBar a) with hW
  set E : Subgroup (CentralizerBar a) := (B.subgroupOf H).map (piBar a) with hE
  set N : Subgroup (CentralizerBar a) := ⁅W, E⁆ with hN
  have hcommY : ∀ y ∈ Y, ∀ β ∈ B, ⁅y, β⁆ ∈ Y := by
    intro y hyY β hβB
    have hcomm : ⁅y, β⁆ = y * (β * y⁻¹ * β⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hcomm]
    refine Y.mul_mem hyY ⟨?_, ?_⟩
    · exact conj_mem_AG (fun d hd => hBc _ hβB d (hDB hd)) ((AG D).inv_mem hyY.1)
    · exact H.mul_mem (H.mul_mem (hBH hβB) (H.inv_mem hyY.2)) (H.inv_mem (hBH hβB))
  have hNW : N ≤ W := by
    rw [hN, Subgroup.commutator_le]
    rintro _ ⟨y₀, hy₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩
    have hyY : (y₀ : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy₀
    have hbB' : (b₀ : G) ∈ B := Subgroup.mem_subgroupOf.mp hb₀
    refine ⟨⁅y₀, b₀⁆, Subgroup.mem_subgroupOf.mpr ?_, map_commutatorElement _ _ _⟩
    exact hcommY _ hyY _ hbB'
  have hN1 : N ≠ ⊥ := by
    intro h
    apply hcb
    have hcH : c₁ ∈ H := hc₁.2
    have hbH : b ∈ H := hBH hbB
    have hmem : piBar a ⁅(⟨c₁, hcH⟩ : ↥H), ⟨b, hbH⟩⁆ ∈ N := by
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ⟨⟨c₁, hcH⟩, Subgroup.mem_subgroupOf.mpr hc₁, rfl⟩
        ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hbB, rfl⟩
    rw [h, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
    exact ⟨_, hmem, rfl⟩
  obtain ⟨L, hL, hFL, hFfaith, hNL, hNnc, hnb⟩ :=
    exists_component_of_image (k := 2) (by norm_num) hDH hDk hDsq hY hNW hN1
  obtain ⟨J₀, hJ₀, hJ₀map⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hL
  set J : Subgroup G := J₀.map H.subtype with hJdef
  have hJH : J ≤ H := Subgroup.map_subtype_le J₀
  have hJsub : J.subgroupOf H = J₀ :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective H) J₀
  have hJc : IsPCompIn 2 H J := ⟨hJH, by rw [hJsub]; exact hJ₀⟩
  have hLJ : (J.subgroupOf H).map (piBar a) = L := by rw [hJsub]; exact hJ₀map
  set X : Subgroup G := ⁅Y, B⁆ with hXdef
  have hXnorm : X ≤ normalizer (J : Set G) := by
    rw [hXdef, Subgroup.commutator_le]
    intro y hy β hβ
    have hyH : y ∈ H := hy.2
    have hβH : β ∈ H := hBH hβ
    have hcY : ⁅y, β⁆ ∈ Y := hcommY y hy β hβ
    have hcH : ⁅y, β⁆ ∈ H := hcY.2
    have hcomm : (⁅(⟨y, hyH⟩ : ↥H), ⟨β, hβH⟩⁆ : ↥H) = ⟨⁅y, β⁆, hcH⟩ :=
      Subtype.ext (by simp [commutatorElement_def])
    have hmemN : piBar a ⟨⁅y, β⁆, hcH⟩ ∈ N := by
      rw [← hcomm, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
        ⟨⟨β, hβH⟩, Subgroup.mem_subgroupOf.mpr hβ, rfl⟩
    exact mem_normalizer_of_piBar hJc hLJ hcH (hNL _ hmemN)
  have hnc' : ∃ n ∈ N, ∃ x ∈ L, n * x ≠ x * n := by
    by_contra hno
    push Not at hno
    exact hNnc fun n hn x hx => hno n hn x hx
  obtain ⟨n, hn, x, hx, hnx⟩ := hnc'
  have hNmap : N = (⁅Y.subgroupOf H, B.subgroupOf H⁆).map (piBar a) := by
    rw [hN, hW, hE, Subgroup.map_commutator]
  rw [hNmap] at hn
  obtain ⟨z, hz, hzn⟩ := hn
  have hzX : (z : G) ∈ X := by
    have hle : ⁅Y.subgroupOf H, B.subgroupOf H⁆ ≤ X.subgroupOf H := by
      rw [Subgroup.commutator_le]
      intro y' hy' β' hβ'
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hy')
        (Subgroup.mem_subgroupOf.mp hβ')
    exact Subgroup.mem_subgroupOf.mp (hle hz)
  refine ⟨J, D, ⟨haB, ha1, hJc, hDB, by simpa using hDk, ?_, ?_, fun x hx => hXnorm hx,
    ⟨(z : G), hzX, ?_⟩⟩, L, hL, hLJ.symm, hnb⟩
  ·
    intro d hd
    have hdH : d ∈ H := hDH hd
    have hF : piBar a (⟨d, hdH⟩ : ↥H) ∈ (D.subgroupOf H).map (piBar a) :=
      ⟨⟨d, hdH⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    exact mem_normalizer_of_piBar hJc hLJ hdH (hFL _ hF)
  ·
    intro d hd hd1 hds
    have hdH : d ∈ H := hDH hd
    have hF : piBar a (⟨d, hdH⟩ : ↥H) ∈ (D.subgroupOf H).map (piBar a) :=
      ⟨⟨d, hdH⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    have hne : piBar a (⟨d, hdH⟩ : ↥H) ≠ 1 := by
      intro h1
      rw [piBar_eq_one_iff] at h1
      have hsq : (⟨d, hdH⟩ : ↥H) * ⟨d, hdH⟩ = 1 := Subtype.ext (hDsq d hd)
      exact hd1 (congrArg Subtype.val (eq_one_of_sq_of_mem_pPrimeCore hsq h1))
    exact hFfaith _ hF hne (piBar_centralizes_of_mem_cSec hJc hLJ hdH hds)
  ·
    intro hcs
    exact hnx (hzn ▸ piBar_centralizes_of_mem_cSec hJc hLJ z.2 hcs x hx)

section BarAct

omit [Finite G]

theorem normalizer_conj_mem {J : Subgroup G} :
    ∀ m ∈ normalizer (J : Set G), ∀ l ∈ J, m * l * m⁻¹ ∈ J :=
  fun _ hm l hl => (Subgroup.mem_normalizer_iff.mp hm l).mp hl

@[expose] noncomputable def barAct (J : Subgroup G) :
    ↥(normalizer (J : Set G)) →* MulAut (kBar J) :=
  C3.Layer1.Back.actHom (M := normalizer (J : Set G)) (L := J) normalizer_conj_mem

theorem barAct_eq_one_iff {J : Subgroup G} (m : ↥(normalizer (J : Set G))) :
    barAct J m = 1 ↔ (m : G) ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  have h := C3.Layer1.Back.actHom_ker (M := normalizer (J : Set G)) (L := J) normalizer_conj_mem
  rw [← MonoidHom.mem_ker]
  change m ∈ (C3.Layer1.Back.actHom (M := normalizer (J : Set G)) (L := J) normalizer_conj_mem).ker ↔ _
  rw [h, Subgroup.mem_subgroupOf]
  exact ⟨fun hm => hm.2, fun hm => ⟨m.2, hm⟩⟩

theorem barAct_of_mem {J : Subgroup G} {k : G} (hk : k ∈ J) :
    barAct J ⟨k, Subgroup.le_normalizer hk⟩ = MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥J) : kBar J) :=
  C3.Layer1.Back.actHom_of_mem normalizer_conj_mem hk (Subgroup.le_normalizer hk)

end BarAct

theorem mem_involutionOddCore_of_mem_pPrimeCoreOf {M : Subgroup G} {d : G} (hdM : d ∈ M)
    {x : G} (hxM : x ∈ M) (hx : x ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G))) :
    (⟨x, hxM⟩ : ↥M) ∈ involutionOddCore (⟨d, hdM⟩ : ↥M) := by
  classical
  set d₀ : ↥M := ⟨d, hdM⟩ with hd₀
  set W : Subgroup ↥M :=
    (pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ M).subgroupOf M with hW
  have hWC : W ≤ centralizer ({d₀} : Set ↥M) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hw1 : (w : G) ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
      (Subgroup.mem_subgroupOf.mp hw).1
    exact mem_centralizer_singleton_iff.mp (pPrimeCoreOf_le_self _ hw1)
  have hWn : ∀ c ∈ centralizer ({d₀} : Set ↥M), ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    have hcd : (c : G) ∈ centralizer ({d} : Set G) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val this
    have hw1 : (w : G) ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
      (Subgroup.mem_subgroupOf.mp hw).1
    rw [hW, Subgroup.mem_subgroupOf]
    exact ⟨CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore hcd hw1,
      M.mul_mem (M.mul_mem c.2 w.2) (M.inv_mem c.2)⟩
  have hWodd : Odd (Nat.card W) := by
    have h1 : Nat.card W = Nat.card ↥(pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h1]
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp (coprime_card_pPrimeCoreOf _))
      (Subgroup.card_dvd_of_le inf_le_left)
  have hW1 : W ≤ involutionOddCore d₀ :=
    CFSG.GH74.GLS.Prop27.le_involutionOddCore_of_normalized hWC hWn hWodd
  exact hW1 (by rw [hW, Subgroup.mem_subgroupOf]; exact ⟨hx, hxM⟩)

theorem map_mem_involutionOddCore {M : Subgroup G} {Z : Type*} [Group Z] (φ : ↥M →* Z)
    (hφ : Function.Surjective φ) {d : G} (hdM : d ∈ M) (hd2 : d * d = 1) {x : G} (hxM : x ∈ M)
    (hx : x ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G))) :
    φ ⟨x, hxM⟩ ∈ involutionOddCore (φ ⟨d, hdM⟩) :=
  map_involutionOddCore_le φ hφ
    (isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext hd2 : (⟨d, hdM⟩ : ↥M) * ⟨d, hdM⟩ = 1))
    (Subgroup.mem_map_of_mem φ (mem_involutionOddCore_of_mem_pPrimeCoreOf hdM hxM hx))

omit [Finite G] in
theorem AG_le_pPrimeCoreOf {D : Subgroup G} {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    AG D ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
  iInf₂_le d ⟨hd, hd1⟩

omit [Finite G] in
theorem commutator_le_Y {B D : Subgroup G} {a : G} (hB : CFSG.IsElementaryAbelian 2 ↥B) (hDB : D ≤ B)
    (haB : a ∈ B) :
    ⁅AG D ⊓ centralizer ({a} : Set G), B⁆ ≤ AG D ⊓ centralizer ({a} : Set G) := by
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hBH : B ≤ centralizer ({a} : Set G) :=
    fun x hx => mem_centralizer_singleton_iff.mpr (hBc x hx a haB)
  rw [Subgroup.commutator_le]
  intro y hyY β hβB
  have hcomm : ⁅y, β⁆ = y * (β * y⁻¹ * β⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hcomm]
  refine (AG D ⊓ centralizer ({a} : Set G)).mul_mem hyY ⟨?_, ?_⟩
  · exact conj_mem_AG (fun d hd => hBc _ hβB d (hDB hd)) ((AG D).inv_mem hyY.1)
  · exact (centralizer ({a} : Set G)).mul_mem
      ((centralizer ({a} : Set G)).mul_mem (hBH hβB) ((centralizer ({a} : Set G)).inv_mem hyY.2))
      ((centralizer ({a} : Set G)).inv_mem (hBH hβB))

omit [Finite G] in
theorem ObsData.exists_ne_one {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D) :
    ∃ d ∈ D, d ≠ 1 :=
  exists_ne_one_of_two_pow_le (k := 2) (by norm_num) (by simpa using h.D_card)

omit [Finite G] in
theorem ObsData.mem_core {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) {x : G}
    (hx : x ∈ ⁅AG D ⊓ centralizer ({a} : Set G), B⁆) {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) :
    x ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
  AG_le_pPrimeCoreOf hd hd1 (commutator_le_Y hB h.D_le h.a_mem hx).1

theorem ObsData.odd_orderOf {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) {x : G}
    (hx : x ∈ ⁅AG D ⊓ centralizer ({a} : Set G), B⁆) : Odd (orderOf x) := by
  obtain ⟨d₀, hd₀, hd₀1⟩ := h.exists_ne_one
  exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd _)
    (Subgroup.orderOf_dvd_natCard _ (h.mem_core hB hx hd₀ hd₀1))

omit [Finite G] in
theorem ObsData.comm_D {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) {x : G}
    (hx : x ∈ ⁅AG D ⊓ centralizer ({a} : Set G), B⁆) {d : G} (hd : d ∈ D) : x * d = d * x := by
  by_cases hd1 : d = 1
  · rw [hd1]; simp
  · have := pPrimeCoreOf_le_self _ (h.mem_core hB hx hd hd1)
    exact mem_centralizer_singleton_iff.mp this

theorem ObsData.exists_noncomm {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G)) :
    ∃ (y β : G) (_ : y ∈ AG D ⊓ centralizer ({a} : Set G)) (hβ : β ∈ B)
      (hx : ⁅y, β⁆ ∈ normalizer (J : Set G)),
      barAct J ⟨⁅y, β⁆, hx⟩ ≠ 1 ∧
        barAct J ⟨β, hBN β hβ⟩ * barAct J ⟨⁅y, β⁆, hx⟩ ≠
          barAct J ⟨⁅y, β⁆, hx⟩ * barAct J ⟨β, hBN β hβ⟩ := by
  by_contra hno
  push Not at hno
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  obtain ⟨x, hxX, hxmove⟩ := h.X_move
  apply hxmove
  have hXle : ⁅AG D ⊓ centralizer ({a} : Set G), B⁆ ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
    rw [Subgroup.commutator_le]
    intro y hy β hβ
    have hxX' : ⁅y, β⁆ ∈ ⁅AG D ⊓ centralizer ({a} : Set G), B⁆ :=
      Subgroup.commutator_mem_commutator hy hβ
    have hxN : ⁅y, β⁆ ∈ normalizer (J : Set G) := h.X_norm _ hxX'
    have hβN : β ∈ normalizer (J : Set G) := hBN β hβ
    change ((⟨⁅y, β⁆, hxN⟩ : ↥(normalizer (J : Set G))) : G) ∈ _
    rw [← barAct_eq_one_iff]
    by_contra hne
    have hcomm := hno y β hy hβ hxN hne
    have hgN : y * β * y⁻¹ ∈ normalizer (J : Set G) := by
      have : y * β * y⁻¹ = ⁅y, β⁆ * β := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact (normalizer (J : Set G)).mul_mem hxN hβN
    have hgg : (⟨y * β * y⁻¹, hgN⟩ : ↥(normalizer (J : Set G))) * ⟨y * β * y⁻¹, hgN⟩ = 1 := by
      apply Subtype.ext
      show y * β * y⁻¹ * (y * β * y⁻¹) = 1
      calc y * β * y⁻¹ * (y * β * y⁻¹) = y * (β * β) * y⁻¹ := by group
        _ = 1 := by rw [hBsq β hβ]; group
    have hgeq : (⟨y * β * y⁻¹, hgN⟩ : ↥(normalizer (J : Set G))) =
        ⟨⁅y, β⁆, hxN⟩ * ⟨β, hβN⟩ := by
      apply Subtype.ext
      show y * β * y⁻¹ = ⁅y, β⁆ * β
      simp only [commutatorElement_def]
      group
    have hββ : (⟨β, hβN⟩ : ↥(normalizer (J : Set G))) * ⟨β, hβN⟩ = 1 :=
      Subtype.ext (hBsq β hβ)
    set a₁ := barAct J ⟨⁅y, β⁆, hxN⟩ with ha₁
    set b₁ := barAct J ⟨β, hβN⟩ with hb₁
    have hcm : Commute a₁ b₁ := hcomm.symm
    have h1 : (a₁ * b₁) * (a₁ * b₁) = 1 := by
      have := congrArg (barAct J) hgg
      simp only [hgeq, map_mul, map_one] at this
      exact this
    have h2 : b₁ * b₁ = 1 := by
      have := congrArg (barAct J) hββ
      rwa [map_mul, map_one] at this
    have h3 : a₁ * a₁ = 1 := by
      have e1 : (a₁ * b₁) * (a₁ * b₁) = (a₁ * a₁) * (b₁ * b₁) := by
        rw [mul_assoc, ← mul_assoc b₁ a₁ b₁, ← hcm.eq, mul_assoc a₁ b₁ b₁, ← mul_assoc]
      rw [e1, h2, mul_one] at h1
      exact h1
    have hodd : Odd (orderOf (⟨⁅y, β⁆, hxN⟩ : ↥(normalizer (J : Set G)))) := by
      rw [Subgroup.orderOf_mk]
      exact h.odd_orderOf hB hxX'
    have h4 : orderOf a₁ ∣ orderOf (⟨⁅y, β⁆, hxN⟩ : ↥(normalizer (J : Set G))) :=
      orderOf_map_dvd (barAct J) _
    have h5 : orderOf a₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
    have h6 : orderOf a₁ = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h5 with h7 | h7
      · exact h7
      · rw [h7] at h4
        exact absurd (Odd.of_dvd_nat hodd h4) (by decide)
    exact hne (orderOf_eq_one_iff.1 h6)
  exact hXle hxX

end CFSG.GH74.GLS.Th2.Obs
