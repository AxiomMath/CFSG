module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.PGroups
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Components
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.PGroupNormalE4
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointRankFour
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerBalance
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Assembly.QuasithinDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ABGLocalTools (IsSylowOf)

structure T29Setup (X : Type) [Group X] [Finite X] (L : Subgroup X) (x : X) : Prop where
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections X
  core : primeComplementCore (G := X) 3 = ⊥
  comp : IsComponentOf L ⊤
  uniq : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = L
  rank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)
  ord : orderOf x = 3
  cent : CFSG.Open.pRank 3 (centralizer ({x} : Set X)) = 2

section Step0

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem T29Setup.normal (h : T29Setup X L x) : L.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hc := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.isComponentOf_map_conj h.comp g
  have heq : L.map (MulAut.conj g).toMonoidHom = L := h.uniq _ hc
  have hmem : (MulAut.conj g).toMonoidHom n ∈ L.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hn
  rw [heq] at hmem
  exact hmem

theorem T29Setup.pRank_top_eq (h : T29Setup X L x) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ h.rank
  by_contra hlt
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by omega
  have hxp : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord, pow_one])
  obtain ⟨P, hPx⟩ := IsPGroup.exists_le_sylow hxp
  have hxP : x ∈ (P : Subgroup X) := hPx (Subgroup.mem_zpowers x)
  have h4P : 4 ≤ CFSG.Open.pRank 3 (P : Subgroup X) :=
    le_trans h4 (CFSG.LocalAnalysis.RankThreeTheoremC.pRank_le_pRank_sylow Nat.prime_three P ⊤)
  have hx3 : x ^ 3 = 1 := by
    rw [← h.ord]
    exact pow_orderOf_eq_one x
  have h3 : 3 ≤ CFSG.Open.pRank 3 ((P : Subgroup X) ⊓ centralizer ({x} : Set X)) :=
    CFSG.LocalAnalysis.RankFourTheoremC.three_le_pRank_inf_centralizer
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.gl83NormalElementaryRankFour_holds
      P.isPGroup' h4P hxP hx3
  have hle : CFSG.Open.pRank 3 ((P : Subgroup X) ⊓ centralizer ({x} : Set X)) ≤
      CFSG.Open.pRank 3 (centralizer ({x} : Set X)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) inf_le_right
  rw [h.cent] at hle
  omega

theorem IsOmegaCentral.mem_of_normal_of_core (hcore : primeComplementCore (G := X) 3 = ⊥)
    {P : Sylow 3 X} {z : X} (hz : IsOmegaCentral (P : Subgroup X) z) {N : Subgroup X}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : z ∈ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3N : 3 ∣ Nat.card N := by
    by_contra hnd
    have hcop : Nat.Coprime 3 (Nat.card N) := (Nat.prime_three.coprime_iff_not_dvd).2 hnd
    have hle : N ≤ primeComplementCore (G := X) 3 :=
      normal_coprime_le_primeComplementCore 3 N hN hcop
    rw [hcore] at hle
    exact hN1 (eq_bot_iff.2 hle)
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 3 (P : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hKN : (⊤ : Subgroup X) ≤ normalizer (N : Set X) :=
    (Subgroup.normalizer_eq_top N : normalizer (N : Set X) = ⊤).symm.le
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 ((P : Subgroup X) ⊓ N) N :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hPtop le_top hKN
  have hne : (P : Subgroup X) ⊓ N ≠ ⊥ := by
    intro hbot
    rw [hbot, CFSG.ABGLocalTools.isSylowOf_iff] at hsyl
    obtain ⟨-, -, hnd⟩ := hsyl
    rw [Subgroup.relIndex_bot_left] at hnd
    exact hnd h3N
  have hnorm : (P : Subgroup X) ≤ normalizer (((P : Subgroup X) ⊓ N : Subgroup X) : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro m
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    constructor
    · rintro ⟨hmP, hmN⟩
      exact ⟨(P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem hg hmP)
        ((P : Subgroup X).inv_mem hg), hN.conj_mem m hmN g⟩
    · rintro ⟨hmP, hmN⟩
      have e : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m := by group
      have hA : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ ∈ (P : Subgroup X) :=
        (P : Subgroup X).mul_mem ((P : Subgroup X).mul_mem ((P : Subgroup X).inv_mem hg) hmP)
          ((P : Subgroup X).inv_mem ((P : Subgroup X).inv_mem hg))
      have hB : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ ∈ N := hN.conj_mem _ hmN g⁻¹
      rw [e] at hA hB
      exact ⟨hA, hB⟩
  have hzPN : z ∈ (P : Subgroup X) ⊓ N :=
    IsOmegaCentral.mem_of_normal P.isPGroup' hz inf_le_left hnorm hne
  exact (Subgroup.mem_inf.1 hzPN).2

end Step0

section Step0

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem le_pRank_of_isElemAbelian_card {p : ℕ} (hp : p.Prime) {Y A : Subgroup X} (hYA : Y ≤ A)
    (hY : CFSG.Open.IsElemAbelian p Y) {k : ℕ} (hk : p ^ k ≤ Nat.card Y) :
    k ≤ CFSG.Open.pRank p A := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p Y hY).exists_card_eq
  have hkj : k ≤ j := by
    rw [hj] at hk
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hk
  refine hkj.trans ?_
  unfold CFSG.Open.pRank
  exact le_csSup (CFSG.RankThreeCoreUniqueness.Helpers.pRank_set_bddAbove p hp.one_lt _)
    ⟨Y, hYA, hY, hj⟩

theorem exists_central_order_three {P : Subgroup X} (hPg : IsPGroup 3 ↥P)
    (hxP : x ∈ P) (hxne : x ≠ 1) :
    ∃ z ∈ P, (∀ y ∈ P, z * y = y * z) ∧ orderOf z = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Nontrivial ↥P := ⟨⟨⟨x, hxP⟩, 1, fun h1 => hxne (congrArg Subtype.val h1)⟩⟩
  haveI : Nontrivial ↥(Subgroup.center ↥P) := hPg.center_nontrivial
  have h3dvd : 3 ∣ Nat.card ↥(Subgroup.center ↥P) := by
    rcases (hPg.to_subgroup (Subgroup.center ↥P)).card_eq_or_dvd with h1 | h1
    · have : 1 < Nat.card ↥(Subgroup.center ↥P) := Finite.one_lt_card
      omega
    · exact h1
  obtain ⟨g0, hg0⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  refine ⟨((g0 : ↥P) : X), (g0 : ↥P).2, ?_, ?_⟩
  · intro y hy
    have h' := Subgroup.mem_center_iff.1 g0.2 ⟨y, hy⟩
    have h'' : y * ((g0 : ↥P) : X) = ((g0 : ↥P) : X) * y := congrArg Subtype.val h'
    exact h''.symm
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg0]

theorem central_unique_of_pRank {P : Subgroup X} (hxP : x ∈ P) (hx3 : x ^ 3 = 1)
    (hcent : CFSG.Open.pRank 3 (centralizer ({x} : Set X)) = 2)
    (hrankP : 3 ≤ CFSG.Open.pRank 3 P)
    {z : X} (hz3 : orderOf z = 3) (hzc : ∀ y ∈ P, z * y = y * z)
    {g : X} (hgP : g ∈ P) (hgc : ∀ y ∈ P, g * y = y * g) (hg3 : g ^ 3 = 1) :
    g ∈ zpowers z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hgz
  have hzz : z ^ 3 = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one z
  have hzg : Commute z g := hzc g hgP
  have hzK : z ∈ centralizer (P : Set X) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => (hzc y hy).symm
  have hgK : g ∈ centralizer (P : Set X) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => (hgc y hy).symm
  have hAK : zpowers z ⊔ zpowers g ≤ centralizer (P : Set X) :=
    sup_le (Subgroup.zpowers_le.2 hzK) (Subgroup.zpowers_le.2 hgK)
  have hgZ : g ∈ centralizer (zpowers z : Set X) := by
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (show h ∈ zpowers z from hh)
    exact (hzg.zpow_left k).eq
  have hcomm_g : ∀ e ∈ zpowers z, e * g = g * e := fun e he =>
    Subgroup.mem_centralizer_iff.1 hgZ e he
  haveI hiz : CFSG.IsElementaryAbelian 3 ↥(zpowers z) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hzz
  haveI hig : CFSG.IsElementaryAbelian 3 ↥(zpowers g) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hg3
  haveI hiA : CFSG.IsElementaryAbelian 3 ↥(zpowers z ⊔ zpowers g) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer (Subgroup.zpowers_le.2 hgZ)
  have hA9 : Nat.card ↥(zpowers z ⊔ zpowers g) = 9 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers z) hg3 hgz
      hcomm_g, Nat.card_zpowers, hz3] <;> norm_num
  by_cases hxA : x ∈ zpowers z ⊔ zpowers g
  ·
    have hPC : P ≤ centralizer ({x} : Set X) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hAK hxA) y hy)
    have hle := CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) hPC
    rw [hcent] at hle
    omega
  ·
    have hAx : ∀ e ∈ zpowers z ⊔ zpowers g, e * x = x * e := fun e he =>
      (Subgroup.mem_centralizer_iff.1 (hAK he) x hxP).symm
    have hAC : zpowers z ⊔ zpowers g ≤ centralizer ({x} : Set X) := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.2 (hAx e he)
    have hV27 : Nat.card ↥((zpowers z ⊔ zpowers g) ⊔ zpowers x) = 27 := by
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers z ⊔ zpowers g)
        hx3 hxA hAx, hA9] <;> norm_num
    have hxZ : x ∈ centralizer ((zpowers z ⊔ zpowers g : Subgroup X) : Set X) :=
      Subgroup.mem_centralizer_iff.2 fun e he => hAx e he
    haveI hix : CFSG.IsElementaryAbelian 3 ↥(zpowers x) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx3
    haveI hiV : CFSG.IsElementaryAbelian 3 ↥((zpowers z ⊔ zpowers g) ⊔ zpowers x) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer (Subgroup.zpowers_le.2 hxZ)
    have hVprop : CFSG.Open.IsElemAbelian 3 ((zpowers z ⊔ zpowers g) ⊔ zpowers x) :=
      ⟨hiV.toIsMulCommutative, fun y hy => CFSG.elemPow_eq_one_of_isElementaryAbelian y hy⟩
    have hVle : (zpowers z ⊔ zpowers g) ⊔ zpowers x ≤ centralizer ({x} : Set X) :=
      sup_le hAC (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
    have hk : 3 ^ 3 ≤ Nat.card ↥((zpowers z ⊔ zpowers g) ⊔ zpowers x) := by
      rw [hV27] <;> norm_num
    have h3 := le_pRank_of_isElemAbelian_card Nat.prime_three hVle hVprop hk
    rw [hcent] at h3
    omega

theorem T29Setup.exists_omegaCentral (h : T29Setup X L x) {P : Sylow 3 X}
    (hxP : x ∈ (P : Subgroup X)) : ∃ z : X, IsOmegaCentral (P : Subgroup X) z := by
  have hord : orderOf x = 3 := h.ord
  have hx3 : x ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one x
  have hxne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    norm_num at hord
  have hPg : IsPGroup 3 ↥(P : Subgroup X) := P.isPGroup'
  have hrankP : 3 ≤ CFSG.Open.pRank 3 (P : Subgroup X) := by
    obtain ⟨Q, hQ⟩ := exists_sylow_rank_at_least_three 3 Nat.prime_three h.rank
    rw [← sylow_pRank_eq 3 Nat.prime_three Q P]
    exact hQ
  obtain ⟨z, hzP, hzc, hz3⟩ := exists_central_order_three hPg hxP hxne
  exact ⟨z, hzP, hzc, hz3, fun g hgP hgc hg3 =>
    central_unique_of_pRank hxP hx3 h.cent hrankP hz3 hzc hgP hgc hg3⟩

end Step0

section CentreHelpers

variable {X : Type} [Group X] [Finite X]

theorem commute_of_mem_map_center (L : Subgroup X) {a b : X}
    (ha : a ∈ (center ↥L).map L.subtype) (hb : b ∈ (center ↥L).map L.subtype) :
    Commute a b := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hb
  have hdc : d * c = c * d := Subgroup.mem_center_iff.mp hc d
  show L.subtype c * L.subtype d = L.subtype d * L.subtype c
  exact congrArg Subtype.val hdc.symm

def threePrimeCentre (L : Subgroup X) : Subgroup X where
  carrier := {g | g ∈ (center ↥L).map L.subtype ∧ Nat.Coprime (orderOf g) 3}
  one_mem' := ⟨((center ↥L).map L.subtype).one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
    refine ⟨((center ↥L).map L.subtype).mul_mem ha hb, ?_⟩
    have hdvd : orderOf (a * b) ∣ Nat.lcm (orderOf a) (orderOf b) :=
      (commute_of_mem_map_center L ha hb).orderOf_mul_dvd_lcm
    have hcop : Nat.Coprime (Nat.lcm (orderOf a) (orderOf b)) 3 :=
      Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _) (Nat.coprime_mul_iff_left.mpr ⟨ha3, hb3⟩)
    exact Nat.Coprime.coprime_dvd_left hdvd hcop
  inv_mem' := by
    rintro a ⟨ha, ha3⟩
    refine ⟨((center ↥L).map L.subtype).inv_mem ha, ?_⟩
    rw [orderOf_inv]
    exact ha3

theorem mem_threePrimeCentre (L : Subgroup X) (g : X) :
    g ∈ threePrimeCentre L ↔ g ∈ (center ↥L).map L.subtype ∧ Nat.Coprime (orderOf g) 3 :=
  Iff.rfl

theorem orderOf_conj_eq (g n : X) : orderOf (g * n * g⁻¹) = orderOf n := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective n
  simpa [MulAut.conj_apply] using h

theorem threePrimeCentre_normal (L : Subgroup X) (hZ : ((center ↥L).map L.subtype).Normal) :
    (threePrimeCentre L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine (mem_threePrimeCentre L _).mpr ⟨hZ.conj_mem n ((mem_threePrimeCentre L n).mp hn).1 g, ?_⟩
  rw [orderOf_conj_eq]
  exact ((mem_threePrimeCentre L n).mp hn).2

theorem threePrimeCentre_coprime (L : Subgroup X) : Nat.Coprime 3 (Nat.card (threePrimeCentre L)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hdvd
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥(threePrimeCentre L)) 3 hdvd
  have hord : orderOf (r : X) = orderOf r :=
    orderOf_injective (threePrimeCentre L).subtype (threePrimeCentre L).subtype_injective r
  have hr3 : Nat.Coprime (orderOf (r : X)) 3 := ((mem_threePrimeCentre L _).mp r.2).2
  rw [hord, hr] at hr3
  exact absurd hr3 (by norm_num)

theorem ne_bot_of_isQuasisimple (L : Subgroup X) (hq : CFSG.Open.IsQuasisimple ↥L) : L ≠ ⊥ := by
  haveI : IsSimpleGroup (↥L ⧸ center ↥L) := hq.2
  haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (N := center ↥L)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance

end CentreHelpers

section Step0

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem T29Setup.pCore_inf_commute (h : T29Setup X L x) :
    ∀ g ∈ L, g ∈ CFSG.pCore 3 X → ∀ l ∈ L, l * g = g * l := by
  intro g hgL hgO l hl
  haveI hLn : L.Normal := h.normal
  haveI hNn : ((CFSG.pCore 3 X).subgroupOf L).Normal :=
    Subgroup.Normal.subgroupOf CFSG.pCore_normal L
  have hNp : IsPGroup 3 ((CFSG.pCore 3 X).subgroupOf L) :=
    (CFSG.pCore_isPGroup (p := 3) (G := X)).comap_subtype
  have hcen : (CFSG.pCore 3 X).subgroupOf L ≤ center ↥L :=
    le_center_of_normal_pGroup h.comp.2.2 ((CFSG.pCore 3 X).subgroupOf L) hNp
  have hgN : (⟨g, hgL⟩ : ↥L) ∈ (CFSG.pCore 3 X).subgroupOf L :=
    Subgroup.mem_subgroupOf.mpr hgO
  have hc := Subgroup.mem_center_iff.mp (hcen hgN) ⟨l, hl⟩
  exact congrArg Subtype.val hc

theorem T29Setup.pCore_eq_bot (h : T29Setup X L x) (hZ : center ↥L = ⊥) :
    CFSG.pCore 3 X = ⊥ := by
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hxP⟩ : ∃ P : Sylow 3 X, x ∈ (P : Subgroup X) := by
    have hp : IsPGroup 3 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord, pow_one])
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, hP (mem_zpowers x)⟩
  obtain ⟨z, hz⟩ := h.exists_omegaCentral hxP
  have hzO : z ∈ CFSG.pCore 3 X :=
    IsOmegaCentral.mem_of_normal_of_core h.core hz CFSG.pCore_normal hne
  have hzL : z ∈ L :=
    IsOmegaCentral.mem_of_normal_of_core h.core hz h.normal (ne_bot_of_isQuasisimple L h.comp.2.2)
  have hcen : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact h.pCore_inf_commute z hzL hzO (l : X) l.2
  rw [hZ, Subgroup.mem_bot] at hcen
  have hz1 : z = 1 := congrArg Subtype.val hcen
  have h3 := hz.order
  rw [hz1, orderOf_one] at h3
  norm_num at h3

theorem T29Setup.center_isPGroup (h : T29Setup X L x) : IsPGroup 3 ↥(center ↥L) := by
  haveI hLn : L.Normal := h.normal
  haveI hZn : ((center ↥L).map L.subtype).Normal := normal_map_center_subtype L
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRn : (threePrimeCentre L).Normal := threePrimeCentre_normal L hZn
  have hRle : threePrimeCentre L ≤ primeComplementCore (G := X) 3 :=
    normal_coprime_le_primeComplementCore 3 (threePrimeCentre L) hRn (threePrimeCentre_coprime L)
  rw [h.core] at hRle
  have hRbot : ∀ y ∈ threePrimeCentre L, y = 1 := fun y hy => Subgroup.mem_bot.mp (hRle hy)
  rw [IsPGroup.iff_orderOf]
  intro g
  obtain ⟨e, m, hm3, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hdvd : 3 ^ e ∣ orderOf g := ⟨m, hnm⟩
  have hyord : orderOf (g ^ 3 ^ e) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero e (by norm_num : (3 : ℕ) ≠ 0)) hdvd, hnm]
    exact Nat.mul_div_cancel_left m (pow_pos (by norm_num) e)
  have hinjZ : Function.Injective (L.subtype.comp (center ↥L).subtype) :=
    L.subtype_injective.comp (center ↥L).subtype_injective
  have hordZ : ∀ c : ↥(center ↥L),
      orderOf ((L.subtype.comp (center ↥L).subtype) c) = orderOf c :=
    fun c => orderOf_injective (L.subtype.comp (center ↥L).subtype) hinjZ c
  have hmemZ : ∀ c : ↥(center ↥L),
      (L.subtype.comp (center ↥L).subtype) c ∈ (center ↥L).map L.subtype :=
    fun c => Subgroup.mem_map.mpr ⟨c.1, c.2, rfl⟩
  have hyR : (L.subtype.comp (center ↥L).subtype) (g ^ 3 ^ e) ∈ threePrimeCentre L := by
    refine (mem_threePrimeCentre L _).mpr ⟨hmemZ _, ?_⟩
    rw [hordZ, hyord]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm
  have hy1 : (L.subtype.comp (center ↥L).subtype) (g ^ 3 ^ e) = 1 := hRbot _ hyR
  have hm1 : m = 1 := by
    have h1 : orderOf ((L.subtype.comp (center ↥L).subtype) (g ^ 3 ^ e)) = 1 := by
      rw [hy1, orderOf_one]
    rw [hordZ, hyord] at h1
    exact h1
  exact ⟨e, by rw [hnm, hm1, mul_one]⟩

theorem T29Setup.isCatalogGroup_quotient (h : T29Setup X L x) :
    IsCatalogGroup (↥L ⧸ center ↥L) := by
  haveI : IsSimpleGroup (↥L ⧸ center ↥L) := h.comp.2.2.2
  exact h.catalog.surjective_image L (QuotientGroup.mk' (center ↥L))
    (QuotientGroup.mk'_surjective (N := center ↥L))
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥L h.comp.2.2)

theorem T29Setup.isCyclic_center (h : T29Setup X L x) (hN1 : NoncyclicCentreRank) :
    IsCyclic ↥(center ↥L) := by
  by_contra hnc
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
    hN1 ↥L h.comp.2.2 h.isCatalogGroup_quotient h.center_isPGroup hnc
  have hmono : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤
      CFSG.Open.pRank 3 ((⊤ : Subgroup ↥L).map L.subtype) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) L.subtype L.subtype_injective ⊤
  have hmono2 : CFSG.Open.pRank 3 ((⊤ : Subgroup ↥L).map L.subtype) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top
  have htop := h.pRank_top_eq
  omega

end Step0

section PGroups

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_cyclic {W : Type*} [Group W] [Finite W] [IsCyclic W] {a b : W}
    (ha : a ^ 3 = 1) (hb : orderOf b = 3) : a ∈ zpowers b := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  by_contra hna
  have hb3 : b ^ 3 = 1 := by
    rw [← hb]
    exact pow_orderOf_eq_one b
  obtain ⟨F, hF⟩ : ∃ F : Finset W, F = (Finset.range 3).image (fun i : ℕ => b ^ i) :=
    ⟨_, rfl⟩
  have hinj : Set.InjOn (fun i : ℕ => b ^ i) (Finset.range 3 : Set ℕ) := by
    rw [Finset.coe_range, ← hb]
    exact pow_injOn_Iio_orderOf
  have hFcard : F.card = 3 := by
    rw [hF, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hanot : a ∉ F := by
    intro haF
    rw [hF, Finset.mem_image] at haF
    obtain ⟨i, _, hi⟩ := haF
    apply hna
    rw [← hi]
    exact pow_mem (Subgroup.mem_zpowers b) i
  have hsub : insert a F ⊆ Finset.univ.filter (fun x : W => x ^ 3 = 1) := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ x, ?_⟩
    rcases hx with rfl | hx
    · exact ha
    · rw [hF, Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      rw [← pow_mul, mul_comm, pow_mul, hb3, one_pow]
  have h1 : (insert a F).card ≤ (Finset.univ.filter (fun x : W => x ^ 3 = 1)).card :=
    Finset.card_le_card hsub
  have h2 : (insert a F).card = F.card + 1 := Finset.card_insert_of_notMem hanot
  have h3 : (Finset.univ.filter (fun x : W => x ^ 3 = 1)).card ≤ 3 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  omega

end PGroups

section Step0

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem T29Setup.not_isCyclic_inf_sylow (h : T29Setup X L x) (hZ : center ↥L ≠ ⊥)
    {P : Sylow 3 X} {z : X} (hz : IsOmegaCentral (P : Subgroup X) z) :
    ¬ IsCyclic ↥((P : Subgroup X) ⊓ L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hLn : L.Normal := h.normal
  have hPtop : IsSylowOf 3 (P : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hPL : IsSylowOf 3 ((P : Subgroup X) ⊓ L) L :=
    hPtop.inf_of_le_normalizer le_top le_normalizer_of_normal
  have hL1 : L ≠ ⊥ := by
    intro hLb
    have hsimp := h.comp.2.2.2
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have hsub1 : ∀ u v : L, u = v := by
      intro u v
      apply Subtype.ext
      have hu : (u : X) ∈ (⊥ : Subgroup X) := by
        rw [← hLb]
        exact u.2
      have hv : (v : X) ∈ (⊥ : Subgroup X) := by
        rw [← hLb]
        exact v.2
      rw [Subgroup.mem_bot.1 hu, Subgroup.mem_bot.1 hv]
    rw [hsub1 a' b'] at hab
    exact hab rfl
  have hzL : z ∈ L := IsOmegaCentral.mem_of_normal_of_core h.core hz hLn hL1
  have hZLn : ((center ↥L).map L.subtype).Normal := normal_map_center_subtype L
  have hZL1 : (center ↥L).map L.subtype ≠ ⊥ := by
    intro hm
    apply hZ
    rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hcb : (c : X) ∈ (⊥ : Subgroup X) := by
      rw [← hm]
      exact Subgroup.mem_map_of_mem L.subtype hc
    exact Subgroup.mem_bot.1 hcb
  have hzZ : z ∈ (center ↥L).map L.subtype :=
    IsOmegaCentral.mem_of_normal_of_core h.core hz hZLn hZL1
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hzZ
  have hcz' : (c : X) = z := hcz
  have hzcomm : ∀ l ∈ L, z * l = l * z := by
    intro l hl
    have h2 : (l : X) * (c : X) = (c : X) * (l : X) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨l, hl⟩)
    rw [hcz'] at h2
    exact h2.symm
  intro hcyc
  obtain ⟨t, htR, hto, l, hl, hne⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.exists_mem_sylow_component h.core h.comp hPL
  have hzR : z ∈ (P : Subgroup X) ⊓ L := ⟨hz.mem, hzL⟩
  have ht3 : t ^ 3 = 1 := by
    rw [← hto]
    exact pow_orderOf_eq_one t
  have ha : (⟨t, htR⟩ : ↥((P : Subgroup X) ⊓ L)) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact ht3
  have hb : orderOf (⟨z, hzR⟩ : ↥((P : Subgroup X) ⊓ L)) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hz.order
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_cyclic ha hb)
  have htz : z ^ k = t := by
    have := congrArg Subtype.val hk
    simpa using this
  have hc' : Commute l z := (hzcomm l hl).symm
  apply hne
  rw [← htz]
  exact (hc'.zpow_right k).eq

end Step0

section Step0

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem normalizer_sup_of_le {P A B : Subgroup X} (hA : P ≤ normalizer (A : Set X))
    (hB : P ≤ normalizer (B : Set X)) : P ≤ normalizer ((A ⊔ B : Subgroup X) : Set X) := by
  intro g hg
  have hA' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hg)
  have hB' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hg)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup, hA', hB']

theorem conj_eq_of_mem_zpowers_central {P : Subgroup X} {z : X} (hzc : ∀ y ∈ P, z * y = y * z) {y : X}
    (hy : y ∈ P) {c : X} (hc : c ∈ zpowers z) : y * c * y⁻¹ = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h : Commute z y := hzc y hy
  rw [mul_inv_eq_iff_eq_mul]
  exact (h.zpow_left k).eq.symm

def commutatorSubgroup {P : Subgroup X} {z : X} (hzc : ∀ y ∈ P, z * y = y * z) (x : X) :
    Subgroup X where
  carrier := {v | v ∈ P ∧ x * v * x⁻¹ * v⁻¹ ∈ zpowers z}
  one_mem' := ⟨P.one_mem, by simp [one_mem]⟩
  mul_mem' := by
    rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
    refine ⟨P.mul_mem haP hbP, ?_⟩
    have hcb := conj_eq_of_mem_zpowers_central hzc haP hb
    have h1 : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [h1, hcb]
    exact mul_mem ha hb
  inv_mem' := by
    rintro a ⟨haP, ha⟩
    refine ⟨P.inv_mem haP, ?_⟩
    have h1 : x * a⁻¹ * x⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ := by group
    rw [h1, conj_eq_of_mem_zpowers_central hzc (P.inv_mem haP) (inv_mem ha)]
    exact inv_mem ha

theorem T29Setup.isCyclic_pCore_of_center_ne_bot (h : T29Setup X L x)
    (hN1 : NoncyclicCentreRank) (hZ : center ↥L ≠ ⊥) : IsCyclic ↥(CFSG.pCore 3 X) := by
  by_contra hnc
  haveI hLn : L.Normal := h.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.ord] at this
  obtain ⟨P, hxP⟩ : ∃ P : Sylow 3 X, x ∈ (P : Subgroup X) := by
    have hp : IsPGroup 3 (zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord]; norm_num)
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, hP (mem_zpowers x)⟩
  obtain ⟨z, hz⟩ := h.exists_omegaCentral hxP
  have hP3 : IsPGroup 3 (P : Subgroup X) := P.isPGroup'
  set O : Subgroup X := CFSG.pCore 3 X with hO
  haveI hOn : O.Normal := CFSG.pCore_normal
  have hOP : O ≤ (P : Subgroup X) := pCore_le_sylow P
  have hOnorm : (P : Subgroup X) ≤ normalizer (O : Set X) := le_normalizer_of_normal
  obtain ⟨U₂, hU₂O, hU₂el, hU₂9, hU₂n⟩ := exists_normal_E9 hP3 hOP hOnorm hnc
  have hRnc := h.not_isCyclic_inf_sylow hZ hz
  have hRnorm : (P : Subgroup X) ≤ normalizer (((P : Subgroup X) ⊓ L : Subgroup X) : Set X) :=
    fun g hg => inf_normalizer_le_normalizer_inf ⟨le_normalizer hg, le_normalizer_of_normal hg⟩
  obtain ⟨U₁, hU₁R, hU₁el, hU₁9, hU₁n⟩ := exists_normal_E9 hP3 inf_le_left hRnorm hRnc
  have hU₁P : U₁ ≤ P := hU₁R.trans inf_le_left
  have hU₁L : U₁ ≤ L := hU₁R.trans inf_le_right
  have hU₂P : U₂ ≤ P := hU₂O.trans hOP
  have hz1 : z ≠ 1 := by
    intro h1
    have := hz.order
    rw [h1, orderOf_one] at this
    omega
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.order] at this
  have hne1 : U₁ ≠ ⊥ := by
    intro h1
    rw [h1, Subgroup.card_bot] at hU₁9
    omega
  have hne2 : U₂ ≠ ⊥ := by
    intro h1
    rw [h1, Subgroup.card_bot] at hU₂9
    omega
  have hzU₁ : z ∈ U₁ := hz.mem_of_normal hP3 hU₁P hU₁n hne1
  have hzU₂ : z ∈ U₂ := hz.mem_of_normal hP3 hU₂P hU₂n hne2
  have hcomm : ∀ l ∈ L, ∀ o ∈ O, l * o = o * l :=
    commute_of_inf_le_center h.comp.2.2 (fun g hgL hgO l hl => h.pCore_inf_commute g hgL hgO l hl)
  have hinf : Nat.card (U₁ ⊓ U₂ : Subgroup X) = 3 := by
    have hge : 3 ≤ Nat.card (U₁ ⊓ U₂ : Subgroup X) := by
      have hle : zpowers z ≤ U₁ ⊓ U₂ := zpowers_le.mpr ⟨hzU₁, hzU₂⟩
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hz.order] at h1
      exact h1
    have hle : Nat.card (U₁ ⊓ U₂ : Subgroup X) ≤ 3 := by
      haveI hcyc : IsCyclic ↥(center ↥L) := h.isCyclic_center hN1
      set ZL : Subgroup X := (center ↥L).map L.subtype with hZL
      haveI : IsCyclic ↥ZL :=
        isCyclic_of_surjective (Subgroup.equivMapOfInjective (center ↥L) L.subtype
          L.subtype_injective).toMonoidHom (Subgroup.equivMapOfInjective (center ↥L)
          L.subtype L.subtype_injective).surjective
      have hWZ : U₁ ⊓ U₂ ≤ ZL := by
        intro g hg
        have hgL : g ∈ L := hU₁L hg.1
        have hgO : g ∈ O := hU₂O hg.2
        refine ⟨⟨g, hgL⟩, Subgroup.mem_center_iff.mpr fun l => ?_, rfl⟩
        have := h.pCore_inf_commute g hgL hgO l l.2
        exact Subtype.ext this
      haveI : IsCyclic ↥(U₁ ⊓ U₂) := isCyclic_of_le hWZ
      refine card_le_three_of_cyclic (W := ↥(U₁ ⊓ U₂)) ?_
      intro w
      have hw : (w : X) ∈ U₁ := w.2.1
      have := hU₁el.2 (w : X) hw
      exact Subtype.ext (by simpa using this)
    omega
  obtain ⟨hVel, hV27⟩ := isElemAbelian_sup_card_27 hU₁el hU₂el hU₁9 hU₂9
    (fun a ha b hb => hcomm a (hU₁L ha) b (hU₂O hb)) hinf
  have hVP : U₁ ⊔ U₂ ≤ P := sup_le hU₁P hU₂P
  have hxV : x ∈ normalizer ((U₁ ⊔ U₂ : Subgroup X) : Set X) :=
    normalizer_sup_of_le hU₁n hU₂n hxP
  have hzV : ∀ v ∈ U₁ ⊔ U₂, z * v = v * z := fun v hv => hz.central v (hVP hv)
  have hK : U₁ ⊔ U₂ ≤ commutatorSubgroup hz.central x := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · exact ⟨hU₁P hu, hz.commutator_mem hP3 hU₁P hU₁el hU₁9 hzU₁ hU₁n x hxP u hu⟩
    · exact ⟨hU₂P hu, hz.commutator_mem hP3 hU₂P hU₂el hU₂9 hzU₂ hU₂n x hxP u hu⟩
  have hcommV : ∀ v ∈ U₁ ⊔ U₂, x * v * x⁻¹ * v⁻¹ ∈ zpowers z := fun v hv => (hK hv).2
  have h3 := three_le_pRank_centralizer_of_unipotent hx3 hz1 hz3 hVel hV27 hzV hxV hcommV
  have h2 := h.cent
  omega

end Step0

section Step0

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem T29Setup.isCyclic_pCore (h : T29Setup X L x) (hN1 : NoncyclicCentreRank) :
    IsCyclic ↥(CFSG.pCore 3 X) := by
  by_cases hZ : center ↥L = ⊥
  · rw [h.pCore_eq_bot hZ]
    infer_instance
  · exact h.isCyclic_pCore_of_center_ne_bot hN1 hZ

theorem T29Setup.le_of_mem_pCore (h : T29Setup X L x) (hN1 : NoncyclicCentreRank) :
    ∀ y ∈ CFSG.pCore 3 X, y ^ 3 = 1 → y ∈ L := by
  intro y hyO hy3
  haveI hLn : L.Normal := h.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hZ : center ↥L = ⊥
  · have h1 := h.pCore_eq_bot hZ
    rw [h1, Subgroup.mem_bot] at hyO
    rw [hyO]
    exact L.one_mem
  · have hcyc : IsCyclic ↥(CFSG.pCore 3 X) := h.isCyclic_pCore hN1
    have hp3 : IsPGroup 3 ↥(center ↥L) := h.center_isPGroup
    have hdvd : 3 ∣ Nat.card ↥(center ↥L) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp3
      have hk0 : k ≠ 0 := by
        rintro rfl
        apply hZ
        exact Subgroup.eq_bot_of_card_eq _ (by simpa using hk)
      rw [hk]
      exact dvd_pow_self 3 hk0
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥L)) 3 hdvd
    set c' : X := (((c : ↥(center ↥L)) : ↥L) : X) with hc'
    have hc'ord : orderOf c' = 3 := by
      rw [hc', Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
    have hc'L : c' ∈ L := ((c : ↥(center ↥L)) : ↥L).2
    haveI hZn : ((center ↥L).map L.subtype).Normal := normal_map_center_subtype L
    have hZp : IsPGroup 3 ↥((center ↥L).map L.subtype) :=
      hp3.of_surjective
        (((center ↥L).equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom)
        (((center ↥L).equivMapOfInjective L.subtype L.subtype_injective).surjective)
    have hZO := normal_pGroup_le_pCore 3 ((center ↥L).map L.subtype) hZn hZp
    have hc'O : c' ∈ CFSG.pCore 3 X := hZO ⟨((c : ↥(center ↥L)) : ↥L), c.2, rfl⟩
    have hmem := mem_zpowers_of_cyclic (W := ↥(CFSG.pCore 3 X)) (a := ⟨y, hyO⟩)
      (b := ⟨c', hc'O⟩) (Subtype.ext (by simpa using hy3))
      (by rw [← Subgroup.orderOf_coe]; exact hc'ord)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hyk : y = c' ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    rw [hyk]
    exact zpow_mem hc'L k

theorem T29Setup.step0 (h : T29Setup X L x) (hN1 : NoncyclicCentreRank) :
    IsCyclic ↥(CFSG.pCore 3 X) ∧ (∀ y ∈ CFSG.pCore 3 X, y ^ 3 = 1 → y ∈ L) ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 :=
  ⟨h.isCyclic_pCore hN1, h.le_of_mem_pCore hN1, h.pRank_top_eq⟩

end Step0

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
