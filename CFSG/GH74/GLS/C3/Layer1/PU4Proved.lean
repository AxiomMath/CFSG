module

public import CFSG.GH74.GLS.C3.Layer1.EvenStd
public import CFSG.LocalAnalysis.ComponentInitial.BlockAschbacherTheorem5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
import CFSG.GH74.E2.TermBasic
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.LocalAnalysis.StandardType.GGCentralQuotientEq
import CFSG.GH74.Generic.BProg.B1.Stage3aSD2
import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitBasic
public import CFSG.LocalAnalysis.OddStandard.Children
import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG

theorem isQuasisimple_of_isCompIn {G : Type} [Group G] {H K : Subgroup G} (h : IsCompIn H K) :
    CFSG.IsQuasisimple ↥K :=
  (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (Subgroup.subgroupOfEquivOfLe h.1).symm).2 h.2.1

theorem isStandardSubgroup_of_componentType {Y : Type*} [Group Y] {J : Subgroup Y}
    (h : CFSG.Assembly.ComponentType.IsStandardSubgroup J) : CFSG.IsStandardSubgroup J :=
  CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_assembly.2 h

theorem center_eq_pPrimeCore_of_alternating_quotient
    {L : Type*} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    {n : ℕ} (hn : 5 ≤ n)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n)) :
    Subgroup.center L = pPrimeCore 2 L := by
  have hcard : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup hcard
  exact CFSG.ComponentClassification.GSThmB.X10Rec.center_eq_pPrimeCore hq e.isSimpleGroup


theorem two_le_pRank_of_alternating {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ CFSG.pRank 2 (alternatingGroup (Fin n)) := by
  classical
  let D : Finset (Fin n) :=
    Finset.univ.image (fun i : Fin 4 => (⟨i.val, by omega⟩ : Fin n))
  have hDcard : D.card = 4 := by
    have hinj : Function.Injective (fun i : Fin 4 => (⟨i.val, by omega⟩ : Fin n)) := by
      intro i j h
      exact Fin.ext (by simpa using congrArg Fin.val h)
    dsimp only [D]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  let f : alternatingGroup D →* alternatingGroup (Fin n) :=
    alternatingGroup.ofSubtype D
  let E : Subgroup (alternatingGroup (Fin n)) :=
    (alternatingGroup.kleinFour D).map f
  have hK4 : IsKleinFour ↥(alternatingGroup.kleinFour D) :=
    alternatingGroup.kleinFour_isKleinFour (by simpa using hDcard)
  let eE : ↥(alternatingGroup.kleinFour D) ≃* ↥E :=
    Subgroup.equivMapOfInjective _ f alternatingGroup.ofSubtype_injective
  have hcardE : Nat.card ↥E = 4 := by
    rw [← Nat.card_congr eE.toEquiv, hK4.card_four]
  have hexpE : Monoid.exponent ↥E = 2 := by
    rw [← Monoid.exponent_eq_of_mulEquiv eE, hK4.exponent_two]
  have hK4E : IsKleinFour ↥E := ⟨hcardE, hexpE⟩
  have hcomm : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u := by
    intro u hu v hv
    exact congrArg Subtype.val
      ((@IsKleinFour.isMulCommutative ↥E _ hK4E).is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hsq : ∀ u ∈ E, u * u = 1 := by
    intro u hu
    have h := Monoid.pow_exponent_eq_one (⟨u, hu⟩ : ↥E)
    rw [hK4E.exponent_two] at h
    simpa [pow_two] using congrArg Subtype.val h
  have hEel : CFSG.IsElementaryAbelian 2 ↥E :=
    CFSG.GH74.GLS.C3.Layer1.Back.isElementaryAbelian_of_forall hcomm hsq
  exact CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian (p := 2) (by norm_num)
    hEel (k := 2) (by rw [hcardE]; norm_num)

theorem two_le_pRank_of_alternating_quotient
    {L : Type*} [Group L] [Finite L] {n : ℕ} (hn : 4 ≤ n)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n)) :
    2 ≤ CFSG.pRank 2 L := by
  have hbar : 2 ≤ CFSG.pRank 2 (L ⧸ pPrimeCore 2 L) := by
    rw [CFSG.pRank_congr_of_mulEquiv e 2]
    exact two_le_pRank_of_alternating hn
  have hOnotdvd : ¬ 2 ∣ Nat.card (pPrimeCore 2 L) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := L))
  have hquot := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd
    (p := 2) Nat.prime_two (pPrimeCore 2 L) hOnotdvd
  exact hquot ▸ hbar

theorem two_le_pRank_of_kBar_smallAlt
    {L : Type} [Group L] [Finite L] {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7)
    (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n)) :
    2 ≤ CFSG.pRank 2 L := by
  have hn4 : 4 ≤ n := by
    rcases hn with rfl | rfl | rfl <;> norm_num
  exact two_le_pRank_of_alternating_quotient hn4 e

theorem assembly_isQuasisimple_of_universal_even
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hU : CFSG.LocalAnalysis.ComponentInitial.IsUniversalComponent K)
    (hCeven : Even (Nat.card (Subgroup.centralizer (K : Set G)))) :
    CFSG.Assembly.IsQuasisimple K := by
  obtain ⟨t, ht2⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer (K : Set G)) 2 hCeven.two_dvd
  have htK : (t : G) ∈ Subgroup.centralizer (K : Set G) := t.2
  have ht2' : orderOf (t : G) = 2 := by
    simpa [Subgroup.orderOf_mk] using ht2
  exact (hU (t : G) htK ht2').2.2

theorem b_cor_PU4_proved :
    B_cor_PU4 := by
  intro G _ _ hG x K hx hcomp hrank hterm
  have : IsSimpleGroup G := hG.1
  have hKC : K ≤ centralizer ({x} : Set G) := hcomp.1
  have hq : CFSG.Assembly.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (isQuasisimple_of_isCompIn hterm.2.1)
  have hrk : 2 ≤ CFSG.Assembly.pRank 2 K := by
    have h1 : CFSG.pRank 2 ↥K = CFSG.Open.pRank 2 K :=
      (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥K).trans
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
    have h2 : 2 ≤ CFSG.Open.pRank 2 K := h1 ▸ hrank
    exact h2
  have hxC : x ∈ centralizer (K : Set G) := by
    rw [mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.1 (hKC hk)
  have hCeven : Even (Nat.card (centralizer (K : Set G))) := by
    have h2 : 2 ∣ Nat.card (centralizer (K : Set G)) := by
      have h3 := orderOf_dvd_natCard (⟨x, hxC⟩ : centralizer (K : Set G))
      have e : orderOf (⟨x, hxC⟩ : centralizer (K : Set G)) = 2 := by
        rw [← hx]
        exact Subgroup.orderOf_mk _ _
      rwa [e] at h3
    exact even_iff_two_dvd.2 h2
  have hU : CFSG.LocalAnalysis.ComponentInitial.IsUniversalComponent K := by
    intro t ht ht2
    have hKt : K ≤ centralizer ({t} : Set G) := by
      intro k hk
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.1 ht) k hk
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKt).2
      (hterm.2.2.2 t ht2 ht).2
  exact isStandardSubgroup_of_componentType
    (CFSG.LocalAnalysis.ComponentInitial.universal_rank_two_component_isStandardSubgroup
      hG.2.1 hq hrk hCeven hU)

theorem card_alternatingGroup_fin_le {m n : ℕ} (hm : 5 ≤ m) (hmn : m ≤ n) :
    Nat.card (alternatingGroup (Fin m)) ≤ Nat.card (alternatingGroup (Fin n)) := by
  have hm2 : 2 ≤ m := le_trans (by norm_num) hm
  have hn2 : 2 ≤ n := le_trans hm2 hmn
  have hmN : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm2
  have hnN : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
  rw [@nat_card_alternatingGroup (Fin m) _ _ hmN,
    @nat_card_alternatingGroup (Fin n) _ _ hnN, Nat.card_fin, Nat.card_fin]
  exact Nat.div_le_div_right (Nat.factorial_le hmn)

theorem eq_of_le_of_kBar_bounded
    {G : Type} [Group G] [Finite G] {K L : Subgroup G} {n m : ℕ}
    (hle : K ≤ L) (hm : 5 ≤ m) (hmn : m ≤ n)
    (eK : CFSG.GH74.GLS.kBar K ≃* alternatingGroup (Fin n))
    (eL : CFSG.GH74.GLS.kBar L ≃* alternatingGroup (Fin m))
    (hqL : CFSG.IsQuasisimple ↥L) :
    K = L := by
  have hn5 : 5 ≤ n := le_trans hm hmn
  have hn4 : 4 ≤ n := le_trans (by norm_num) hn5
  have hcenterA : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (α := Fin n) (by simpa using hn4)
  have hcenterK : Subgroup.center (CFSG.GH74.GLS.kBar K) = ⊥ := by
    have hmap : Subgroup.map (eK : CFSG.GH74.GLS.kBar K →* alternatingGroup (Fin n))
      (Subgroup.center (CFSG.GH74.GLS.kBar K)) = ⊥ := by
      rw [Subgroup.map_center_eq eK, hcenterA]
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := Subgroup.center (CFSG.GH74.GLS.kBar K)) eK.injective).mp hmap
  have hZK : Subgroup.center ↥K ≤ CFSG.pPrimeCore 2 ↥K := by
    have h := MonoidHom.center_le_ker
      (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥K))
      (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 2 ↥K)) hcenterK
    simpa only [QuotientGroup.ker_mk'] using h
  have hcardK : Nat.card (CFSG.GH74.GLS.kBar K) ≤
      Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    have h := Subgroup.index_antitone
      (H := Subgroup.center ↥K) (K := CFSG.pPrimeCore 2 ↥K) hZK
    simpa only [Subgroup.index_eq_card] using h
  have hZL : Subgroup.center ↥L = CFSG.pPrimeCore 2 ↥L :=
    CFSG.GH74.GLS.center_eq_pPrimeCore_of_alternating_quotient (L := ↥L) hqL hm eL
  have hcardL : Nat.card (↥L ⧸ Subgroup.center ↥L) =
      Nat.card (alternatingGroup (Fin m)) := by
    rw [hZL]
    exact Nat.card_congr eL.toEquiv
  have hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) ≤
      Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    calc
      Nat.card (↥L ⧸ Subgroup.center ↥L) = Nat.card (alternatingGroup (Fin m)) := hcardL
      _ ≤ Nat.card (alternatingGroup (Fin n)) := card_alternatingGroup_fin_le hm hmn
      _ = Nat.card (CFSG.GH74.GLS.kBar K) := (Nat.card_congr eK.toEquiv).symm
      _ ≤ Nat.card (↥K ⧸ Subgroup.center ↥K) := hcardK
  have hperfL : commutator ↥L = ⊤ := Group.isPerfect_def.mp hqL.1
  exact CFSG.StandardType.eq_of_le_of_card_centralQuotient_le hle hperfL hcard

theorem isUniversalComponent_of_varying_ordinary_bounded
    {G : Type} [Group G] [Finite G]
    {K R : Subgroup G} {n : ℕ}
    (eK : CFSG.GH74.GLS.kBar K ≃* alternatingGroup (Fin n))
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (Subgroup.centralizer (K : Set G)))
    (hfamily : ∀ s ∈ R, orderOf s = 2 →
      ∃ (L : Subgroup G) (m : ℕ), K ≤ L ∧
        CFSG.GH74.GLS.IsCompIn (Subgroup.centralizer ({s} : Set G)) L ∧
        5 ≤ m ∧ m ≤ n ∧
        Nonempty (CFSG.GH74.GLS.kBar L ≃* alternatingGroup (Fin m))) :
    CFSG.LocalAnalysis.ComponentInitial.IsUniversalComponent K := by
  refine CFSG.GH74.Generic.BProg.B1.isUniversalComponent_of_sylow hR ?_
  intro s hsR hs2
  obtain ⟨L, m, hKL, hLcomp, hm, hmn, ⟨eL⟩⟩ := hfamily s hsR hs2
  have hqL : CFSG.IsQuasisimple ↥L :=
    CFSG.GH74.GLS.isQuasisimple_of_isCompIn hLcomp
  have hEq : K = L := eq_of_le_of_kBar_bounded hKL hm hmn eK eL hqL
  subst hEq
  exact hLcomp

theorem isAltTwoComponent_of_isCompIn
    {G : Type} [Group G] [Finite G] {s : G} {L : Subgroup G} {m : ℕ}
    (hs2 : orderOf s = 2)
    (hLcomp : CFSG.GH74.GLS.IsCompIn (Subgroup.centralizer ({s} : Set G)) L)
    (eL : CFSG.GH74.GLS.kBar L ≃* alternatingGroup (Fin m)) :
    CFSG.ComponentClassification.SolAltLit.IsAltTwoComponent s L m :=
  ⟨hs2, hLcomp.1,
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hLcomp.2,
    ⟨eL⟩⟩

theorem even_card_centralizer_of_isAltTwoComponent
    {G : Type} [Group G] [Finite G] {t : G} {K : Subgroup G} {n : ℕ}
    (h : CFSG.ComponentClassification.SolAltLit.IsAltTwoComponent t K n) :
    Even (Nat.card (Subgroup.centralizer (K : Set G))) := by
  have htC : t ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.1 (h.2.1 hk)
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer (K : Set G)) := by
    have h3 := orderOf_dvd_natCard (⟨t, htC⟩ : Subgroup.centralizer (K : Set G))
    have e : orderOf (⟨t, htC⟩ : Subgroup.centralizer (K : Set G)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact h.1
    rwa [e] at h3
  exact even_iff_two_dvd.2 h2

theorem isUniversalComponent_of_allComponentMax
    {G : Type} [Group G] [Finite G]
    {t0 : G} {K0 R : Subgroup G} {n0 : ℕ}
    (hK0 : CFSG.ComponentClassification.SolAltLit.IsAltTwoComponent t0 K0 n0)
    (hmax : ∀ (t' : G) (K' : Subgroup G) (n' : ℕ),
      CFSG.ComponentClassification.SolAltLit.IsAltTwoComponent t' K' n' → n' ≤ n0)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (Subgroup.centralizer (K0 : Set G)))
    (hfamily : ∀ s ∈ R, orderOf s = 2 →
      ∃ (L : Subgroup G) (m : ℕ), K0 ≤ L ∧
        CFSG.GH74.GLS.IsCompIn (Subgroup.centralizer ({s} : Set G)) L ∧
        5 ≤ m ∧
        Nonempty (CFSG.GH74.GLS.kBar L ≃* alternatingGroup (Fin m))) :
    CFSG.LocalAnalysis.ComponentInitial.IsUniversalComponent K0 := by
  obtain ⟨eK0⟩ := hK0.2.2.2
  refine isUniversalComponent_of_varying_ordinary_bounded eK0 hR ?_
  intro s hsR hs2
  obtain ⟨L, m, hKL, hLcomp, hm5, ⟨eL⟩⟩ := hfamily s hsR hs2
  have hIsAlt : CFSG.ComponentClassification.SolAltLit.IsAltTwoComponent s L m :=
    isAltTwoComponent_of_isCompIn hs2 hLcomp eL
  exact ⟨L, m, hKL, hLcomp, hm5, hmax s L m hIsAlt, ⟨eL⟩⟩


section CertificatesPU4


theorem standardSetting_of_terminal_of_two_le_pRank
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {x : G} {K : Subgroup G}
    (hterm : CFSG.GH74.GLS.IsTerminalPair 2 x K)
    (hrank : 2 ≤ CFSG.pRank 2 ↥K) :
    CFSG.OddStandard.StandardSetting G K := by
  have hcomp : CFSG.GH74.GLS.IsPCompIn 2 (Subgroup.centralizer ({x} : Set G)) K :=
    ⟨hterm.2.1.1, CFSG.GH74.E2.isPComponent_two_of_component hterm.2.1.2⟩
  have hKproperSimple : CFSG.GH74.GLS.IsKProperSimple G :=
    ⟨inferInstance, hnab, hKproper⟩
  have hstdNative : CFSG.IsStandardSubgroup K :=
    CFSG.GH74.GLS.b_cor_PU4_proved G hKproperSimple x K hterm.1 hcomp hrank hterm
  have hstd : CFSG.Open.standardComponentIsStandard K :=
    CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_standardComponentIsStandard.1 hstdNative
  exact ⟨inferInstance, hnab, hKproper, hstd⟩

theorem standardSetting_and_rankTwoQuot_of_terminal_smallAlt
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {x : G} {K : Subgroup G}
    (hterm : CFSG.GH74.GLS.IsTerminalPair 2 x K)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7)
    (hAn : Nonempty (CFSG.GH74.GLS.kBar K ≃* alternatingGroup (Fin n))) :
    CFSG.OddStandard.StandardSetting G K ∧
      Nonempty (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot K ≃*
        alternatingGroup (Fin n)) := by
  classical
  obtain ⟨e⟩ := hAn
  have hn5 : 5 ≤ n := by
    rcases hn with rfl | rfl | rfl <;> norm_num
  have hOZ : Subgroup.center ↥K = pPrimeCore 2 ↥K :=
    center_eq_pPrimeCore_of_alternating_quotient (L := ↥K)
      (CFSG.GH74.GLS.isQuasisimple_of_isCompIn hterm.2.1) hn5 e
  have hqbar : Nonempty (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot K ≃*
      alternatingGroup (Fin n)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hOZ).trans e⟩
  have hrankK : 2 ≤ CFSG.pRank 2 ↥K :=
    two_le_pRank_of_kBar_smallAlt hn e
  exact ⟨standardSetting_of_terminal_of_two_le_pRank hnab hKproper hterm hrankK, hqbar⟩

theorem standardSetting_and_rankTwoQuot_of_universal_alternating
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {K : Subgroup G}
    (hU : CFSG.LocalAnalysis.ComponentInitial.IsUniversalComponent K)
    (hCeven : Even (Nat.card (Subgroup.centralizer (K : Set G))))
    {n : ℕ} (hn : 5 ≤ n)
    (hAn : Nonempty (CFSG.GH74.GLS.kBar K ≃* alternatingGroup (Fin n))) :
    CFSG.OddStandard.StandardSetting G K ∧
      Nonempty (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot K ≃*
        alternatingGroup (Fin n)) := by
  obtain ⟨e⟩ := hAn
  have hq : CFSG.Assembly.IsQuasisimple K :=
    assembly_isQuasisimple_of_universal_even hU hCeven
  have hrankGroup : 2 ≤ CFSG.pRank 2 ↥K :=
    two_le_pRank_of_alternating_quotient (n := n) (by omega) e
  have hrankTop : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥K) := by
    simpa only [CFSG.SectionRank.pRank_eq_open_pRank_top] using hrankGroup
  have hrankSub : CFSG.Open.pRank 2 (⊤ : Subgroup ↥K) = CFSG.Open.pRank 2 K :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
  have hrank : 2 ≤ CFSG.Assembly.pRank 2 K := by
    rw [hrankSub] at hrankTop
    exact hrankTop
  have hstdNative : CFSG.Assembly.ComponentType.IsStandardSubgroup K :=
    CFSG.LocalAnalysis.ComponentInitial.universal_rank_two_component_isStandardSubgroup
      hnab hq hrank hCeven hU
  have hstd : CFSG.Open.standardComponentIsStandard K :=
    CFSG.StandardSubgroupAPI.standardComponentIsStandard_iff_assembly.2 hstdNative
  have hS : CFSG.OddStandard.StandardSetting G K :=
    ⟨inferInstance, hnab, hKproper, hstd⟩
  have hqNative : CFSG.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).1 hq
  have hcenter : Subgroup.center ↥K = pPrimeCore 2 ↥K :=
    CFSG.GH74.GLS.center_eq_pPrimeCore_of_alternating_quotient (L := ↥K) hqNative hn e
  have hqbar : Nonempty (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot K ≃*
      alternatingGroup (Fin n)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans e⟩
  exact ⟨hS, hqbar⟩

theorem standardSetting_and_rankTwoQuot_of_varying_ordinary_bounded
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {K R : Subgroup G}
    (hCeven : Even (Nat.card (Subgroup.centralizer (K : Set G))))
    {n : ℕ} (hn : 5 ≤ n)
    (eK : CFSG.GH74.GLS.kBar K ≃* alternatingGroup (Fin n))
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (Subgroup.centralizer (K : Set G)))
    (hfamily : ∀ s ∈ R, orderOf s = 2 →
      ∃ (L : Subgroup G) (m : ℕ), K ≤ L ∧
        CFSG.GH74.GLS.IsCompIn (Subgroup.centralizer ({s} : Set G)) L ∧
        5 ≤ m ∧ m ≤ n ∧
        Nonempty (CFSG.GH74.GLS.kBar L ≃* alternatingGroup (Fin m))) :
    CFSG.OddStandard.StandardSetting G K ∧
      Nonempty (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot K ≃*
        alternatingGroup (Fin n)) := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.IsUniversalComponent K :=
    isUniversalComponent_of_varying_ordinary_bounded eK hR hfamily
  exact standardSetting_and_rankTwoQuot_of_universal_alternating
    hnab hKproper hU hCeven hn ⟨eK⟩

theorem exists_standardSetting_and_rankTwoQuot_of_allComponentMax
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hseed : ∃ (t : G) (K : Subgroup G) (n : ℕ),
      CFSG.ComponentClassification.SolAltLit.IsAltTwoComponent t K n ∧ 8 ≤ n)
    (hfamily : ∀ (t0 : G) (K0 : Subgroup G) (n0 : ℕ),
      CFSG.ComponentClassification.SolAltLit.IsAltTwoComponent t0 K0 n0 → 8 ≤ n0 →
      (∀ (t' : G) (K' : Subgroup G) (n' : ℕ),
        CFSG.ComponentClassification.SolAltLit.IsAltTwoComponent t' K' n' → n' ≤ n0) →
      ∃ R : Subgroup G,
        CFSG.ABGLocalTools.IsSylowOf 2 R (Subgroup.centralizer (K0 : Set G)) ∧
        ∀ s ∈ R, orderOf s = 2 →
          ∃ (L : Subgroup G) (m : ℕ), K0 ≤ L ∧
            CFSG.GH74.GLS.IsCompIn (Subgroup.centralizer ({s} : Set G)) L ∧
            5 ≤ m ∧
            Nonempty (CFSG.GH74.GLS.kBar L ≃* alternatingGroup (Fin m))) :
    ∃ (t0 : G) (K0 : Subgroup G) (n0 : ℕ),
      CFSG.ComponentClassification.SolAltLit.IsAltTwoComponent t0 K0 n0 ∧ 8 ≤ n0 ∧
      CFSG.OddStandard.StandardSetting G K0 ∧
      Nonempty (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot K0 ≃*
        alternatingGroup (Fin n0)) := by
  obtain ⟨t0, K0, n0, hK0, h8, hmax⟩ :=
    CFSG.ComponentClassification.SolAltLit.exists_isAltTwoComponent_max hseed
  obtain ⟨R, hR, hfam⟩ := hfamily t0 K0 n0 hK0 h8 hmax
  have hn05 : 5 ≤ n0 := le_trans (by norm_num) h8
  obtain ⟨eK0⟩ := hK0.2.2.2
  have hEven := even_card_centralizer_of_isAltTwoComponent hK0
  have hfamBounded : ∀ s ∈ R, orderOf s = 2 →
      ∃ (L : Subgroup G) (m : ℕ), K0 ≤ L ∧
        CFSG.GH74.GLS.IsCompIn (Subgroup.centralizer ({s} : Set G)) L ∧
        5 ≤ m ∧ m ≤ n0 ∧
        Nonempty (CFSG.GH74.GLS.kBar L ≃* alternatingGroup (Fin m)) := by
    intro s hsR hs2
    obtain ⟨L, m, hKL, hLcomp, hm5, ⟨eL⟩⟩ := hfam s hsR hs2
    have hIsAlt : CFSG.ComponentClassification.SolAltLit.IsAltTwoComponent s L m :=
      isAltTwoComponent_of_isCompIn hs2 hLcomp eL
    exact ⟨L, m, hKL, hLcomp, hm5, hmax s L m hIsAlt, ⟨eL⟩⟩
  have hS := standardSetting_and_rankTwoQuot_of_varying_ordinary_bounded
    hnab hKproper hEven hn05 eK0 hR hfamBounded
  exact ⟨t0, K0, n0, hK0, h8, hS.1, hS.2⟩

theorem standardSetting_and_rankTwoQuot_of_universal_smallAlt
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a)
    (hKproper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {K : Subgroup G}
    (hU : CFSG.LocalAnalysis.ComponentInitial.IsUniversalComponent K)
    (hCeven : Even (Nat.card (Subgroup.centralizer (K : Set G))))
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7)
    (hAn : Nonempty (CFSG.GH74.GLS.kBar K ≃* alternatingGroup (Fin n))) :
    CFSG.OddStandard.StandardSetting G K ∧
      Nonempty (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot K ≃*
        alternatingGroup (Fin n)) := by
  have hn5 : 5 ≤ n := by
    rcases hn with rfl | rfl | rfl <;> norm_num
  exact standardSetting_and_rankTwoQuot_of_universal_alternating
    hnab hKproper hU hCeven hn5 hAn

end CertificatesPU4

end CFSG.GH74.GLS
