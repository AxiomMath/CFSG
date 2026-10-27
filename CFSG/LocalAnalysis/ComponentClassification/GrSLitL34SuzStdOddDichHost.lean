module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichSetup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddLocal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanConfig
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911E16
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank
public import CFSG.GH74.GLS.Bg.Rank
public import CFSG.GH74.Generic.BProg.B2.Prop31
public import CFSG.GH74.GLS.C3.Layer1.Th2IV26Abs
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CenterData
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroSuzStd

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank
  (card_le_eight_of_isElemAbelian_ON)

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

private theorem odd_card_ker_comp_subtype_pPrimeCore {C : Type} [Group C] [Finite C]
    (K : Subgroup C) :
    Odd (Nat.card ((QuotientGroup.mk' (pPrimeCore 2 C)).comp K.subtype).ker) := by
  have hle : (((QuotientGroup.mk' (pPrimeCore 2 C)).comp K.subtype).ker).map K.subtype ≤
      pPrimeCore 2 C := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff (x : C)).1 hx
  rw [← Subgroup.card_map_of_injective K.subtype_injective]
  exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    (Subgroup.card_dvd_of_le hle)

private theorem pRank_map_pPrimeCore_eq {C : Type} [Group C] [Finite C] (H : Subgroup C) :
    pRank 2 ↥(H.map (QuotientGroup.mk' (pPrimeCore 2 C))) = pRank 2 ↥H := by
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥H →* (C ⧸ pPrimeCore 2 C),
      φ = (QuotientGroup.mk' (pPrimeCore 2 C)).comp H.subtype := ⟨_, rfl⟩
  have hrange : φ.range = H.map (QuotientGroup.mk' (pPrimeCore 2 C)) := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hodd : ¬ 2 ∣ Nat.card φ.ker := by
    rw [hφ]
    exact fun hd => (Nat.not_even_iff_odd.mpr (odd_card_ker_comp_subtype_pPrimeCore H))
      (even_iff_two_dvd.mpr hd)
  rw [← hrange]
  exact (CFSG.GH74.GLS.Bg.pRank_mulEquiv one_lt_two
    (QuotientGroup.quotientKerEquivRange φ)).symm.trans
    (CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two φ.ker hodd)

theorem isQuasisimple_map_pPrimeCore_and_odd_card_center_and_isL34Type {C : Type} [Group C]
    [Finite C] {K : Subgroup C}
    (hq : IsQuasisimple ↥K) (hodd : Odd (Nat.card (center ↥K)))
    (htype : IsL34Type (↥K ⧸ center ↥K)) :
    IsQuasisimple ↥(K.map (QuotientGroup.mk' (pPrimeCore 2 C))) ∧
      Odd (Nat.card (center ↥(K.map (QuotientGroup.mk' (pPrimeCore 2 C))))) ∧
      IsL34Type (↥(K.map (QuotientGroup.mk' (pPrimeCore 2 C))) ⧸
        center ↥(K.map (QuotientGroup.mk' (pPrimeCore 2 C)))) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥K →* (C ⧸ pPrimeCore 2 C),
      θ = (QuotientGroup.mk' (pPrimeCore 2 C)).comp K.subtype := ⟨_, rfl⟩
  have hrange : θ.range = K.map (QuotientGroup.mk' (pPrimeCore 2 C)) := by
    rw [hθ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : θ.ker ≤ center ↥K := by
    rw [hθ]
    exact CFSG.GH74.Generic.BProg.B2.Prop31.normal_le_center_of_odd hq inferInstance
      (odd_card_ker_comp_subtype_pPrimeCore K)
  have hq' : IsQuasisimple ↥θ.range := by
    rw [hrange]
    exact CFSG.GH74.GLS.Th2.IV26.isQuasisimple_map_of_isQuasisimple (C := C) hq
  have hodd' : Odd (Nat.card (center ↥θ.range)) := by
    have hc : center ↥θ.range = (center ↥K).map θ.rangeRestrict :=
      CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hq θ.rangeRestrict_surjective
        (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
    rw [hc]
    exact Odd.of_dvd_nat hodd (Subgroup.card_map_dvd _ _)
  have htype' : IsL34Type (↥θ.range ⧸ center ↥θ.range) := by
    obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsL4U4.OutInv.nonempty_quotient_center_equiv'
      hq' θ.rangeRestrict θ.rangeRestrict_surjective (⊥ : Subgroup ↥K)
      (by rw [Subgroup.map_bot, Subgroup.card_bot]; exact ⟨0, by norm_num⟩)
      QuotientGroup.quotientBot hq
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm htype
  refine ⟨?_, ?_, ?_⟩
  · rwa [← hrange]
  · rwa [hrange] at hodd'
  · rwa [hrange] at htype'

private theorem exists_pComponent_lift_of_component {u : G}
    {L : Subgroup (↥(centralizer ({u} : Set G)) ⧸
      pPrimeCore 2 ↥(centralizer ({u} : Set G)))}
    (hL : IsComponent L) :
    ∃ M : Subgroup G, M ≤ centralizer ({u} : Set G) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set G))) ∧
      (M.subgroupOf (centralizer ({u} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G)))) = L ∧
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* ↥L ⧸ center ↥L) := by
  obtain ⟨M₀, hM₀, hM₀L⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Thm1.exists_pComponent_of_quotient_component hL
  have hMu : M₀.map (centralizer ({u} : Set G)).subtype ≤ centralizer ({u} : Set G) :=
    Subgroup.map_subtype_le M₀
  have hMsub : (M₀.map (centralizer ({u} : Set G)).subtype).subgroupOf
      (centralizer ({u} : Set G)) = M₀ :=
    Subgroup.comap_map_eq_self_of_injective (centralizer ({u} : Set G)).subtype_injective M₀
  have hM : IsPComponent 2 ((M₀.map (centralizer ({u} : Set G)).subtype).subgroupOf
      (centralizer ({u} : Set G))) := by
    rw [hMsub]
    exact hM₀
  have hML : ((M₀.map (centralizer ({u} : Set G)).subtype).subgroupOf
      (centralizer ({u} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G)))) = L := by
    rw [hMsub, hM₀L]
  obtain ⟨e⟩ := nonempty_image_center_quotient_equiv hMu hM
  exact ⟨M₀.map (centralizer ({u} : Set G)).subtype, hMu, hM, hML, ⟨hML ▸ e.symm⟩⟩

section ONan


theorem false_of_le_onan_of_l34_odd {X : Type} [Group X] [Finite X] (hO : pPrimeCore 2 X = ⊥)
    {L D : Subgroup X} (hL : IsComponent L)
    (hLON : Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .ONan) (hDL : D ≤ L)
    (_hD : IsQuasisimple ↥D) (hDodd : Odd (Nat.card (center ↥D)))
    (hDtype : IsL34Type (↥D ⧸ center ↥D)) : False := by
  obtain ⟨Eb, hEb, hEb16⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.exists_elemAb16_of_lieModel hDtype
  obtain ⟨V, hV, hV16⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.exists_lift_elemAb16 (Subgroup.center ↥D) hDodd hEb hEb16
  have hVinst : IsElementaryAbelian 2 V := hV
  let W : Subgroup ↥L := V.map (Subgroup.inclusion hDL)
  have hW : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hWcard : Nat.card W = 16 := by
    dsimp only [W]
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hDL), hV16]
  have hZ : center ↥L = ⊥ := center_eq_bot_of_isComponent_on hO hL hLON
  have hmk_inj : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥L)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hZ
  let Wq : Subgroup (↥L ⧸ center ↥L) := W.map (QuotientGroup.mk' (Subgroup.center ↥L))
  have hWq : IsElementaryAbelian 2 Wq := IsElementaryAbelian.map _
  have hWqcard : Nat.card Wq = 16 := by
    dsimp only [Wq]
    rw [Subgroup.card_map_of_injective hmk_inj, hWcard]
  obtain ⟨e⟩ := hLON
  let E : Subgroup (Blueprint.NativeSporadic.Carrier .ONan) := Wq.map e.toMonoidHom
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEcard : Nat.card E = 16 := by
    dsimp only [E]
    rw [Subgroup.card_map_of_injective e.injective, hWqcard]
  have hle := card_le_eight_of_isElemAbelian_ON
    E (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hE)
  have hle' : Nat.card ↥E ≤ 8 := hle
  have hcard' : Nat.card ↥E = 16 := hEcard
  omega

end ONan

section Solomon


theorem false_of_isPComponent_field_of_l34Base
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hC5 : L3TwoPowProperFixedCatalog) (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple) (hCField : L34FieldCoreStepMirror)
    (hSField : L34FieldStandardExclusion) (hG : L34BaseSetting G) {b : G} (hb : orderOf b = 2)
    {M : Subgroup G} (hMb : M ≤ centralizer ({b} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G)))) {n : ℕ} (hn : 4 ≤ n)
    (hne : Even n) (hML : Blueprint.LieModel (↥M ⧸ Open.fusionZStar ↥M) .PSL 3 2 n) : False := by
  obtain ⟨hsimple, hna, hK, -, -, -, -, -⟩ := id hG
  have := hsimple
  obtain ⟨hsF, hnF, hoF⟩ := GrS5.fstar_facts hG
  obtain ⟨J, -, hJmm, hJw, hJsol, m, hm, hmev, hJL⟩ :=
    exists_field_mirror_solomon_top hSch hna hsF hnF hK hC5 hb ⟨hMb, hM⟩ hn hne hML
  have hJtype : SuzONanFieldType (J ⧸ Open.fusionZStar J) := Or.inr (Or.inr ⟨m, hm, hmev, hJL⟩)
  have hJrank : 3 ≤ pRank 2 ↥J := three_le_pRank_of_lieModel_fusionZStar (by omega) hJL
  obtain ⟨c, hc, hJc, hJcp⟩ := hJw.1
  have hT9 := fun (t : G) (ht : orderOf t = 2) (hJt : J ≤ centralizer ({t} : Set G)) =>
    Sol76.maximalTwoComponentSimple_at_of_solomonMaximal hCI hGA hsF hnF hoF h13 hK hJw
      (by omega) (not_psp4_of_suzONanFieldType hJtype) hJsol ht hJt
  have hZ : ∀ g : G, g ≠ 1 → g ∉ center G := fun g hg hgZ =>
    hg (by rwa [CatLeaf.center_eq_bot_of_simple hna, mem_bot] at hgZ)
  obtain ⟨hst, hO⟩ := GrS5.isStandardSubgroup_of_cor211 hSch hK hZ hc hJc hJcp
    (fun t ht hJt => (hT9 t ht hJt).1) ((hT9 c hc hJc).2 hJrank)
    (hCField G hG J hJmm ⟨m, hm, hmev, hJL⟩)
  exact hSField G hG c J hc hJc hJcp ⟨m, hm, hmev, hJL⟩ hst hO

section SuzHost


theorem false_of_isPComponent_suz_of_mem_commutator
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple) (hCSuz : L34SuzCoreStepMirror)
    (hEven : L34SuzEvenStandardExclusion) (hAS : RankTwoSporadic.SporadicCaseOdd .Suz)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (h25 : EvenSporadicStandard.Finkelstein77.Asc76Lemma25) (hG : L34BaseSetting G)
    {u : G} (hu : orderOf u = 2)
    (hcomm : u ∈ ⁅centralizer ({u} : Set G), centralizer ({u} : Set G)⁆) {M : Subgroup G}
    (hMu : M ≤ centralizer ({u} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set G))))
    (hMs : Blueprint.NativeSporadic.IsSporadic (↥M ⧸ Open.fusionZStar ↥M) .Suz)
    (hMr : 3 ≤ pRank 2 ↥M) : False := by
  exact not_mem_commutator_centralizer_of_l34SuzOdd
    (l34SuzOddSetting_of_isPComponent_suz hSch hC4 hCI hGA h13 hCSuz hEven hAS hCIT h25 hG
      hu hMu hM hMs hMr)
    hcomm

section Host


theorem false_of_host_of_l34SuzOdd
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hC5 : L3TwoPowProperFixedCatalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple) (hCSuz : L34SuzCoreStepMirror)
    (hCField : L34FieldCoreStepMirror) (hSField : L34FieldStandardExclusion)
    (hEven : L34SuzEvenStandardExclusion) (hAS : RankTwoSporadic.SporadicCaseOdd .Suz)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (h25 : EvenSporadicStandard.Finkelstein77.Asc76Lemma25)
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    {L : Subgroup (↥(centralizer ({u} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({u} : Set G)))}
    (hL : IsComponent L) (hKL : (K.subgroupOf (centralizer ({u} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G)))) ≤ L)
    (htype : Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .Suz ∨
      Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .ONan ∨
      Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 4) : False := by
  have hG : L34BaseSetting G := hS.base
  have hu2 : orderOf u = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hD.mul_self u hu) hu1
  obtain ⟨M, hMu, hM, hML, ⟨e⟩⟩ := exists_pComponent_lift_of_component hL
  obtain ⟨hKbq, hKbodd, hKbtype⟩ :=
    isQuasisimple_map_pPrimeCore_and_odd_card_center_and_isL34Type
      (C := ↥(centralizer ({u} : Set G)))
      (K := K.subgroupOf (centralizer ({u} : Set G)))
      (isQuasisimple_subgroupOf_of_l34SuzOdd hD hu)
      (odd_card_center_subgroupOf_of_l34SuzOdd hS hD hu)
      (isL34Type_subgroupOf_of_l34SuzOdd hD hu)
  rcases htype with hSuz | hON | hF
  ·
    obtain ⟨f⟩ := hSuz
    have hMs : Blueprint.NativeSporadic.IsSporadic (↥M ⧸ Open.fusionZStar ↥M) .Suz :=
      ⟨e.trans f⟩
    have h3K : 3 ≤ pRank 2 ↥((K.subgroupOf (centralizer ({u} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G))))) :=
      EvenSporadicStandard.Induction.three_le_pRank_of_cover_L3 (n := 2) le_rfl hKbtype
        (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    have h3L : 3 ≤ pRank 2 ↥L :=
      le_trans h3K (CFSG.GH74.GLS.Bg.pRank_subgroup_mono one_lt_two hKL)
    have h3M : 3 ≤ pRank 2 ↥M := by
      have h1 : pRank 2 ↥((M.subgroupOf (centralizer ({u} : Set G))).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G))))) =
          pRank 2 ↥(M.subgroupOf (centralizer ({u} : Set G))) :=
        pRank_map_pPrimeCore_eq _
      have h2 : pRank 2 ↥(M.subgroupOf (centralizer ({u} : Set G))) = pRank 2 ↥M :=
        CFSG.GH74.GLS.Bg.pRank_mulEquiv one_lt_two (Subgroup.subgroupOfEquivOfLe hMu)
      rw [← h2, ← h1, hML]
      exact h3L
    exact false_of_isPComponent_suz_of_mem_commutator hSch hC4 hCI hGA h13 hCSuz hEven hAS hCIT h25
      hG hu2 (mem_commutator_centralizer_of_l34SuzOdd hS hD hu hu1) hMu hM hMs h3M
  ·
    exact false_of_le_onan_of_l34_odd
      (X := ↥(centralizer ({u} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({u} : Set G)))
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hL hON hKL hKbq hKbodd hKbtype
  ·
    exact false_of_isPComponent_field_of_l34Base hSch hC5 hCI hGA h13 hCField hSField hG hu2 hMu hM
      (n := 4) le_rfl ⟨2, by norm_num⟩
      (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hF)

end Host

end SuzHost

end Solomon

end CFSG.ComponentClassification.GrSLit.L34Sec5S
