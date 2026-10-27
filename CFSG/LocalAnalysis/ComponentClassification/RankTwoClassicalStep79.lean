module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalHJ
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalStep76
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalStep75
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G]

@[expose] def E76 (Y L : Subgroup G) : Subgroup G :=
  (normalClosure ((L.subgroupOf (centralizer (Y : Set G)) : Subgroup ↥(centralizer (Y : Set G))) :
    Set ↥(centralizer (Y : Set G)))).map (centralizer (Y : Set G)).subtype

@[expose] def O76 (Y : Subgroup G) : Subgroup G :=
  (standardComponentOddCore ↥(centralizer (Y : Set G))).map (centralizer (Y : Set G)).subtype

omit [Finite G] in
theorem isElemAbelian_subgroupOf' {p : ℕ} {V X : Subgroup G} (hV : IsElemAbelian p V) :
    IsElemAbelian p (V.subgroupOf X) := CFSG.Open.IsElemAbelian.subgroupOf hV X

namespace Cfg76

variable {A R Y L : Subgroup G} (hc : Cfg76 A R Y L)
include hc

theorem center_eq_bot : center ↥(L.subgroupOf (centralizer (Y : Set G))) = ⊥ ∧
    Nat.card (L.subgroupOf (centralizer (Y : Set G))) = 60 := by
  set e := subgroupOfEquivOfLe hc.L_le_centralizer
  obtain ⟨f⟩ := hc.a5
  refine center_eq_bot_of_a5 hc.standard.1 ?_
    ⟨(QuotientGroup.congr (center _) (center _) e (Subgroup.map_center_eq e)).trans f⟩
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact hc.oddCenter

theorem isElemAbelian_R (h32 : Lemma32) :
    IsElemAbelian 2 (R.subgroupOf (centralizer (Y : Set G))) :=
  isElemAbelian_subgroupOf' (h32 G A hc.hyp R hc.sylowR)

theorem four_le_R : 4 ≤ Nat.card (R.subgroupOf (centralizer (Y : Set G))) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe hc.R_le_centralizer_Y).toEquiv]
  exact Lemma36.four_le_card hc.hyp hc.sylowR

theorem R_le_centralizer' : R.subgroupOf (centralizer (Y : Set G)) ≤
    centralizer ((L.subgroupOf (centralizer (Y : Set G)) : Subgroup ↥(centralizer (Y : Set G))) :
      Set ↥(centralizer (Y : Set G))) := by
  rw [Lemma37.centralizer_subgroupOf hc.L_le_centralizer]
  intro r hr
  exact mem_subgroupOf.mpr (hc.R_le_centralizer_L (mem_subgroupOf.mp hr))

theorem exists_conj
    (h5 : Asc08Lemma310) (h32 : Lemma32) (hJ : J2Std.J2StdFacts) {x : G} (hxL : x ∈ L)
    (hx5 : orderOf x = 5) :
    ∃ c ∈ centralizer (Y : Set G) ⊓ centralizer ({x} : Set G), ∃ r ∈ R,
      c * r * c⁻¹ ∉ centralizer (L : Set G) := by
  obtain ⟨hZ, h60⟩ := hc.center_eq_bot
  have hxC : x ∈ centralizer (Y : Set G) := hc.L_le_centralizer hxL
  obtain ⟨c, hcx, r, hr, hcr⟩ := exists_conj_not_mem_centralizer hJ hc.rankTwoHyp
    (hc.isSporadic_j2 h5) (hc.isElemAbelian_R h32) hc.four_le_R hc.R_le_centralizer' hZ h60
    (x := ⟨x, hxC⟩) (mem_subgroupOf.mpr hxL) (by rw [Subgroup.orderOf_mk]; exact hx5)
  refine ⟨c, mem_inf.mpr ⟨c.2, ?_⟩, r, mem_subgroupOf.mp hr, fun hmem => hcr ?_⟩
  · rw [mem_centralizer_singleton_iff] at hcx ⊢
    exact congrArg Subtype.val hcx
  · rw [Lemma37.centralizer_subgroupOf hc.L_le_centralizer, mem_subgroupOf]
    simpa using hmem

omit [Finite G] hc in
theorem E76_le_centralizer : E76 Y L ≤ centralizer (Y : Set G) := map_subtype_le _

theorem R_le_E
    (h5 : Asc08Lemma310) (h32 : Lemma32) {x : G} (hxL : x ∈ L) (hx5 : orderOf x = 5) :
    R ≤ E76 Y L := by
  obtain ⟨hZ, -⟩ := hc.center_eq_bot
  have hxC : x ∈ centralizer (Y : Set G) := hc.L_le_centralizer hxL
  have h := le_normalClosure_of_elem hc.rankTwoHyp (hc.isSporadic_j2 h5) (hc.isElemAbelian_R h32)
    hc.R_le_centralizer' hZ (x := ⟨x, hxC⟩) (mem_subgroupOf.mpr hxL)
    (by rw [Subgroup.orderOf_mk]; exact hx5)
  intro r hr
  exact ⟨⟨r, hc.R_le_centralizer_Y hr⟩, h (mem_subgroupOf.mpr hr), rfl⟩

theorem mem_O76_of_central {z : G} (hz : z ∈ E76 Y L)
    (hzc : ∀ w ∈ E76 Y L, z * w = w * z) : z ∈ O76 Y := by
  obtain ⟨z', hz', rfl⟩ := hz
  refine ⟨z', mem_oddCore_of_central hc.rankTwoHyp fun w hw => ?_, rfl⟩
  exact Subtype.ext (hzc w ⟨w, hw, rfl⟩)

theorem card_E76 (h5 : Asc08Lemma310) :
    Nat.card (E76 Y L) = 604800 * Nat.card ↥(E76 Y L ⊓ O76 Y) := by
  have h := card_normalClosure (hc.isSporadic_j2 h5)
  rw [E76, O76, ← map_inf_eq _ _ _ (subtype_injective _),
    card_map_of_injective (subtype_injective _), card_map_of_injective (subtype_injective _)]
  exact h

theorem conj_mem_E
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (h5 : Asc08Lemma310) {Z : Subgroup G} (hZY : Z ≤ Y) (hZA : Z ≤ A)
    (hlay : layerCentralizer A Z = L) (hnoZ : NoInvolutoryCentralizing A (Z ⊔ L)) :
    ∀ c ∈ centralizer (Z : Set G), ∀ r ∈ E76 Y L, r ^ 2 = 1 → c * r * c⁻¹ ∈ E76 Y L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CZ := centralizer (Z : Set G) with hCZ
  have hCYZ : centralizer (Y : Set G) ≤ CZ := centralizer_le hZY
  have hLZ : L ≤ A ⊓ CZ := hlay ▸ layerCentralizer_le A Z
  have hLCZ : L ≤ CZ := hLZ.trans inf_le_right
  have hNL : normalizer (A : Set G) ⊓ CZ ≤ normalizer (L : Set G) :=
    hlay ▸ normalizer_inf_le_normalizer_layerCentralizer A Z
  have hRZ : R ≤ CZ := hc.sylowR.le.trans (centralizer_le hZA)
  have hRL : IsSylowOf 2 R (CZ ⊓ centralizer (L : Set G) ⊓ normalizer (R : Set G)) := by
    refine isSylowOf_of_noInvolutory hc.hyp hc.sylowR hnoZ
      (le_inf (le_inf hRZ hc.R_le_centralizer_L) le_normalizer) ?_ inf_le_right
    intro y hy
    obtain ⟨⟨hyZ, hyL⟩, -⟩ := mem_inf.mp hy
    exact mem_centralizer_sup hyZ hyL
  have hLq : CFSG.Open.IsQuasisimple ↥L :=
    (Lemma37.isQuasisimple_subgroupOf_iff hc.L_le_centralizer).mp hc.standard.1
  have hstd : standardComponentIsStandard (L.subgroupOf CZ) := by
    rcases lemma37_bender_of_le h4 h32 h34 hc.hyp hc.sylowR hZA hLq hLZ hNL hRL with
      h | ⟨c, -, -, -, hRc, -⟩
    · exact h
    · exfalso
      apply hc.not_le c
      rw [conj_eq_rightConjugate] at hRc
      calc rightConjugate R c ≤ rightConjugate (rightConjugate L c⁻¹) c := map_mono hRc
        _ = L := by rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
        _ ≤ A := hc.L_le_A
  have hnn : ¬ (L.subgroupOf CZ).Normal := by
    intro hn
    apply hc.not_normal
    refine ⟨fun n hn' g => ?_⟩
    have h1 := hn.conj_mem ⟨n, hCYZ n.2⟩ hn' ⟨g, hCYZ g.2⟩
    rw [mem_subgroupOf] at h1 ⊢
    simpa using h1
  have hH₂ : RankTwoHyp ↥CZ (L.subgroupOf CZ) :=
    ⟨LocalAnalysis.ComponentInitial.kProper_subgroup
        (fun e h => SectionRank.catalog_of_mulEquiv e h) hc.kProper _, hstd, hnn,
      two_le_pRank_centralizer_subgroupOf' hZA hc.L_le_A hc.rank⟩
  set e := subgroupOfEquivOfLe hLCZ
  obtain ⟨f⟩ := hc.a5
  have hX : Nat.card (rankTwoX ((L.subgroupOf CZ).map
      (QuotientGroup.mk' (standardComponentOddCore ↥CZ)))) ≤ 604800 := by
    refine card_rankTwoX_le h5 hH₂ (R := R.subgroupOf CZ)
      ⟨(QuotientGroup.congr (center _) (center _) e (Subgroup.map_center_eq e)).trans f⟩ ?_ ?_ ?_
    · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact hc.oddCenter
    · rw [Lemma37.centralizer_subgroupOf hLCZ,
        ← Subgroup.inf_subgroupOf_left (centralizer (L : Set G)) CZ,
        Lemma37.isSylowOf_subgroupOf_iff hRZ inf_le_left]
      exact Lemma37.isSylowOf_of_isSylowOf_inf_normalizer hRL
    · intro x hle
      apply hc.not_le (x : G)
      intro r hr
      rw [mem_rightConjugate_iff] at hr
      have hrC : r ∈ CZ := by
        have h1 : (x : G) * r * (x : G)⁻¹ ∈ CZ := hRZ hr
        have h2 : r = (x : G)⁻¹ * ((x : G) * r * (x : G)⁻¹) * (x : G) := by group
        rw [h2]
        exact mul_mem (mul_mem (inv_mem x.2) h1) x.2
      have h2 : (⟨r, hrC⟩ : ↥CZ) ∈ rightConjugate (R.subgroupOf CZ) x := by
        rw [mem_rightConjugate_iff, mem_subgroupOf]
        simpa using hr
      exact hc.L_le_A (mem_subgroupOf.mp (hle h2))
  have hEC : E76 Y L ≤ CZ := (E76_le_centralizer).trans hCYZ
  set EZ := (E76 Y L).subgroupOf CZ with hEZdef
  have hEZ : EZ ≤ normalClosure ((L.subgroupOf CZ : Subgroup ↥CZ) : Set ↥CZ) := by
    rintro ⟨w, hwC⟩ hw
    obtain ⟨w', hw', rfl⟩ := mem_subgroupOf.mp hw
    have hι := map_normalClosure_le ((L.subgroupOf (centralizer (Y : Set G)) :
      Subgroup ↥(centralizer (Y : Set G))) : Set ↥(centralizer (Y : Set G))) (inclusion hCYZ)
    have h1 : inclusion hCYZ w' ∈ normalClosure (inclusion hCYZ ''
        ((L.subgroupOf (centralizer (Y : Set G)) : Subgroup ↥(centralizer (Y : Set G))) :
          Set ↥(centralizer (Y : Set G)))) := hι ⟨w', hw', rfl⟩
    refine normalClosure_mono ?_ h1
    rintro _ ⟨l, hl, rfl⟩
    exact mem_subgroupOf.mpr (mem_subgroupOf.mp hl)
  have hOE : standardComponentOddCore ↥CZ ≤ centralizer (EZ : Set ↥CZ) :=
    (oddCore_le_centralizer_normalClosure hH₂).trans (centralizer_le hEZ)
  have hcard : 604800 ≤ Nat.card (EZ.map (QuotientGroup.mk' (standardComponentOddCore ↥CZ))) := by
    have h1 := card_map_mk'_mul EZ
    have h2 : Nat.card EZ = Nat.card (E76 Y L) := Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv
    have h3 := hc.card_E76 h5
    have h4 : Nat.card ↥(EZ ⊓ standardComponentOddCore ↥CZ) ≤ Nat.card ↥(E76 Y L ⊓ O76 Y) := by
      rw [← card_map_of_injective (subtype_injective CZ)]
      refine card_le_of_le ?_
      rintro _ ⟨z, ⟨hzE, hzO⟩, rfl⟩
      refine ⟨mem_subgroupOf.mp hzE, hc.mem_O76_of_central (mem_subgroupOf.mp hzE) ?_⟩
      intro w hw
      have h5' := (mem_centralizer_iff.mp (hOE hzO)) ⟨w, hEC hw⟩ (mem_subgroupOf.mpr hw)
      exact (congrArg Subtype.val h5').symm
    have hpos : 0 < Nat.card ↥(EZ ⊓ standardComponentOddCore ↥CZ) := Nat.card_pos
    rw [h2, h3] at h1
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc 604800 * Nat.card ↥(EZ ⊓ standardComponentOddCore ↥CZ) ≤
        604800 * Nat.card ↥(E76 Y L ⊓ O76 Y) := Nat.mul_le_mul_left _ h4
      _ = _ := h1.symm
  have hN := normal_sup_of_card hEZ hX hcard
  intro c hc' r hr hr2
  have hrZ : (⟨r, hEC hr⟩ : ↥CZ) ∈ EZ := mem_subgroupOf.mpr hr
  have h1 := hN.conj_mem _ (mem_sup_left hrZ) ⟨c, hc'⟩
  have h2 : (⟨c, hc'⟩ * ⟨r, hEC hr⟩ * (⟨c, hc'⟩ : ↥CZ)⁻¹) ^ 2 ^ 1 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one, pow_one]
    rw [sq, show c * r * c⁻¹ * (c * r * c⁻¹) = c * (r * r) * c⁻¹ by group, ← sq, hr2]
    group
  have h3 := mem_of_mem_sup odd_card_standardComponentOddCore hOE h1 h2
  exact mem_subgroupOf.mp h3

end Cfg76

end CFSG.ComponentClassification.RankTwoClassical
