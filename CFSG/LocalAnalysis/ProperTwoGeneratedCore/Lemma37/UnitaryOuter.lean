module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterContradiction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Statement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterModelData

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

namespace UnitaryOuter

theorem card_sq_eq_card_sq_bar {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G}
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    (y : Subgroup.centralizer ({z} : Set G)) (hy : (y : G) ∈ (S : Subgroup G)) :
    Nat.card {w : G // w ∈ (S : Subgroup G) ∧ w ^ 2 = y} =
      Nat.card {v : EscapingQuotient z // v ∈ escapingSylowImage S z ∧
        v ^ 2 = escapingMk z y} := by
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨escapingMk z ⟨w.1, hSz w.2.1⟩,
    ⟨⟨w.1, hSz w.2.1⟩, Subgroup.mem_subgroupOf.mpr w.2.1, rfl⟩, ?_⟩) ⟨?_, ?_⟩)
  · rw [← map_pow]
    congr 1
    exact Subtype.ext w.2.2
  · intro w w' h
    have := escapingMk_injOn_twoGroup S.isPGroup' (a := ⟨w.1, hSz w.2.1⟩) (b := ⟨w'.1, hSz w'.2.1⟩)
      w.2.1 w'.2.1 (congrArg Subtype.val h)
    have h2 := congrArg (fun a : Subgroup.centralizer ({z} : Set G) => (a : G)) this
    exact Subtype.ext h2
  · rintro ⟨v, ⟨w, hw, rfl⟩, hv⟩
    have hw' : (w : G) ∈ (S : Subgroup G) := Subgroup.mem_subgroupOf.mp hw
    refine ⟨⟨w, hw', ?_⟩, rfl⟩
    have h := escapingMk_injOn_twoGroup S.isPGroup' (a := w ^ 2) (b := y)
      (by simpa using (S : Subgroup G).pow_mem hw' 2) hy (by rw [map_pow]; exact hv)
    simpa using congrArg Subtype.val h

end UnitaryOuter

theorem caseIUnitaryOuterExcluded : CaseIUnitaryOuterExcluded := by
  intro G _ _ S H z hset hz hesc J hJ hzJ ⟨n, ⟨e⟩⟩ hnot
  have hq := escapingQuotientData hset (hset.sylow_le hz.1) hz.2.1 hesc
  have := hq.component_normal hJ hzJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · exact UnitaryOuter.false_of_mulEquiv_psu3Model_of_lt_two
      (hq.component_isSimpleBenderGroup hJ hzJ) hn e
  have hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := hz.le_centralizer
  have hsyl : ∀ P : Subgroup G, P ≤ Subgroup.centralizer ({z} : Set G) → IsPGroup 2 P →
      Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G) :
        Subgroup G) := by
    intro P _ hP
    rw [inf_eq_left.mpr hSz]
    obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
    refine (Subgroup.card_le_of_le hPQ).trans (le_of_eq ?_)
    rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity S]
  obtain ⟨T, hT⟩ := exists_sylow_eq_escapingSylowImage hsyl
  let k := GaloisField 2 n
  let K := FiniteField.Extension k 2 2
  let J' := binaryQuadraticHermitian n (by omega)
  have hcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : K // J'.conj x = x} = 2 ^ n :=
    quadraticBinaryFrobenius_fixed_card n (by omega)
  obtain ⟨u⟩ := projectiveSpecialUnitary_equiv_PSU3Model J' n hn rfl hcard hfixed
  have hmodel := UnitaryOuter.unitaryOuterModel_of_mulEquiv J' hn hcard hfixed rfl (e.trans u.symm)
    (CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal T J)
  rw [CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe, hT] at hmodel
  have hS : UnitaryOuter.OuterSetting (EscapingQuotient z) J (escapingSylowImage S z)
      (escapingBar z) (2 ^ n) :=
    { isPGroup := hT ▸ T.isPGroup'
      zb_mem := ⟨escapingSelf z, Subgroup.mem_subgroupOf.mpr hz.1, rfl⟩
      zb_central := fun x => (hq.commute_bar x).eq
      zb_not_mem := hzJ
      zb_sq := by
        have h := pow_orderOf_eq_one (escapingBar z)
        rwa [hq.bar_order] at h
      involution := fun t ht2 ht1 => hq.involution_mem_component_or hJ hzJ
        (orderOf_eq_prime ht2 ht1)
      model := hmodel }
  obtain ⟨s, hs, hsJK⟩ := Set.not_subset.mp hnot
  have hsRT : ¬ UnitaryOuter.OuterSetting.InRT (escapingSylowImage S z) J s := by
    rintro ⟨y, hy, t, ht, rfl⟩
    exact hsJK (Subgroup.mul_mem _ (Subgroup.mem_sup_left hy.2) (Subgroup.mem_sup_right ht.2))
  obtain ⟨r, hr, hrz, hrJ, a, ha, -, -, hroots⟩ :=
    coreSetting_component_fused_class_roots hset hz hesc hJ hzJ
  have hc := hroots S le_rfl 2
  have hz' := UnitaryOuter.card_sq_eq_card_sq_bar hSz (escapingSelf z) hz.1
  have hr' := UnitaryOuter.card_sq_eq_card_sq_bar hSz r hr.1
  have hrz' := UnitaryOuter.card_sq_eq_card_sq_bar hSz (r * escapingSelf z)
    ((S : Subgroup G).mul_mem hr.1 hz.1)
  have hr2 : r ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hr.2.1, pow_orderOf_eq_one, Subgroup.coe_one]
  have hu : escapingMk z r ∈ escapingSylowImage S z ⊓ J :=
    ⟨⟨r, Subgroup.mem_subgroupOf.mpr hr.1, rfl⟩, hrJ⟩
  have hu1 : escapingMk z r ≠ 1 := by
    intro h1
    have h := escapingMk_injOn_twoGroup S.isPGroup' (a := r) (b := 1) hr.1
      (Subgroup.one_mem _) (by rw [h1, map_one])
    have h2 := hr.2.1
    rw [show (r : G) = 1 from congrArg Subtype.val h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hu2 : escapingMk z r ^ 2 = 1 := by rw [← map_pow, hr2, map_one]
  refine hS.false_of_card_sq hs hsRT hu hu1 hu2 ?_
  rcases ha with rfl | rfl
  · left
    rw [← hz', ← hr']
    exact hc
  · right
    rw [← hz', show escapingMk z r * escapingBar z = escapingMk z (r * escapingSelf z) from
      (map_mul _ _ _).symm, ← hrz']
    exact hc

end CFSG.ProperTwoGeneratedCore.Lemma37
