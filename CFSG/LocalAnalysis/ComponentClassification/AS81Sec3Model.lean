module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3G2Align
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step31
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Foundations
public import CFSG.LargeExtraspecial.Types
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
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
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

namespace Sec3

section Transport

variable {H G : Type*} [Group H] [Group G] {f : H →* G}

theorem range_inf_normalizer_map (hf : Function.Injective f) (X : Subgroup H) :
    f.range ⊓ normalizer ((X.map f : Subgroup G) : Set G) = (normalizer (X : Set H)).map f := by
  apply le_antisymm
  · rintro g ⟨⟨n, rfl⟩, hg⟩
    refine ⟨n, ?_, rfl⟩
    have key : ∀ m : H, f m ∈ normalizer ((X.map f : Subgroup G) : Set G) →
        ∀ w ∈ X, m * w * m⁻¹ ∈ X := by
      intro m hm w hw
      obtain ⟨w', hw', hw'e⟩ := (mem_normalizer_iff.mp hm (f w)).mp ⟨w, hw, rfl⟩
      rw [show f m * f w * (f m)⁻¹ = f (m * w * m⁻¹) by simp] at hw'e
      rwa [← hf hw'e]
    refine G2.mem_normalizer_of_conj (key n hg) (fun w hw => ?_)
    have := key n⁻¹ (by rw [map_inv]; exact inv_mem hg) w hw
    rwa [inv_inv] at this
  · rintro _ ⟨n, hn, rfl⟩
    refine ⟨⟨n, rfl⟩, G2.mem_normalizer_of_conj (fun w hw => ?_) (fun w hw => ?_)⟩
    · obtain ⟨w', hw', rfl⟩ := hw
      exact ⟨n * w' * n⁻¹, (mem_normalizer_iff.mp hn w').mp hw', by simp⟩
    · obtain ⟨w', hw', rfl⟩ := hw
      have := (mem_normalizer_iff.mp (inv_mem hn) w').mp hw'
      rw [inv_inv] at this
      exact ⟨n⁻¹ * w' * n, this, by simp⟩

theorem pCoreOf_map_of_injective (hf : Function.Injective f) (p : ℕ) (X : Subgroup H) :
    pCoreOf p (X.map f) = (pCoreOf p X).map f := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have h1 := LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [← h1, map_map, map_map]
  congr 1

end Transport

section Frame

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}

omit [Finite G] in
theorem isElemAbelian_of_le {X Y : Subgroup G} (hX : IsElemAbelian 2 X) (hYX : Y ≤ X) :
    IsElemAbelian 2 Y := CFSG.Open.IsElemAbelian.mono hX hYX

theorem R_inf_A (hS : Sec3Setting G A A₁ R g E F x) : R ⊓ A = ⊥ := by
  rw [eq_bot_iff]
  rintro r ⟨hrR, hrA⟩
  have hrc : (⟨r, hrA⟩ : ↥A) ∈ center ↥A := by
    rw [mem_center_iff]
    intro a
    exact Subtype.ext (mem_centralizer_iff.mp (hS.sylowR.le hrR) a a.2)
  rw [hS.center_eq, mem_bot] at hrc
  exact congrArg Subtype.val hrc

theorem exists_mul_of_mem_sup (hS : Sec3Setting G A A₁ R g E F x) {w : G} (hw : w ∈ A₁ ⊔ R) :
    ∃ a ∈ A₁, ∃ r ∈ R, w = a * r := by
  have hRA₁ : R ≤ normalizer (A₁ : Set G) :=
    (hS.sylowR.le.trans (centralizer_le hS.le)).trans (centralizer_le_normalizer _)
  have hw' : w ∈ (A₁ : Set G) * (R : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A₁ R hRA₁]
    exact hw
  obtain ⟨a, ha, r, hr, rfl⟩ := hw'
  exact ⟨a, ha, r, hr, rfl⟩

theorem inf_A_eq (hS : Sec3Setting G A A₁ R g E F x) {X : Subgroup G} (hX : X ≤ A₁ ⊔ R) :
    X ⊓ A = X ⊓ A₁ := by
  refine le_antisymm (fun w ⟨hwX, hwA⟩ => ⟨hwX, ?_⟩) (inf_le_inf_left _ hS.le)
  obtain ⟨a, ha, r, hr, rfl⟩ := exists_mul_of_mem_sup hS (hX hwX)
  have hrA : r ∈ A := by
    rw [show r = a⁻¹ * (a * r) by group]
    exact A.mul_mem (A.inv_mem (hS.le ha)) hwA
  have h1 : r ∈ R ⊓ A := ⟨hr, hrA⟩
  rw [R_inf_A hS, mem_bot] at h1
  rw [h1, mul_one]
  exact ha

theorem card_eq_of_le_sup (hS : Sec3Setting G A A₁ R g E F x) {X : Subgroup G} (hRX : R ≤ X)
    (hX : X ≤ A₁ ⊔ R) : Nat.card X = Nat.card ↥(X ⊓ A₁) * Nat.card R := by
  rw [← Nat.card_prod]
  refine (Nat.card_eq_of_bijective (fun p : ↥(X ⊓ A₁) × ↥R =>
    (⟨(p.1 : G) * p.2, X.mul_mem p.1.2.1 (hRX p.2.2)⟩ : ↥X)) ⟨fun p p' h => ?_, fun w => ?_⟩).symm
  · have h1 : (p.1 : G) * p.2 = p'.1 * p'.2 := congrArg Subtype.val h
    have h2 : (p'.1 : G)⁻¹ * p.1 ∈ R ⊓ A := by
      refine ⟨?_, A.mul_mem (A.inv_mem (hS.le p'.1.2.2)) (hS.le p.1.2.2)⟩
      rw [show (p'.1 : G)⁻¹ * p.1 = p'.2 * (p.2 : G)⁻¹ by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]]
      exact R.mul_mem p'.2.2 (R.inv_mem p.2.2)
    rw [R_inf_A hS, mem_bot, inv_mul_eq_one] at h2
    have h3 : (p.2 : G) = p'.2 := by
      rw [← h2] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext h2.symm) (Subtype.ext h3)
  · obtain ⟨a, ha, r, hr, hw⟩ := exists_mul_of_mem_sup hS (hX w.2)
    have haX : a ∈ X := by
      rw [show a = w * r⁻¹ by rw [hw, mul_inv_cancel_right]]
      exact X.mul_mem w.2 (X.inv_mem (hRX hr))
    exact ⟨(⟨a, haX, ha⟩, ⟨r, hr⟩), Subtype.ext hw.symm⟩

theorem card_A₁ (hS : Sec3Setting G A A₁ R g E F x) : Nat.card A₁ = 60480 := by
  have hZ : Nat.card (center ↥A₁) = 3 := by
    rw [← card_centerIn, hS.center_A₁, Nat.card_zpowers, hS.order_x]
  have hQ : Nat.card (↥A₁ ⧸ center ↥A₁) = 20160 := by
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS.typeA₁
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
    decide
  rw [card_eq_card_quotient_mul_card_subgroup (center ↥A₁), hQ, hZ]

theorem frame_inf_A₁ (hS : Sec3Setting G A A₁ R g E F x) :
    E ⊓ A = E ⊓ A₁ ∧ F ⊓ A = F ⊓ A₁ ∧ IsElemAbelian 2 (E ⊓ A₁) ∧ IsElemAbelian 2 (F ⊓ A₁) ∧
      Nat.card ↥(E ⊓ A₁) = 16 ∧ Nat.card ↥(F ⊓ A₁) = 16 ∧ E ⊓ A₁ ≠ F ⊓ A₁ ∧
      IsSylowOf 2 ((E ⊔ F) ⊓ A₁) A₁ ∧ Nat.card ↥((E ⊔ F) ⊓ A₁) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFr := hS.frame
  have hR4 := hFr.cardR
  have hE := card_eq_of_le_sup hS hFr.R_le_E hFr.E_le
  have hF := card_eq_of_le_sup hS hFr.R_le_F hFr.F_le
  rw [hFr.cardE, hR4] at hE
  rw [hFr.cardF, hR4] at hF
  have hRA₁ : A₁ ⊔ R ≤ normalizer (A₁ : Set G) := sup_le le_normalizer
    ((hS.sylowR.le.trans (centralizer_le hS.le)).trans (centralizer_le_normalizer _))
  have hSyl := hFr.sylow.inf_of_le_normalizer le_sup_left hRA₁
  refine ⟨inf_A_eq hS hFr.E_le, inf_A_eq hS hFr.F_le, isElemAbelian_of_le hFr.elemE inf_le_left,
    isElemAbelian_of_le hFr.elemF inf_le_left, by omega, by omega, fun h => hFr.ne ?_, hSyl, ?_⟩
  ·
    have key : ∀ {X Y : Subgroup G}, R ≤ X → R ≤ Y → X ≤ A₁ ⊔ R → X ⊓ A₁ ≤ Y → X ≤ Y := by
      intro X Y hRX hRY hX hXY w hw
      obtain ⟨a, ha, r, hr, rfl⟩ := exists_mul_of_mem_sup hS (hX hw)
      have haX : a ∈ X := by
        rw [show a = a * r * r⁻¹ by group]
        exact X.mul_mem hw (X.inv_mem (hRX hr))
      exact Y.mul_mem (hXY ⟨haX, ha⟩) (hRY hr)
    exact le_antisymm (key hFr.R_le_E hFr.R_le_F hFr.E_le (by rw [h]; exact inf_le_left))
      (key hFr.R_le_F hFr.R_le_E hFr.F_le (by rw [← h]; exact inf_le_left))
  · rw [hSyl.card_eq, card_A₁ hS]
    have h1 : (60480 : ℕ) = 2 ^ 6 * 945 := by norm_num
    rw [h1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
    norm_num

end Frame

section Sub

variable {M : Type*} [Group M] {C : Subgroup M}

theorem eq_subgroupOf_of_map_eq {X : Subgroup ↥C} {Y : Subgroup M} (h : X.map C.subtype = Y) :
    X = Y.subgroupOf C := by
  rw [← h, subgroupOf, comap_map_eq_self_of_injective C.subtype_injective]

theorem map_subgroupOf_eq {Y : Subgroup M} (hY : Y ≤ C) : (Y.subgroupOf C).map C.subtype = Y := by
  rw [subgroupOf_map_subtype, inf_eq_left.mpr hY]

theorem map_conj_eq_of_mem_normalizer {L : Subgroup M} {c : M} (hc : c ∈ normalizer (L : Set M)) :
    L.map (MulAut.conj c).toMonoidHom = L := by
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact (mem_normalizer_iff.mp hc w').mp hw'
  · intro hw
    refine ⟨c⁻¹ * w * c, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (mem_normalizer_iff.mp (inv_mem hc) w).mp hw
    rwa [inv_inv] at this

end Sub

section TrC

variable {M G : Type} [Group M] [Group G] {C : Subgroup M} {f : ↥C →* G}

theorem tr_mono {Y Y' : Subgroup M} (h : Y ≤ Y') :
    (Y.subgroupOf C).map f ≤ (Y'.subgroupOf C).map f :=
  map_mono fun _ ha => mem_subgroupOf.mpr (h (mem_subgroupOf.mp ha))

theorem tr_sup {Y Y' : Subgroup M} (hY : Y ≤ C) (hY' : Y' ≤ C) :
    ((Y ⊔ Y').subgroupOf C).map f = (Y.subgroupOf C).map f ⊔ (Y'.subgroupOf C).map f := by
  rw [subgroupOf_sup hY hY', Subgroup.map_sup]

theorem subgroupOf_commutator {Y Y' : Subgroup M} (hY : Y ≤ C) (hY' : Y' ≤ C) :
    ⁅Y, Y'⁆.subgroupOf C = ⁅Y.subgroupOf C, Y'.subgroupOf C⁆ := by
  refine (eq_subgroupOf_of_map_eq ?_).symm
  rw [map_commutator, map_subgroupOf_eq hY, map_subgroupOf_eq hY']

theorem tr_commutator {Y Y' : Subgroup M} (hY : Y ≤ C) (hY' : Y' ≤ C) :
    (⁅Y, Y'⁆.subgroupOf C).map f = ⁅(Y.subgroupOf C).map f, (Y'.subgroupOf C).map f⁆ := by
  rw [subgroupOf_commutator hY hY', map_commutator]

theorem subgroupOf_centerIn {Y : Subgroup M} (hY : Y ≤ C) :
    centerIn (Y.subgroupOf C) = (centerIn Y).subgroupOf C := by
  refine eq_subgroupOf_of_map_eq ?_
  rw [← centerIn_map_of_injective _ C.subtype_injective, map_subgroupOf_eq hY]

theorem tr_centerIn (hf : Function.Injective f) {Y : Subgroup M} (hY : Y ≤ C) :
    centerIn ((Y.subgroupOf C).map f) = ((centerIn Y).subgroupOf C).map f := by
  rw [centerIn_map_of_injective _ hf, subgroupOf_centerIn hY]

theorem subgroupOf_pCoreOf {Y : Subgroup M} (hY : Y ≤ C) (p : ℕ) :
    pCoreOf p (Y.subgroupOf C) = (pCoreOf p Y).subgroupOf C := by
  refine eq_subgroupOf_of_map_eq ?_
  rw [← pCoreOf_map_of_injective C.subtype_injective, map_subgroupOf_eq hY]

theorem tr_pCoreOf (hf : Function.Injective f) {Y : Subgroup M} (hY : Y ≤ C) (p : ℕ) :
    pCoreOf p ((Y.subgroupOf C).map f) = ((pCoreOf p Y).subgroupOf C).map f := by
  rw [pCoreOf_map_of_injective hf, subgroupOf_pCoreOf hY]

theorem tr_normalizer (hf : Function.Injective f) {Y : Subgroup M} (hY : Y ≤ C) :
    f.range ⊓ normalizer (((Y.subgroupOf C).map f : Subgroup G) : Set G) =
      ((C ⊓ normalizer (Y : Set M)).subgroupOf C).map f := by
  rw [range_inf_normalizer_map hf, ← subgroupOf_normalizer_eq hY, inf_subgroupOf_left]

theorem tr_relIndex (hf : Function.Injective f) {Y Y' : Subgroup M} (hY' : Y' ≤ C) :
    ((Y.subgroupOf C).map f).relIndex ((Y'.subgroupOf C).map f) = Y.relIndex Y' := by
  rw [relIndex_map_map_of_injective _ _ hf, relIndex_subgroupOf hY']

end TrC

end Sec3

structure Sec3Model
    (G : Type) [Group G] (A A₁ E F : Subgroup G) (x : G) (K : Type) [Field K] [CharP K 2]
    (f : ↥(adjointGroup .G2 K) →* G) : Prop where
  inj : Function.Injective f
  range_eq : f.range = A
  E_eq : ((g2BCGroup K).subgroupOf (adjointGroup .G2 K)).map f = E ⊓ A
  F_eq : ((G2.g2ACGroup K).subgroupOf (adjointGroup .G2 K)).map f = F ⊓ A₁
  A₁_eq : ((g2LongA2 K).subgroupOf (adjointGroup .G2 K)).map f = A₁
  x_eq : ((g2TorusR K).subgroupOf (adjointGroup .G2 K)).map f = zpowers x

open Sec3 in
theorem exists_sec3Model
    {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
    (hS : Sec3Setting G A A₁ R g E F x) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 4 ∧
      ∃ f : ↥(adjointGroup .G2 K) →* G, Sec3Model G A A₁ E F x K f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hEA, hFA, hE₁, hF₁, hE16, hF16, hne, hSyl, hS64⟩ := frame_inf_A₁ hS
  obtain ⟨K, _, _, _, hK, φ, hφA₁, hφx⟩ := hS.coords
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, ?_⟩
  set ι : ↥A →* ModGL .G2 K := (adjointGroup .G2 K).subtype.comp φ.toMonoidHom with hι
  have hιinj : Function.Injective ι := (adjointGroup .G2 K).subtype_injective.comp φ.injective
  have himA : ∀ {X : Subgroup G}, X ≤ A → Nat.card ((X.subgroupOf A).map ι) = Nat.card X :=
    fun {X} hX => by
      rw [card_map_of_injective hιinj, Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv]
  have hA₁ : (A₁.subgroupOf A).map ι = g2LongA2 K := by
    rw [hι, ← map_map, hφA₁, map_subgroupOf_eq g2LongA2_le_adjointGroup]
  have hHr : ((zpowers x).subgroupOf A).map ι = g2TorusR K := by
    rw [hι, ← map_map, hφx, map_subgroupOf_eq G2.g2TorusR_le_adjointGroup]
  have hS₁A : (E ⊔ F) ⊓ A₁ ≤ A := inf_le_right.trans hS.le
  have hE₁A : E ⊓ A₁ ≤ A := inf_le_right.trans hS.le
  have hF₁A : F ⊓ A₁ ≤ A := inf_le_right.trans hS.le
  have hSylL : IsSylowOf 2 ((((E ⊔ F) ⊓ A₁).subgroupOf A).map ι) (g2LongA2 K) := by
    rw [← hA₁]
    refine AschbacherTheorem3.IsSylowOf.map ?_ ι
    rw [← isSylowOf_map_subtype_iff A, map_subgroupOf_eq hS₁A, map_subgroupOf_eq hS.le]
    exact hSyl
  have helem : ∀ {X : Subgroup G}, IsElemAbelian 2 X →
      IsElemAbelian 2 ((X.subgroupOf A).map ι) := fun {X} hX => by
    refine G2.isElemAbelian_map_of ι ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩,
      fun a ha => Subtype.ext ?_⟩
    · have := congrArg Subtype.val (hX.1.is_comm.comm ⟨a, mem_subgroupOf.mp a.2⟩
        ⟨b, mem_subgroupOf.mp b.2⟩)
      simpa using this
    · simpa using hX.2 _ (mem_subgroupOf.mp ha)
  have hle : ∀ {X Y : Subgroup G}, X ≤ Y →
      (X.subgroupOf A).map ι ≤ (Y.subgroupOf A).map ι := fun {X Y} h =>
    map_mono fun a ha => mem_subgroupOf.mpr (h (mem_subgroupOf.mp ha))
  have himinj : ∀ {X Y : Subgroup G}, X ≤ A → Y ≤ A →
      (X.subgroupOf A).map ι = (Y.subgroupOf A).map ι → X = Y := fun {X Y} hX hY h => by
    have h1 := map_injective hιinj h
    rw [← map_subgroupOf_eq hX, ← map_subgroupOf_eq hY, h1]
  obtain ⟨c, hcC, hcL, hcH, hc₁, hc₂⟩ := G2.exists_align hK hSylL (by rw [himA hS₁A, hS64])
    (hle (inf_le_inf_right _ le_sup_left)) (hle (inf_le_inf_right _ le_sup_right)) (helem hE₁)
    (helem hF₁) (by rw [himA hE₁A, hE16]) (by rw [himA hF₁A, hF16])
    (fun h => hne (himinj hE₁A hF₁A h))
  set φ' : ↥A ≃* ↥(adjointGroup .G2 K) := φ.trans (MulAut.conj (⟨c, hcC⟩ :
    ↥(adjointGroup .G2 K))) with hφ'
  have hφ'map : ∀ X : Subgroup G, ((X.subgroupOf A).map φ'.toMonoidHom).map
      (adjointGroup .G2 K).subtype = ((X.subgroupOf A).map ι).map (MulAut.conj c).toMonoidHom := by
    intro X
    rw [map_map, map_map]
    congr 1
  have hcorr : ∀ {X : Subgroup G} {Y : Subgroup (ModGL .G2 K)},
      ((X.subgroupOf A).map ι).map (MulAut.conj c).toMonoidHom = Y →
      (X.subgroupOf A).map φ'.toMonoidHom = Y.subgroupOf (adjointGroup .G2 K) :=
    fun {X Y} h => eq_subgroupOf_of_map_eq ((hφ'map X).trans h)
  have hE₁ := hcorr hc₁
  have hF₁ := hcorr hc₂
  have hA₁' := hcorr (show ((A₁.subgroupOf A).map ι).map (MulAut.conj c).toMonoidHom =
    g2LongA2 K by rw [hA₁, Sec3.map_conj_eq_of_mem_normalizer hcL])
  have hx' := hcorr (show (((zpowers x).subgroupOf A).map ι).map (MulAut.conj c).toMonoidHom =
    g2TorusR K by rw [hHr, Sec3.map_conj_eq_of_mem_normalizer hcH])
  set f : ↥(adjointGroup .G2 K) →* G := A.subtype.comp φ'.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := A.subtype_injective.comp φ'.symm.injective
  have hfrange : f.range = A := by
    rw [hf, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ φ'.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hback : ∀ {X : Subgroup G} {Y : Subgroup (ModGL .G2 K)}, X ≤ A →
      (X.subgroupOf A).map φ'.toMonoidHom = Y.subgroupOf (adjointGroup .G2 K) →
      (Y.subgroupOf (adjointGroup .G2 K)).map f = X := fun {X Y} hX h => by
    rw [← h, hf, map_map, MonoidHom.comp_assoc, show φ'.symm.toMonoidHom.comp φ'.toMonoidHom =
      MonoidHom.id _ by ext; simp, MonoidHom.comp_id, map_subgroupOf_eq hX]
  have hEA' : ((g2BCGroup K).subgroupOf (adjointGroup .G2 K)).map f = E ⊓ A := by
    rw [hEA]
    exact hback hE₁A hE₁
  have hFA' : ((G2.g2ACGroup K).subgroupOf (adjointGroup .G2 K)).map f = F ⊓ A₁ :=
    hback hF₁A hF₁
  have hxA₁ : x ∈ centerIn A₁ := by
    rw [hS.center_A₁]
    exact mem_zpowers x
  have hxA' : ((g2TorusR K).subgroupOf (adjointGroup .G2 K)).map f = zpowers x :=
    hback (zpowers_le.mpr (hS.le hxA₁.1)) hx'

  exact ⟨f, hfinj, hfrange, hEA', hFA', hback hS.le hA₁', hxA'⟩

namespace Sec3Model

variable {G : Type} [Group G] {A A₁ E F : Subgroup G} {x : G} {K : Type} [Field K] [CharP K 2]
  {f : ↥(adjointGroup .G2 K) →* G}

theorem I_eq
    (hM : Sec3Model G A A₁ E F x K f) :
    A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G) =
      ((G2.g2Para K).subgroupOf (adjointGroup .G2 K)).map f := by
  rw [← hM.E_eq, ← hM.range_eq, Sec3.tr_normalizer hM.inj
    (G2.g2BCGroup_le_g2ShortParabolicRadical.trans G2.g2ShortParabolicRadical_le_adjointGroup),
    G2.adjointGroup_inf_normalizer_eq]

end Sec3Model

end CFSG.ComponentClassification.AS81
