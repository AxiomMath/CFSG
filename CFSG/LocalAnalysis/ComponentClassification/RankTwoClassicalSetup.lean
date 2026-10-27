module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma39
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma36

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_admResidual_of_perfect {X P : Subgroup G} (hPX : P ≤ X) (hP : ⁅P, P⁆ = P) :
    P ≤ admResidual X := by
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  refine le_sInf ?_
  rintro Y ⟨-, hN, hsolv, -⟩
  let φ : ↥P →* ↥X ⧸ Y.subgroupOf X := (QuotientGroup.mk' (Y.subgroupOf X)).comp (inclusion hPX)
  have hφ : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥φ.range := (nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
    exact Group.IsPerfect.not_isSolvable ↥φ.range inferInstance
  intro x hx
  have h1 : φ ⟨x, hx⟩ ∈ φ.range := ⟨_, rfl⟩
  rw [hφ, mem_bot] at h1
  have h2 : (inclusion hPX ⟨x, hx⟩ : ↥X) ∈ Y.subgroupOf X := by
    rw [← QuotientGroup.ker_mk' (Y.subgroupOf X)]
    exact h1
  exact mem_subgroupOf.mp h2

structure Sec3 (A R T : Subgroup G) (g : G) : Prop where
  hyp : Hyp31 A
  sylowR : IsSylowOf 2 R (centralizer (A : Set G))
  not_mem : g ∉ normalizer (A : Set G)
  sylowT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)
  le_centralizer : T ≤ centralizer (R : Set G)

theorem Choice74.sec3 {A R T : Subgroup G} {g : G} {D : ClassicalModel A} (hA : Hyp31 A)
    (h : Choice74 D R T g) : Sec3 A R T g :=
  ⟨hA, h.sylowR, h.not_mem, h.sylowT, h.le_centralizer⟩

namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem R_ne_bot : R ≠ ⊥ :=
  Lemma22.ne_bot_of_isSylowOf_of_tightlyEmbedded (tightlyEmbedded_centralizer hc.hyp.standard)
    hc.sylowR

theorem T_ne_bot : T ≠ ⊥ :=
  isSylowOf_ne_bot_of_even hc.sylowT
    (by rw [rightConjugate_card]; exact (tightlyEmbedded_centralizer hc.hyp.standard).1)

theorem le_normalizer : T ≤ normalizer (A : Set G) := by
  have h := Lemma36.normalizer_le hc.hyp hc.sylowR 1
  rw [rightConjugate_one, rightConjugate_one] at h
  exact hc.le_centralizer.trans ((centralizer_le_normalizer _).trans h)

theorem le_normalizer_R : T ≤ normalizer (R : Set G) :=
  hc.le_centralizer.trans (centralizer_le_normalizer _)

theorem inf_eq_bot : R ⊓ T = ⊥ :=
  Lemma36.inf_eq_bot_of_not_mem hc.hyp hc.sylowR hc.not_mem hc.sylowT

theorem card_eq : Nat.card T = Nat.card R := by
  rw [hc.sylowT.card_eq, hc.sylowR.card_eq, rightConjugate_card]

theorem four_le : 4 ≤ Nat.card R :=
  Lemma36.four_le_card hc.hyp hc.sylowR

theorem elemR (h32 : Lemma32) : IsElemAbelian 2 R :=
  h32 G A hc.hyp R hc.sylowR

theorem elemT (h32 : Lemma32) : IsElemAbelian 2 T :=
  isElemAbelian_of_isSylowOf_rightConjugate h32 hc.hyp hc.sylowT

theorem isPGroup_sup : IsPGroup 2 ↥(R ⊔ T) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.to_sup_of_normal_left' hc.sylowR.isPGroup hc.sylowT.isPGroup hc.le_normalizer_R

theorem le_sup_centralizer (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) :
    T ≤ A ⊔ centralizer (A : Set G) :=
  lemma33Two_of h32 h4 h34 G A hc.hyp R hc.sylowR g hc.not_mem T
    (hc.sylowT.of_le (le_inf hc.sylowT.le hc.le_normalizer) inf_le_left) hc.T_ne_bot
    hc.le_normalizer_R hc.sylowT

theorem le_sup (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) : T ≤ R ⊔ A :=
  le_sup_right.trans (le_sup_of_isSylowOf (centralizer_le_normalizer _) hc.sylowR le_sup_left
    hc.isPGroup_sup (sup_le (hc.sylowR.le.trans le_sup_right)
      (hc.le_sup_centralizer h32 h4 h34)))

theorem exists_aPart (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) {t : G}
    (ht : t ∈ T) : ∃ p ∈ A, t⁻¹ * p ∈ R := by
  have hRA : R ≤ normalizer (A : Set G) :=
    hc.sylowR.le.trans (centralizer_le_normalizer _)
  have htRA : t ∈ ((R ⊔ A : Subgroup G) : Set G) := hc.le_sup h32 h4 h34 ht
  rw [coe_mul_of_left_le_normalizer_right R A hRA] at htRA
  obtain ⟨r, hr, a, ha, hra⟩ := htRA
  refine ⟨a, ha, ?_⟩
  have hrt : Commute r t := mem_centralizer_iff.mp (hc.le_centralizer ht) r hr
  have h1 : a = r⁻¹ * t := by rw [← hra]; group
  have : t⁻¹ * a = r⁻¹ := by
    rw [h1, hrt.inv_left.eq]
    group
  rw [this]
  exact inv_mem hr

theorem swap : Sec3 A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) g⁻¹ := by
  refine ⟨hc.hyp, ?_, fun h => hc.not_mem (by simpa using inv_mem h), ?_, ?_⟩
  · have := AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowT g⁻¹
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
  · exact AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR g⁻¹
  · rw [centralizer_rightConjugate]
    have h : R ≤ centralizer (T : Set G) := by
      rw [le_centralizer_iff]
      exact hc.le_centralizer
    exact map_mono h

theorem inf_eq_bot_of_primary (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (h117 : ClassicalPrimaryPerfect) (D : ClassicalModel A) (hq : 4 ≤ D.q)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZ : Odd (Nat.card (center A)))
    (hprim : ∀ t ∈ T, t ≠ 1 → ∀ p ∈ A, t⁻¹ * p ∈ R → D.IsPrimary p) : T ⊓ A = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  rw [mem_bot]
  by_contra ht1
  obtain ⟨htT, htA⟩ := mem_inf.mp ht
  have hp := hprim t htT ht1 t htA (by rw [inv_mul_cancel]; exact one_mem R)
  have h1 := h117 G A D hc.hyp.standard.1 hZ hq t hp
  have h2 : CFSG.Quasithin.perfectCore (A ⊓ centralizer ({t} : Set G)) ≤
      admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆) :=
    le_admResidual_of_perfect
      ((CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans le_sup_right)
      (CFSG.Quasithin.perfectCore_perfect _)
  have htg : t ∈ rightConjugate A g :=
    (Lemma39.lemma39_one h4 h32 h34 hc.hyp hc.sylowT htT ht1 hOut).1 (h2 h1)
  have htK : t ∈ rightConjugate (centralizer (A : Set G)) g := hc.sylowT.le htT
  rw [mem_rightConjugate_iff] at htg htK
  set x := g * t * g⁻¹ with hx
  have hxZ : (⟨x, htg⟩ : ↥A) ∈ center ↥A := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp htK y y.2)
  have ht2 : orderOf t = 2 := orderOf_eq_prime ((hc.elemT h32).2 t htT) ht1
  have hx2 : orderOf (⟨x, htg⟩ : ↥A) = 2 := by
    rw [Subgroup.orderOf_mk, hx, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ht2]
  have hdvd := Subgroup.orderOf_dvd_natCard (center ↥A) hxZ
  rw [hx2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr hdvd)

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
