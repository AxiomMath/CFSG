module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSec72

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.Goldschmidt AS76b.Lemma36

variable {G : Type} [Group G] [Finite G]

structure Inputs74 : Prop where
  h32 : Lemma32
  h4 : Asc75Theorem4
  h34 : Asc08Lemma34
  h2 : Asc76Theorem2
  hOut : ClassicalOutCommOdd
  hF : ClassicalCentralizerCharTwo
  h222 : Classical222Large
  hJS : ClassicalJSylow

omit [Finite G] in
theorem CaseI.case14 {A : Subgroup G} {D : ClassicalModel A} {p : G}
    (hfam : D.family ≠ .symplectic) (h : CaseI D p) : Case1 D p ∨ Case4 D p := by
  revert h hfam
  unfold CaseI
  cases D.family with
  | linear => exact fun _ => Or.inl
  | unitary => exact fun _ => Or.inl
  | symplectic => exact fun h => absurd rfl h
  | orthPlus => exact fun _ h => h
  | orthMinus => exact fun _ h => h

theorem Classical222Large.conclusion14 (h : Classical222Large) {A T : Subgroup G}
    (D : ClassicalModel A) (hfam : D.family ≠ .symplectic) (hq : 4 ≤ D.q) (hH : Hyp221 A T) :
    Conclusion222 A T D.q (fun p => Case1 D p ∨ Case4 D p) fun _ => CaseII D T :=
  (h G A T D hq hH).mono (fun _ hp => hp.case14 hfam) fun _ h => h.elim

theorem card_eq_of_regularOn {A J : Subgroup G} {n : ℕ}
    (hreg : RegularOn A J (nonidentity J)) (hcyc : AutCyclic A J n) {j₀ : G} (hj₀ : j₀ ∈ J)
    (hj₀1 : j₀ ≠ 1) : Nat.card J = n + 1 := by
  set N := A ⊓ normalizer (J : Set G) with hN
  let _ : MulAction ↥N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (a : ↥N) (x : G), a • x = (a : G) * x * (a : G)⁻¹ := fun a x => rfl
  have horbit : MulAction.orbit ↥N j₀ = nonidentity J := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      show a • j₀ ∈ nonidentity J
      rw [hsmul]
      refine ⟨(mem_normalizer_iff.mp (mem_inf.mp a.2).2 j₀).mp hj₀, fun h => hj₀1 ?_⟩
      have h' : (a : G)⁻¹ * ((a : G) * j₀ * (a : G)⁻¹) * (a : G) = j₀ := by group
      rw [h, mul_one, inv_mul_cancel] at h'
      exact h'.symm
    · rintro ⟨hx, hx1⟩
      obtain ⟨a, ha, rfl⟩ := hreg.1 j₀ ⟨hj₀, hj₀1⟩ _ ⟨hx, hx1⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hstab : MulAction.stabilizer ↥N j₀ = (A ⊓ centralizer (J : Set G)).subgroupOf N := by
    ext a
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf]
    constructor
    · intro h
      exact mem_inf.mpr ⟨(mem_inf.mp a.2).1, hreg.2 a a.2 j₀ ⟨hj₀, hj₀1⟩ h⟩
    · intro h
      have h1 := mem_centralizer_iff.mp (mem_inf.mp h).2 j₀ hj₀
      rw [← h1, mul_inv_cancel_right]
  have h1 := MulAction.index_stabilizer ↥N j₀
  rw [hstab, horbit] at h1
  have h2 : ((A ⊓ centralizer (J : Set G)).subgroupOf N).index = n := hcyc.1
  rw [h2] at h1
  have hJ : (J : Set G) = insert 1 (nonidentity J) := by
    ext x
    by_cases hx : x = 1
    · subst hx
      simp
    · simp [hx]
  have h3 : (J : Set G).ncard = (nonidentity J).ncard + 1 := by
    rw [hJ, Set.ncard_insert_of_notMem (fun h => h.2 rfl)]
  rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h3
  rw [h3, ← h1]

omit [Finite G] in
theorem sec3V_derived (T : Subgroup G) (g b : G) :
    sec3V (rightConjugate T g⁻¹) (rightConjugate T (b * g⁻¹)) =
      rightConjugate (sec3V T (rightConjugate T b)) g⁻¹ := by
  rw [← sec3V_rightConjugate, rightConjugate_mul]

namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem orderOf_aPart (h32 : Lemma32) {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hρ : t⁻¹ * p ∈ R) : orderOf p = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : Commute t (t⁻¹ * p) := hc.commute_T_R ht hρ
  have h2 : p ^ 2 = 1 := by
    rw [show p = t * (t⁻¹ * p) by group, hcomm.mul_pow, (hc.elemT h32).2 t ht,
      (hc.elemR h32).2 _ hρ, one_mul]
  exact orderOf_eq_prime h2 (hc.aPart_ne_one ht ht1 hρ)

theorem derived {b : G} (hbT : rightConjugate T b ≤ centralizer (T : Set G))
    (hne : rightConjugate T b ≠ T) :
    Sec3 A (rightConjugate T g⁻¹) (rightConjugate T (b * g⁻¹)) (g * b * g⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hc.hyp, hc.swap.sylowR, fun hN => hne ?_, ?_, ?_⟩
  · have hbA : b ∈ normalizer (rightConjugate A g : Set G) :=
      (mem_normalizer_rightConjugate_iff A g b).mpr hN
    have hbK : rightConjugate (rightConjugate (centralizer (A : Set G)) g) b =
        rightConjugate (centralizer (A : Set G)) g := by
      rw [← centralizer_rightConjugate, ← centralizer_rightConjugate,
        (rightConjugate_eq_self_iff _ _).mpr hbA]
    have hTbK : rightConjugate T b ≤ rightConjugate (centralizer (A : Set G)) g := by
      rw [← hbK]
      exact map_mono hc.sylowT.le
    have hp : IsPGroup 2 ↥(T ⊔ rightConjugate T b) :=
      IsPGroup.to_sup_of_normal_left' hc.sylowT.isPGroup (hc.sylowT.isPGroup.map _)
        (hbT.trans (centralizer_le_normalizer _))
    have h1 : T ⊔ rightConjugate T b = T :=
      hc.sylowT.eq_of_le le_sup_left (sup_le hc.sylowT.le hTbK) hp
    have h2 : rightConjugate T b ≤ T := le_sup_right.trans h1.le
    exact eq_of_le_of_card_ge h2 (by rw [rightConjugate_card])
  · have h := AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowT (b * g⁻¹)
    rwa [rightConjugate_mul, show g * (b * g⁻¹) = g * b * g⁻¹ by group] at h
  · rw [centralizer_rightConjugate, ← rightConjugate_mul T b g⁻¹]
    exact map_mono hbT

section Config

variable (I : Inputs74) (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) (D : ClassicalModel A)
  (hfam : D.family ≠ .symplectic) (hq : 4 ≤ D.q)
include I hTy hfam hq

theorem case14 {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) :
    Odd (Nat.card (center ↥A)) ∧ (∀ t' ∈ T, ∀ p' ∈ A, t'⁻¹ * p' ∈ R → p' ∈ jGroup A p) ∧
      Nat.card T ≤ D.q ∧ (Case1 D p ∨ Case4 D p) := by
  have hOut := I.hOut ↥A hc.hyp.standard.1.1 hTy
  obtain ⟨hZ, -, h⟩ :=
    I.h222.conclusion14 D hfam hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)
  rcases h t ht ht1 p (hc.isAPart I.h32 ht hp hρ) with ⟨hle, hT, hI⟩ | hII
  · exact ⟨hZ, fun t' ht' p' hp' hρ' => hle t' ht' p' (hc.isAPart I.h32 ht' hp' hρ'), hT, hI⟩
  · have := hII.2.2
    omega

theorem exists_jData {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) :
    ∃ y : G, JData A R T p (jGroup A p) y := by
  obtain ⟨hZ, hle, -, hI⟩ := hc.case14 I hTy D hfam hq ht ht1 hp hρ
  have hsyl := I.hJS.jSylowAt D hc.hyp.standard.1 hZ hq hp (hc.orderOf_aPart I.h32 ht ht1 hρ)
  rcases hI with ⟨-, hreg, hcyc⟩ | ⟨-, hreg, hcyc⟩
  · exact hc.jData_of ht ht1 hp hρ hle hreg hcyc hsyl
  · exact hc.jData_of ht ht1 hp hρ hle hreg hcyc hsyl

theorem card_jGroup {t p : G} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R) :
    Nat.card (jGroup A p) = D.q := by
  obtain ⟨-, hle, -, hI⟩ := hc.case14 I hTy D hfam hq ht ht1 hp hρ
  have hpJ := hle t ht p hp hρ
  have hp1 := hc.aPart_ne_one ht ht1 hρ
  rcases hI with ⟨-, hreg, hcyc⟩ | ⟨-, hreg, hcyc⟩
  · rw [card_eq_of_regularOn hreg hcyc hpJ hp1]
    omega
  · rw [card_eq_of_regularOn hreg hcyc hpJ hp1]
    omega

theorem exists_pairData :
    ∃ y y' : G, PairData (sec3V R T) R A T (rightConjugate A g) y y' := by
  obtain ⟨t, ht, ht1⟩ := T.bot_or_exists_ne_one.resolve_left hc.T_ne_bot
  obtain ⟨p, hp, hρ⟩ := hc.exists_aPart I.h32 I.h4 I.h34 ht
  obtain ⟨y, hJ⟩ := hc.exists_jData I hTy D hfam hq ht ht1 hp hρ
  have hsw := hc.swap
  obtain ⟨t', ht', ht'1⟩ :=
    (rightConjugate R g⁻¹).bot_or_exists_ne_one.resolve_left hsw.T_ne_bot
  obtain ⟨p', hp', hρ'⟩ := hsw.exists_aPart I.h32 I.h4 I.h34 ht'
  obtain ⟨y', hJ'⟩ := hsw.exists_jData I hTy D hfam hq ht' ht'1 hp' hρ'
  exact ⟨y, _, hc.pairData_RT I.h32 I.h4 I.h34 hJ hJ'⟩

theorem card_inf_sec3V : Nat.card (sec3V R T ⊓ A : Subgroup G) = D.q := by
  obtain ⟨t, ht, ht1⟩ := T.bot_or_exists_ne_one.resolve_left hc.T_ne_bot
  obtain ⟨p, hp, hρ⟩ := hc.exists_aPart I.h32 I.h4 I.h34 ht
  obtain ⟨y, hJ⟩ := hc.exists_jData I hTy D hfam hq ht ht1 hp hρ
  rw [hc.inf_sec3V_eq I.h32 I.h4 I.h34 hJ]
  exact hc.card_jGroup I hTy D hfam hq ht ht1 hp hρ

theorem card_sec3V : Nat.card (sec3V R T) = Nat.card R * D.q := by
  obtain ⟨y, y', hp⟩ := hc.exists_pairData I hTy D hfam hq
  rw [hp.d₁.card_eq, hc.card_inf_sec3V I hTy D hfam hq]

theorem cover : T = sec3V R T ⊓ A ∨ ∀ v ∈ sec3V R T, v ∉ A →
    ∃ x : G, rightConjugate R x ≤ sec3V R T ∧ v ∈ rightConjugate R x := by
  obtain ⟨y, y', hp⟩ := hc.exists_pairData I hTy D hfam hq
  by_cases hX : ∀ x ∈ pairGroup (sec3V R T) A (rightConjugate A g), conjSub x R = R
  · exact Or.inl (hp.eq_of_normalizes hX).1
  · push Not at hX
    obtain ⟨x₀, hx₀, hx₀R⟩ := hX
    obtain ⟨-, hcov⟩ := hp.case_three₁ hx₀ hx₀R
    refine Or.inr fun v hv hvA => ?_
    obtain ⟨x, hx, hvx, -⟩ := (hcov v hv).mp fun h => hvA (mem_inf.mp h).2
    exact ⟨x, rightConjugate_le hp.d₁.le (pairGroup_le hx), hvx⟩

theorem cover_derived {b : G} (hbT : rightConjugate T b ≤ centralizer (T : Set G))
    (hne : rightConjugate T b ≠ T) :
    rightConjugate T b = sec3V T (rightConjugate T b) ⊓ rightConjugate A g ∨
      ∀ v ∈ sec3V T (rightConjugate T b), v ∉ rightConjugate A g →
        ∃ y : G, rightConjugate T y ≤ sec3V T (rightConjugate T b) ∧ v ∈ rightConjugate T y := by
  have hd := hc.derived hbT hne
  have hV := sec3V_derived T g b
  rcases hd.cover I hTy D hfam hq with h1 | h2
  · left
    rw [hV] at h1
    have e1 : rightConjugate (rightConjugate T (b * g⁻¹)) g = rightConjugate T b := by
      rw [rightConjugate_mul, inv_mul_cancel_right]
    have e2 : rightConjugate (rightConjugate (sec3V T (rightConjugate T b)) g⁻¹ ⊓ A) g =
        sec3V T (rightConjugate T b) ⊓ rightConjugate A g := by
      rw [rightConjugate_inf, rightConjugate_inv_rightConjugate]
    calc rightConjugate T b = rightConjugate (rightConjugate T (b * g⁻¹)) g := e1.symm
      _ = rightConjugate (rightConjugate (sec3V T (rightConjugate T b)) g⁻¹ ⊓ A) g := by
        rw [h1]
      _ = _ := e2
  · right
    intro v hv hvA
    have hv' : g * v * g⁻¹ ∈ sec3V (rightConjugate T g⁻¹) (rightConjugate T (b * g⁻¹)) := by
      rw [hV, mem_rightConjugate_iff]
      simpa [mul_assoc] using hv
    have hvA' : g * v * g⁻¹ ∉ A := fun h => hvA ((mem_rightConjugate_iff _ _ _).mpr h)
    obtain ⟨x, hx, hvx⟩ := h2 _ hv' hvA'
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have h := (rightConjugate_le_rightConjugate_iff (x := g)).mpr hx
      rwa [hV, rightConjugate_inv_rightConjugate, rightConjugate_mul, rightConjugate_mul,
        ← mul_assoc] at h
    · rw [rightConjugate_mul, mem_rightConjugate_iff] at hvx
      rw [mem_rightConjugate_iff]
      convert hvx using 1
      group

theorem card_derived {b : G} (hbT : rightConjugate T b ≤ centralizer (T : Set G))
    (hne : rightConjugate T b ≠ T) :
    Nat.card (sec3V T (rightConjugate T b) ⊓ rightConjugate A g : Subgroup G) = D.q ∧
      Nat.card (sec3V T (rightConjugate T b)) = Nat.card T * D.q := by
  have hd := hc.derived hbT hne
  have hV := sec3V_derived T g b
  have h1 := hd.card_inf_sec3V I hTy D hfam hq
  have h2 := hd.card_sec3V I hTy D hfam hq
  rw [hV] at h1 h2
  rw [rightConjugate_card, rightConjugate_card] at h2
  refine ⟨?_, h2⟩
  have e : rightConjugate (sec3V T (rightConjugate T b)) g⁻¹ ⊓ A =
      rightConjugate (sec3V T (rightConjugate T b) ⊓ rightConjugate A g) g⁻¹ := by
    rw [rightConjugate_inf, rightConjugate_rightConjugate_inv]
  rw [e, rightConjugate_card] at h1
  exact h1

end Config

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
