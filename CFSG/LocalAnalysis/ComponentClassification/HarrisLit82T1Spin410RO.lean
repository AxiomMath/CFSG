module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RE
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RRes

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

theorem card_SL2_spin (K : Type) [Field K] [Finite K] :
    Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, _root_.sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem comm_left_of_comm {G : Type*} [Group G] {a b c y : G} (hb : b * y = y * b)
    (hc : c * y = y * c) (h : a * b * c * y = y * (a * b * c)) : a * y = y * a := by
  have e : a * y * (b * c) = y * a * (b * c) := by
    calc a * y * (b * c) = a * ((y * b) * c) := by simp only [mul_assoc]
      _ = a * (b * (y * c)) := by rw [← hb]; simp only [mul_assoc]
      _ = a * b * c * y := by rw [← hc]; simp only [mul_assoc]
      _ = y * (a * b * c) := h
      _ = y * a * (b * c) := by simp only [mul_assoc]
  exact mul_right_cancel e

theorem comm_mid_of_comm {G : Type*} [Group G] {a b c y : G} (ha : a * y = y * a)
    (hc : c * y = y * c) (h : a * b * c * y = y * (a * b * c)) : b * y = y * b := by
  have e : a * (b * y) * c = a * (y * b) * c := by
    calc a * (b * y) * c = a * b * (y * c) := by simp only [mul_assoc]
      _ = a * b * c * y := by rw [← hc]; simp only [mul_assoc]
      _ = y * (a * b * c) := h
      _ = y * a * b * c := by simp only [mul_assoc]
      _ = a * (y * b) * c := by rw [← ha]; simp only [mul_assoc]
  exact mul_left_cancel (mul_right_cancel e)

theorem comm_right_of_comm {G : Type*} [Group G] {a b c y : G} (ha : a * y = y * a)
    (hb : b * y = y * b) (h : a * b * c * y = y * (a * b * c)) : c * y = y * c := by
  have e : a * b * (c * y) = a * b * (y * c) := by
    calc a * b * (c * y) = y * (a * b * c) := by rw [← h]; simp only [mul_assoc]
      _ = y * a * b * c := by simp only [mul_assoc]
      _ = a * (y * b) * c := by rw [← ha]; simp only [mul_assoc]
      _ = a * b * (y * c) := by rw [← hb]; simp only [mul_assoc]
  exact mul_left_cancel e

theorem le_of_isPerfect_of_index_dvd {G : Type*} [Group G] [Finite G] {C E P : Subgroup G}
    {n : ℕ} (hEn : (E.subgroupOf C).Normal) (hidx : (E.subgroupOf C).index ∣ 2 ^ n)
    (hPC : P ≤ C) (hP : Group.IsPerfect ↥P) : P ≤ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥P →* ↥C ⧸ E.subgroupOf C := (QuotientGroup.mk' _).comp (inclusion hPC) with hφ
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hidx
  have hQ : IsPGroup 2 (↥C ⧸ E.subgroupOf C) :=
    IsPGroup.of_card (n := k) ((index_eq_card _).symm.trans hk)
  have : Group.IsNilpotent (↥C ⧸ E.subgroupOf C) := hQ.isNilpotent
  have hperf : ⁅φ.range, φ.range⁆ = φ.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range φ)
  have hbot : φ.range = ⊥ := by
    by_contra h
    exact (Group.IsSolvable.commutator_lt_of_ne_bot h).ne hperf
  intro x hx
  have h1 : φ ⟨x, hx⟩ = 1 := by
    rw [MonoidHom.range_eq_bot_iff.mp hbot]
    rfl
  exact (QuotientGroup.eq_one_iff (inclusion hPC ⟨x, hx⟩)).mp h1

theorem le_of_coprime_of_index_dvd {G : Type*} [Group G] [Finite G] {C E P : Subgroup G}
    {n : ℕ} (hEn : (E.subgroupOf C).Normal) (hidx : (E.subgroupOf C).index ∣ 2 ^ n)
    (hPC : P ≤ C) (hP : Nat.Coprime 2 (Nat.card P)) : P ≤ E := by
  set φ : ↥P →* ↥C ⧸ E.subgroupOf C := (QuotientGroup.mk' _).comp (inclusion hPC) with hφ
  have hQ : Nat.card (↥C ⧸ E.subgroupOf C) ∣ 2 ^ n := by
    rw [← index_eq_card]
    exact hidx
  have h1 : Nat.card φ.range ∣ Nat.card P := card_range_dvd φ
  have h2 : Nat.card φ.range ∣ 2 ^ n := (card_subgroup_dvd_card φ.range).trans hQ
  have h3 : Nat.card φ.range = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right h1 (hP.pow_left n)).symm h2
  have hbot : φ.range = ⊥ := card_eq_one.mp h3
  intro x hx
  have h1 : φ ⟨x, hx⟩ = 1 := by
    rw [MonoidHom.range_eq_bot_iff.mp hbot]
    rfl
  exact (QuotientGroup.eq_one_iff (inclusion hPC ⟨x, hx⟩)).mp h1

theorem commute_of_mem_of_pPrimeCore_eq_bot {G : Type*} [Group G] [Finite G] {C J : Subgroup G}
    (hJC : J ≤ C) (hJn : (J.subgroupOf C).Normal) (hJO : pPrimeCore 2 ↥J = ⊥) {O : Subgroup ↥C}
    (hOn : O.Normal) (hOc : Nat.Coprime 2 (Nat.card O)) {x : ↥C} (hx : x ∈ O) {y : G}
    (hy : y ∈ J) : (x : G) * y = y * x := by
  have hJn' := (normal_subgroupOf_iff hJC).mp hJn
  set y' : ↥C := ⟨y, hJC hy⟩ with hy'
  have hcO : x * y' * x⁻¹ * y'⁻¹ ∈ O := by
    have e : x * y' * x⁻¹ * y'⁻¹ = x * (y' * x⁻¹ * y'⁻¹) := by group
    rw [e]
    exact mul_mem hx (hOn.conj_mem _ (inv_mem hx) y')
  have hcJ : (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ J := mul_mem (hJn' y x hy x.2) (inv_mem hy)
  set D : Subgroup ↥J := (O.map C.subtype).subgroupOf J with hD
  have hDn : D.Normal := by
    refine ⟨fun d hd g => ?_⟩
    obtain ⟨o, ho, hod⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hd)
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨⟨g, hJC g.2⟩ * o * ⟨g, hJC g.2⟩⁻¹,
      hOn.conj_mem o ho _, ?_⟩)
    rw [map_mul, map_mul, map_inv, hod]
    rfl
  have hDc : Nat.Coprime 2 (Nat.card D) := by
    have h1 : Nat.card D = Nat.card ↥(O.map C.subtype ⊓ J) := by
      rw [← subgroupOf_map_subtype, card_map_of_injective J.subtype_injective]
    have h2 : Nat.card ↥(O.map C.subtype ⊓ J) ∣ Nat.card O := by
      rw [← card_map_of_injective C.subtype_injective]
      exact card_dvd_of_le inf_le_left
    have h3 : Nat.card D ∣ Nat.card O := by
      rw [h1]
      exact h2
    exact Nat.Coprime.coprime_dvd_right h3 hOc
  have hDbot : D = ⊥ := (pPrimeCore_eq_bot_iff (p := 2) (G := ↥J)).mp hJO D hDn hDc
  have hcD : (⟨(x : G) * y * (x : G)⁻¹ * y⁻¹, hcJ⟩ : ↥J) ∈ D :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨_, hcO, rfl⟩)
  rw [hDbot, mem_bot] at hcD
  have hc1 : (x : G) * y * (x : G)⁻¹ * y⁻¹ = 1 := congrArg Subtype.val hcD
  calc (x : G) * y = (x : G) * y * (x : G)⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [hc1, one_mul]

theorem card_range_sl2 {K : Type} [Field K] [Finite K] {G : Type*} [Group G]
    (ρ : SL(2, K) →* G) (hρ : Function.Injective ρ) :
    Nat.card ρ.range = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [← card_SL2_spin K]
  exact (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm

theorem sl2_facts_spin {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) {Y : Type}
    [Group Y] [Finite Y] (hY : IsSLTwoOver (p ^ f) Y) :
    IsQuasisimple Y ∧ Nat.card ↥(center Y) = 2 ∧ pPrimeCore 2 Y = ⊥ := by
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
  obtain ⟨h1, h2, -, h4⟩ := Lemma47.sl2_facts hp hp2 hf h5 hY
  exact ⟨h1, h2, h4⟩

variable {K : Type} [Field K]

theorem finite_spinSeven [Finite K] (h2 : (2 : K) ≠ 0) : Finite (spinGroup (quadOdd 3 K)) := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  exact LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)

theorem isSLTwoOver_range_sl2_spin [Finite K] {q : ℕ} (hK : Nat.card K = q) {G : Type}
    [Group G] (ρ : SL(2, K) →* G) (hρ : Function.Injective ρ) : IsSLTwoOver q ↥ρ.range := by
  let _ := Fintype.ofFinite K
  exact ⟨K, inferInstance, inferInstance, by rw [Fintype.card_eq_nat_card, hK],
    ⟨(MonoidHom.ofInjective hρ).symm⟩⟩

theorem injective_shortSeven : Function.Injective (shortSeven K) :=
  LieType.Steinberg.SpinOdd.shortSL2_injective (oddFrame 3 K) 2 true

section Card

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
  (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

omit h5 in
theorem centralizer_longSL2_true_false :
    centralizer ({(oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false (-1)} :
      Set (spinGroup (quadOdd 3 K))) = centralizer {tSeven K} := by
  obtain ⟨-, -, hzc, -, -, -, -, -, -, h3eq⟩ := spinZ_facts hp hp2 hK
  rw [h3eq]
  exact centralizer_mul_of_mem_center hzc

omit h5 in
theorem spinJ_le_centralizer :
    spinJ₁ K ≤ centralizer {tSeven K} ∧ spinJ₂ K ≤ centralizer {tSeven K} ∧
      spinJ₃ K ≤ centralizer {tSeven K} := by
  refine ⟨range_shortSeven_le_centralizer,
    range_longSL2_le_centralizer _ fin3_zero_ne_one true true, ?_⟩
  rw [← centralizer_longSL2_true_false hp hp2 hK]
  exact range_longSL2_le_centralizer _ fin3_zero_ne_one true false

theorem normal_spinJ :
    ((spinJ₁ K).subgroupOf (centralizer {tSeven K})).Normal ∧
      ((spinJ₂ K).subgroupOf (centralizer {tSeven K})).Normal ∧
        ((spinJ₃ K).subgroupOf (centralizer {tSeven K})).Normal := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h4 := four_le_card_spin hK h5
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  refine ⟨normal_range_shortSeven h2,
    normal_range_longSL2 _ fin3_zero_ne_one hodd h4 hQ true true, ?_⟩
  rw [← centralizer_longSL2_true_false hp hp2 hK]
  exact normal_range_longSL2 _ fin3_zero_ne_one hodd h4 hQ true false

omit hp hp2 h5 in
theorem isSLTwoOver_spinJ :
    IsSLTwoOver (p ^ f) ↥(spinJ₁ K) ∧ IsSLTwoOver (p ^ f) ↥(spinJ₂ K) ∧
      IsSLTwoOver (p ^ f) ↥(spinJ₃ K) :=
  ⟨isSLTwoOver_range_sl2_spin hK _ injective_shortSeven,
    isSLTwoOver_range_longSL2 _ fin3_zero_ne_one hK true true,
    isSLTwoOver_range_longSL2 _ fin3_zero_ne_one hK true false⟩

theorem pPrimeCore_spinJ :
    pPrimeCore 2 ↥(spinJ₁ K) = ⊥ ∧ pPrimeCore 2 ↥(spinJ₂ K) = ⊥ ∧
      pPrimeCore 2 ↥(spinJ₃ K) = ⊥ := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  obtain ⟨h1, h2, h3⟩ := isSLTwoOver_spinJ (K := K) hK
  exact ⟨(sl2_facts_spin hp hp2 h5 h1).2.2, (sl2_facts_spin hp hp2 h5 h2).2.2,
    (sl2_facts_spin hp hp2 h5 h3).2.2⟩

theorem card_ker_spinMul : Nat.card (spinMul (four_le_card_spin hK h5)).ker = 2 := by
  obtain ⟨hzz, hz1, hzc, htt, -, -, hz1', ht2', hzt3, -⟩ := spinZ_facts hp hp2 hK
  set w : (spinJ₁ K × spinJ₂ K) × spinJ₃ K :=
    ((⟨spinZ K, hz1'⟩, ⟨tSeven K, ht2'⟩), ⟨spinZ K * tSeven K, hzt3⟩) with hw
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
  have hww : w * w = 1 :=
    Prod.ext (Prod.ext (Subtype.ext hzz) (Subtype.ext htt)) (Subtype.ext hztzt)
  have hw1 : w ≠ 1 := fun h => hz1 (congrArg (fun v => (v.1.1 : spinGroup (quadOdd 3 K))) h)
  have hker : (spinMul (four_le_card_spin hK h5)).ker = zpowers w := by
    ext x
    rw [mem_ker_spinMul_iff hp hp2 hK h5 (four_le_card_spin hK h5)]
    constructor
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact mem_zpowers _
    · exact eq_one_or_eq_of_mem_zpowers_of_mul_self hww
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hker, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hww) hw1

theorem card_spinE : 2 * Nat.card (spinE K) = (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 3 := by
  have h := card_ker_mul_card_range (spinMul (four_le_card_spin hK h5))
  rw [card_ker_spinMul hp hp2 hK h5, range_spinMul, Nat.card_prod, Nat.card_prod,
    card_range_sl2 _ injective_shortSeven,
    card_range_sl2 _ (longSL2_injective _ fin3_zero_ne_one true true),
    card_range_sl2 _ (longSL2_injective _ fin3_zero_ne_one true false)] at h
  rw [h]
  ring

omit h5 in
theorem spinE_le_centralizer : spinE K ≤ centralizer {tSeven K} := by
  obtain ⟨h1, h2, h3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  exact sup_le (sup_le h1 h2) h3

theorem normal_spinE : ((spinE K).subgroupOf (centralizer {tSeven K})).Normal := by
  obtain ⟨h1, h2, h3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, n2, n3⟩ := normal_spinJ (K := K) hp hp2 hK h5
  rw [subgroupOf_sup (sup_le h1 h2) h3, subgroupOf_sup h1 h2]
  exact Subgroup.sup_normal _ _

theorem index_spinE_dvd : ((spinE K).subgroupOf (centralizer {tSeven K})).index ∣ 2 ^ 4 := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hC := card_centralizer_tSeven_dvd (two_ne_zero_spin hp hp2 hK)
  have hE := card_spinE hp hp2 hK h5
  have hEC := card_mul_index ((spinE K).subgroupOf (centralizer {tSeven K}))
  rw [Nat.card_congr (subgroupOfEquivOfLe (spinE_le_centralizer hp hp2 hK)).toEquiv] at hEC
  have hpos : 0 < Nat.card (spinE K) := Nat.card_pos
  have h16 : 8 * Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 3 = Nat.card (spinE K) * 2 ^ 4 := by
    rw [mul_assoc, ← mul_pow, ← hE]
    ring
  rw [← hEC, h16] at hC
  exact Nat.dvd_of_mul_dvd_mul_left hpos hC

theorem le_spinE_of_isPerfect {P : Subgroup (spinGroup (quadOdd 3 K))}
    (hPC : P ≤ centralizer {tSeven K}) (hP : Group.IsPerfect ↥P) : P ≤ spinE K := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  exact le_of_isPerfect_of_index_dvd (normal_spinE hp hp2 hK h5) (index_spinE_dvd hp hp2 hK h5)
    hPC hP

theorem le_spinE_of_coprime {P : Subgroup (spinGroup (quadOdd 3 K))}
    (hPC : P ≤ centralizer {tSeven K}) (hP : Nat.Coprime 2 (Nat.card P)) : P ≤ spinE K := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  exact le_of_coprime_of_index_dvd (normal_spinE hp hp2 hK h5) (index_spinE_dvd hp hp2 hK h5)
    hPC hP

theorem mul_self_eq_one_of_commute {x : spinGroup (quadOdd 3 K)} (hx : x ∈ spinE K)
    (h1 : ∀ a ∈ spinJ₁ K, x * a = a * x) (h2 : ∀ b ∈ spinJ₂ K, x * b = b * x)
    (h3 : ∀ c ∈ spinJ₃ K, x * c = c * x) : x * x = 1 := by
  obtain ⟨hzz, -, hzc, htt, -, -, -, -, -, h3eq⟩ := spinZ_facts hp hp2 hK
  have h4 := four_le_card_spin hK h5
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
  rw [← range_spinMul h4] at hx
  obtain ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩, rfl⟩ := hx
  rw [spinMul_apply] at h1 h2 h3 ⊢
  change a * b * c * (a * b * c) = 1
  change ∀ a' ∈ spinJ₁ K, a * b * c * a' = a' * (a * b * c) at h1
  change ∀ b' ∈ spinJ₂ K, a * b * c * b' = b' * (a * b * c) at h2
  change ∀ c' ∈ spinJ₃ K, a * b * c * c' = c' * (a * b * c) at h3
  have hac : ∀ a' ∈ spinJ₁ K, a * a' = a' * a := fun a' ha' =>
    comm_left_of_comm (commute_spinJ₁_spinJ₂ ha' hb).symm (commute_spinJ₁_spinJ₃ ha' hc).symm
      (h1 a' ha')
  have hbc : ∀ b' ∈ spinJ₂ K, b * b' = b' * b := fun b' hb' =>
    comm_mid_of_comm (commute_spinJ₁_spinJ₂ ha hb') (commute_spinJ₂_spinJ₃ h4 hb' hc).symm
      (h2 b' hb')
  have hcc : ∀ c' ∈ spinJ₃ K, c * c' = c' * c := fun c' hc' =>
    comm_right_of_comm (commute_spinJ₁_spinJ₃ ha hc') (commute_spinJ₂_spinJ₃ h4 hb hc')
      (h3 c' hc')
  have ha2 : a * a = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hzz
      (mem_zpowers_of_commute_spinJ₁ hp hp2 hK h5 ha hac) with rfl | rfl
    · exact mul_one 1
    · exact hzz
  have hb2 : b * b = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self htt
      (mem_zpowers_of_commute_spinJ₂ hp hp2 hK h5 hb hbc) with rfl | rfl
    · exact mul_one 1
    · exact htt
  have hc2 : c * c = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hztzt
      (h3eq ▸ mem_zpowers_of_commute_spinJ₃ hp hp2 hK h5 hc hcc) with rfl | rfl
    · exact mul_one 1
    · exact hztzt
  have hab : Commute a b := commute_spinJ₁_spinJ₂ ha hb
  have hac' : Commute a c := commute_spinJ₁_spinJ₃ ha hc
  have hbc' : Commute b c := commute_spinJ₂_spinJ₃ h4 hb hc
  rw [← pow_two, (hac'.mul_left hbc').mul_pow, hab.mul_pow]
  simp only [pow_two, ha2, hb2, hc2, one_mul]

theorem pPrimeCore_centralizer_tSeven :
    pPrimeCore 2 ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K)))) = ⊥ := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, n2, n3⟩ := normal_spinJ (K := K) hp hp2 hK h5
  obtain ⟨o1, o2, o3⟩ := pPrimeCore_spinJ (K := K) hp hp2 hK h5
  rw [pPrimeCore_eq_bot_iff]
  intro O hOn hOc
  have hO'c : Nat.Coprime 2 (Nat.card (O.map (centralizer {tSeven K}).subtype)) := by
    rwa [card_map_of_injective (subtype_injective _)]
  have hO'E := le_spinE_of_coprime hp hp2 hK h5 (map_subtype_le O) hO'c
  rw [eq_bot_iff]
  intro x hx
  have hxE : (x : spinGroup (quadOdd 3 K)) ∈ spinE K := hO'E ⟨x, hx, rfl⟩
  have hxx : (x : spinGroup (quadOdd 3 K)) * x = 1 := mul_self_eq_one_of_commute hp hp2 hK h5 hxE
    (fun _ ha => commute_of_mem_of_pPrimeCore_eq_bot l1 n1 o1 hOn hOc hx ha)
    (fun _ hb => commute_of_mem_of_pPrimeCore_eq_bot l2 n2 o2 hOn hOc hx hb)
    (fun _ hc => commute_of_mem_of_pPrimeCore_eq_bot l3 n3 o3 hOn hOc hx hc)
  have hxx' : x ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext hxx
  have ho : orderOf x ∣ Nat.gcd 2 (Nat.card O) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxx') (Subgroup.orderOf_dvd_natCard O hx)
  rw [Nat.Coprime.gcd_eq_one hOc, Nat.dvd_one, orderOf_eq_one_iff] at ho
  exact (mem_bot).mpr ho

end Card

end CFSG.ComponentClassification.HarrisLit.T1
