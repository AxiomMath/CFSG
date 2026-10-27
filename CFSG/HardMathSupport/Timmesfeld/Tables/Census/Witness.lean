module

public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.Open

@[expose] def ThreeTwoWitness (G : Type*) [Group G] : Prop :=
  ∃ P : Subgroup G, P ≠ ⊥ ∧ IsPGroup 2 P ∧
    ∃ x : G, orderOf x = 3 ∧ x ∈ Subgroup.normalizer (P : Set G)

variable {G : Type*} [Group G]

theorem ThreeTwoWitness.mk' {P : Subgroup G} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P) {x : G}
    (hx : orderOf x = 3) (hxN : x ∈ Subgroup.normalizer (P : Set G)) : ThreeTwoWitness G :=
  ⟨P, hP, hP2, x, hx, hxN⟩

theorem ThreeTwoWitness.of_mulEquiv {H : Type*} [Group H] (e : G ≃* H) (h : ThreeTwoWitness G) :
    ThreeTwoWitness H := by
  obtain ⟨P, hP, hP2, x, hx, hxN⟩ := h
  refine ⟨P.map e.toMonoidHom, ?_, hP2.map e.toMonoidHom, e x, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective P e.injective]
  · rw [← hx]
    exact orderOf_injective e.toMonoidHom e.injective x
  · rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro g
    have := hxN (e.symm g)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    rw [this]
    simp

theorem ThreeTwoWitness.of_injective {H : Type*} [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : ThreeTwoWitness G) : ThreeTwoWitness H := by
  obtain ⟨P, hP, hP2, x, hx, hxN⟩ := h
  refine ⟨P.map f, ?_, hP2.map f, f x, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective P hf]
  · rw [← hx]
    exact orderOf_injective f hf x
  · rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨x * y * x⁻¹, (hxN y).1 hy, by simp⟩
    · rintro ⟨y, hy, hyg⟩
      refine ⟨x⁻¹ * y * x, (hxN _).2 (by simpa [mul_assoc] using hy), ?_⟩
      have h1 : g = (f x)⁻¹ * (f x * g * (f x)⁻¹) * f x := by group
      rw [h1, ← hyg]
      simp

theorem ThreeTwoWitness.of_commuting {g x : G} (hg : g ^ 2 = 1) (hg1 : g ≠ 1)
    (hx : orderOf x = 3) (hc : Commute g x) : ThreeTwoWitness G := by
  refine ⟨Subgroup.zpowers g, ?_, ?_, x, hx, ?_⟩
  · intro h
    apply hg1
    have : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
    rw [h, Subgroup.mem_bot] at this
    exact this
  · intro y
    obtain ⟨y, i, rfl⟩ := y
    refine ⟨1, Subtype.ext ?_⟩
    show (g ^ i) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  · have hz : ∀ y ∈ Subgroup.zpowers g, x * y * x⁻¹ = y := by
      rintro y ⟨i, rfl⟩
      exact mul_inv_eq_iff_eq_mul.mpr ((hc.zpow_left i).symm.eq)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hz y hy]
      exact hy
    · intro hy
      have h4 : x * (x * y * x⁻¹) * x⁻¹ = x * y * x⁻¹ := hz _ hy
      have h5 : x * y * x⁻¹ = y := by
        calc x * y * x⁻¹ = x⁻¹ * (x * (x * y * x⁻¹) * x⁻¹) * x := by group
          _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [h4]
          _ = y := by group
      rwa [h5] at hy

theorem mem_normalizer_of_conj_le [Finite G] {P : Subgroup G} {x : G}
    (h : ∀ y ∈ P, x * y * x⁻¹ ∈ P) : x ∈ Subgroup.normalizer (P : Set G) := by
  have hle : P.map (MulAut.conj x).toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have hcard : Nat.card P ≤ Nat.card (P.map (MulAut.conj x).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge
  have heq : P.map (MulAut.conj x).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h y
  · intro hy
    rw [← heq] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      have h1 : x * z * x⁻¹ = x * y * x⁻¹ := hzy
      have h2 := mul_right_cancel h1
      exact mul_left_cancel h2
    rwa [this] at hz

theorem ThreeTwoWitness.of_klein [Finite G] (d1 d2 c : G) (hd1 : d1 * d1 = 1) (hd2 : d2 * d2 = 1)
    (hcomm : d1 * d2 = d2 * d1) (hd1ne : d1 ≠ 1) (hc : orderOf c = 3)
    (h1 : c * d1 * c⁻¹ = d2) (h2 : c * d2 * c⁻¹ = d1 * d2) : ThreeTwoWitness G := by
  have e1 : d1 * (d1 * d2) = d2 := by rw [← mul_assoc, hd1, one_mul]
  have e2 : d2 * d1 = d1 * d2 := hcomm.symm
  have e3 : d2 * (d1 * d2) = d1 := by rw [hcomm, ← mul_assoc, hd2, one_mul]
  have e4 : d1 * d2 * d1 = d2 := by rw [hcomm, mul_assoc, hd1, mul_one]
  have e5 : d1 * d2 * d2 = d1 := by rw [mul_assoc, hd2, mul_one]
  have e6 : d1 * d2 * (d1 * d2) = 1 := by rw [← mul_assoc, e4, hd2]
  have i1 : d1⁻¹ = d1 := inv_eq_of_mul_eq_one_right hd1
  have i2 : d2⁻¹ = d2 := inv_eq_of_mul_eq_one_right hd2
  have i12 : (d1 * d2)⁻¹ = d1 * d2 := inv_eq_of_mul_eq_one_right e6
  let P : Subgroup G :=
    { carrier := {y | y = 1 ∨ y = d1 ∨ y = d2 ∨ y = d1 * d2}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at *
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [hd1, hd2, e1, e2, e3, e4, e5, e6]
      one_mem' := Or.inl rfl
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at *
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · rw [i1]; exact Or.inr (Or.inl rfl)
        · rw [i2]; exact Or.inr (Or.inr (Or.inl rfl))
        · rw [i12]; exact Or.inr (Or.inr (Or.inr rfl)) }
  refine ⟨P, ?_, ?_, c, hc, ?_⟩
  · intro h
    have : d1 ∈ P := Or.inr (Or.inl rfl)
    rw [h, Subgroup.mem_bot] at this
    exact hd1ne this
  · intro y
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨y, hy⟩ := y
    have hy' : y = 1 ∨ y = d1 ∨ y = d2 ∨ y = d1 * d2 := hy
    show y ^ 2 ^ 1 = 1
    rw [pow_one, pow_two]
    rcases hy' with rfl | rfl | rfl | rfl <;> simp [hd1, hd2, e6]
  · refine mem_normalizer_of_conj_le fun y hy => ?_
    have hy' : y = 1 ∨ y = d1 ∨ y = d2 ∨ y = d1 * d2 := hy
    show c * y * c⁻¹ = 1 ∨ c * y * c⁻¹ = d1 ∨ c * y * c⁻¹ = d2 ∨ c * y * c⁻¹ = d1 * d2
    rcases hy' with rfl | rfl | rfl | rfl
    · left; simp
    · right; right; left; exact h1
    · right; right; right; exact h2
    · right; left
      calc c * (d1 * d2) * c⁻¹ = (c * d1 * c⁻¹) * (c * d2 * c⁻¹) := by group
        _ = d1 := by rw [h1, h2, e3]

theorem one_le_glaTwoLocalRank_of_witness [Finite G] (h : ThreeTwoWitness G) :
    1 ≤ GLATwoLocalRank 3 G := by
  obtain ⟨P, hP, hP2, x, hx, hxN⟩ := h
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbdd : BddAbove {k | ∃ H : Subgroup G, IsTwoLocal H ∧ pRank 3 H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) H
    have h1 : pRank 3 H < 3 ^ pRank 3 H := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    omega
  have hloc : IsTwoLocal (Subgroup.normalizer (P : Set G)) := ⟨P, hP, hP2, rfl⟩
  have hrank : 1 ≤ pRank 3 (Subgroup.normalizer (P : Set G)) := by
    refine CFSG.SectionRank.le_pRank (by norm_num) (E := Subgroup.zpowers x) ?_ ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact hxN
    · have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
      · rcases a with ⟨_, i, rfl⟩
        rcases b with ⟨_, j, rfl⟩
        exact Subtype.ext (Commute.zpow_zpow_self x i j).eq
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    · rw [Nat.card_zpowers, hx, pow_one]
  exact hrank.trans (le_csSup hbdd ⟨_, hloc, rfl⟩)

theorem threeTwoWitness_of_one_le [Finite G] (h : 1 ≤ GLATwoLocalRank 3 G) : ThreeTwoWitness G := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbdd : BddAbove {k | ∃ H : Subgroup G, IsTwoLocal H ∧ pRank 3 H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) H
    have h1 : pRank 3 H < 3 ^ pRank 3 H := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    omega
  have hne : {k | ∃ H : Subgroup G, IsTwoLocal H ∧ pRank 3 H = k}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank at h
    rw [hne, Nat.sSup_def (by simp)] at h
    simp at h
  obtain ⟨H, ⟨P, hP, hP2, rfl⟩, hk⟩ := Nat.sSup_mem hne hbdd
  have hk1 : 1 ≤ pRank 3 (Subgroup.normalizer (P : Set G)) := by
    rw [hk]
    exact h
  obtain ⟨E, hEH, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (Subgroup.normalizer (P : Set G))
  have h3E : 3 ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := E) 3 h3E
  refine ⟨P, hP, hP2, (y : G), ?_, hEH y.2⟩
  rw [Subgroup.orderOf_coe, hy]

theorem one_le_glaTwoLocalRank_iff [Finite G] : 1 ≤ GLATwoLocalRank 3 G ↔ ThreeTwoWitness G :=
  ⟨threeTwoWitness_of_one_le, one_le_glaTwoLocalRank_of_witness⟩

theorem glaTwoLocalRank_eq_zero_iff [Finite G] :
    GLATwoLocalRank 3 G = 0 ↔ ¬ ThreeTwoWitness G := by
  rw [← one_le_glaTwoLocalRank_iff]
  omega

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
