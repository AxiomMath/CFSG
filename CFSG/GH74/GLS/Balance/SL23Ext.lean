module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup
open scoped MatrixGroups commutatorElement

namespace SL23

abbrev S3 : Type := SL(2, ZMod 3)

theorem S3_pow_twelve : ∀ s : S3, s ^ 12 = 1 := by decide +kernel

theorem S3_mul_pow_four : ∀ a b : S3, a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by decide +kernel

theorem S3_card : Nat.card S3 = 24 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

@[expose] def Q8 : Subgroup S3 where
  carrier := {s | s ^ 4 = 1}
  one_mem' := one_pow 4
  mul_mem' := fun {a b} ha hb => S3_mul_pow_four a b ha hb
  inv_mem' := fun {a} ha => by
    show a⁻¹ ^ 4 = 1
    rw [inv_pow]
    have : a ^ 4 = 1 := ha
    rw [this, inv_one]

theorem mem_Q8 {s : S3} : s ∈ Q8 ↔ s ^ 4 = 1 := Iff.rfl

instance Q8_normal : Q8.Normal where
  conj_mem n hn g := by
    rw [mem_Q8] at hn ⊢
    rw [conj_pow, hn, mul_one, mul_inv_cancel]

theorem card_Q8 : Nat.card Q8 = 8 := by
  have h : Nat.card Q8 = Nat.card {s : S3 // s ^ 4 = 1} := Nat.card_congr (Equiv.refl _)
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel


theorem S3_comm_gen : ∀ t : S3, t ^ 3 = 1 → t ≠ 1 → ∀ q : S3, q ^ 4 = 1 →
    ∃ h₁ : S3, h₁ ^ 4 = 1 ∧ ∃ h₂ : S3, h₂ ^ 4 = 1 ∧ q = ⁅h₁, t⁆ * ⁅h₂, t⁆ := by
  decide +kernel

theorem S3_gen_Q8 : ∀ t a q : S3, t ^ 3 = 1 → t ≠ 1 → a ^ 4 = 1 → a ^ 2 ≠ 1 → q ^ 4 = 1 →
    ∃ u ∈ [1, a, a⁻¹, t * a * t⁻¹, (t * a * t⁻¹)⁻¹, t * (t * a * t⁻¹) * t⁻¹,
        (t * (t * a * t⁻¹) * t⁻¹)⁻¹],
    ∃ v ∈ [1, a, a⁻¹, t * a * t⁻¹, (t * a * t⁻¹)⁻¹, t * (t * a * t⁻¹) * t⁻¹,
        (t * (t * a * t⁻¹) * t⁻¹)⁻¹],
      q = u * v := by
  decide +kernel

theorem S3_normal_closure :
    ∀ g : S3, g ^ 2 ≠ 1 → ∀ q : S3, q ^ 4 = 1 →
      ∃ h₁ : S3, h₁ ^ 3 = 1 ∧ ∃ h₂ : S3, h₂ ^ 3 = 1 ∧ q = ⁅h₁, g⁆ * ⁅h₂, g⁆ := by
  decide +kernel

theorem S3_prod_three : ∀ s : S3, ∃ a : S3, a ^ 3 = 1 ∧ ∃ b : S3, b ^ 3 = 1 ∧
    ∃ c : S3, c ^ 3 = 1 ∧ s = a * b * c := by
  decide +kernel

theorem S3_central : ∀ s : S3, s ^ 2 = 1 → ∀ g : S3, g * s = s * g := by decide +kernel

theorem S3_nonab : ∃ a b : S3, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ a * b ≠ b * a := by decide +kernel

theorem S3_exists_order_three : ∃ t : S3, t ^ 3 = 1 ∧ t ≠ 1 := by decide +kernel

structure Ext (G : Type*) [Group G] where
  π : G →* S3
  surj : Function.Surjective π
  odd : Odd (Nat.card π.ker)

section Elementary

variable {G : Type*} [Group G]

theorem eq_one_of_odd_of_two_pow {g : G} (hg : Odd (orderOf g)) {k : ℕ} (h : g ^ 2 ^ k = 1) :
    g = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : Nat.Coprime (orderOf g) (2 ^ k) := Nat.Coprime.pow_right k hg.coprime_two_right
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem pow_four_of_pow_two_pow {s : S3} {k : ℕ} (h : s ^ 2 ^ k = 1) : s ^ 4 = 1 := by
  have h1 : orderOf s ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf s ∣ 12 := orderOf_dvd_of_pow_eq_one (S3_pow_twelve s)
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h3 : orderOf s ∣ 4 := by
    have hc : Nat.Coprime (orderOf s) 3 := by
      rw [hjeq]; exact Nat.Coprime.pow_left j (by norm_num)
    exact hc.dvd_of_dvd_mul_right (show orderOf s ∣ 4 * 3 from h2)
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem exists_pow_eq_one_of_mem {T : Subgroup G} (hT : IsPGroup 2 T) {a : G} (ha : a ∈ T) :
    ∃ k : ℕ, a ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨a, ha⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem comm_mem_of_mem_normalizer {T : Subgroup G} {a b : G} (ha : a ∈ T)
    (hb : b ∈ normalizer (T : Set G)) : ⁅a, b⁆ ∈ T := by
  have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact mul_mem ha ((Subgroup.mem_normalizer_iff.mp hb a⁻¹).mp (inv_mem ha))

theorem comm_le_of_le_normalizer {T U : Subgroup G} (h : U ≤ normalizer (T : Set G)) :
    ⁅T, U⁆ ≤ T :=
  Subgroup.commutator_le.mpr fun _ ha _ hb => comm_mem_of_mem_normalizer ha (h hb)

theorem mem_of_mul_odd {K : Subgroup G} {a k y : G} (ha : a ∈ K) (hk : k ∈ normalizer (K : Set G))
    (hy : y = a * k) (hodd : Odd (orderOf k)) {j : ℕ} (hyj : y ^ 2 ^ j = 1) : y ∈ K := by
  have key : ∀ n : ℕ, ∃ b ∈ K, y ^ n = b * k ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem K, by simp⟩
    | succ n ih =>
      obtain ⟨b, hb, hbn⟩ := ih
      refine ⟨b * (k ^ n * a * (k ^ n)⁻¹), mul_mem hb ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (pow_mem hk n) a).mp ha
      · rw [pow_succ, hbn, hy, pow_succ]; group
  obtain ⟨b, hb, hbd⟩ := key (orderOf k)
  rw [pow_orderOf_eq_one, mul_one] at hbd
  have hcop : Nat.Coprime (orderOf k) (orderOf y) := by
    have h1 : orderOf y ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hyj
    exact Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right j hodd.coprime_two_right)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, hbd]
  exact pow_mem hb m

end Elementary

namespace Ext

variable {G : Type*} [Group G] (E : Ext G)

include E

theorem odd_orderOf_of_mem_ker {g : G} (hg : g ∈ E.π.ker) : Odd (orderOf g) := by
  have h : orderOf (⟨g, hg⟩ : E.π.ker) ∣ Nat.card E.π.ker := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h
  exact Odd.of_dvd_nat E.odd h

theorem eq_one_of_mem_ker_of_two_pow {g : G} (hg : g ∈ E.π.ker) {k : ℕ} (h : g ^ 2 ^ k = 1) :
    g = 1 :=
  eq_one_of_odd_of_two_pow (E.odd_orderOf_of_mem_ker hg) h

theorem pow_four_of_two_pow {g : G} {k : ℕ} (h : g ^ 2 ^ k = 1) : E.π g ^ 4 = 1 :=
  pow_four_of_pow_two_pow (k := k) (by rw [← map_pow, h, map_one])

theorem inj_on {T : Subgroup G} (hT : IsPGroup 2 T) {a b : G} (ha : a ∈ T) (hb : b ∈ T)
    (h : E.π a = E.π b) : a = b := by
  have hc : a⁻¹ * b ∈ T := mul_mem (inv_mem ha) hb
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem hT hc
  have hker : a⁻¹ * b ∈ E.π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have := E.eq_one_of_mem_ker_of_two_pow hker hk
  exact (inv_mul_eq_one.mp this)

theorem map_le_Q8 {T : Subgroup G} (hT : IsPGroup 2 T) : T.map E.π ≤ Q8 := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem hT ha
  exact E.pow_four_of_two_pow hk

theorem card_map {T : Subgroup G} (hT : IsPGroup 2 T) : Nat.card (T.map E.π) = Nat.card T := by
  have hinj : Function.Injective (E.π.comp T.subtype) := fun a b hab =>
    Subtype.ext (E.inj_on hT a.2 b.2 hab)
  have h := Nat.card_range_of_injective hinj
  have h2 : (E.π.comp T.subtype).range = T.map E.π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h2]
  exact h

theorem card_le {T : Subgroup G} (hT : IsPGroup 2 T) : Nat.card T ≤ 8 := by
  rw [← E.card_map hT, ← card_Q8]
  exact Subgroup.card_le_of_le (E.map_le_Q8 hT)


theorem map_eq_Q8 {T : Subgroup G} [Finite G] (hT : IsPGroup 2 T) (hc : Nat.card T = 8) :
    T.map E.π = Q8 := by
  apply Subgroup.eq_of_le_of_card_ge (E.map_le_Q8 hT)
  rw [E.card_map hT, hc, card_Q8]

theorem exists_mem_of_mem_Q8 [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T) (hc : Nat.card T = 8)
    {q : S3} (hq : q ∈ Q8) : ∃ a ∈ T, E.π a = q := by
  have h := E.map_eq_Q8 hT hc
  rw [← h] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  exact ⟨a, ha, rfl⟩

theorem card_eq : Nat.card G = Nat.card E.π.ker * 24 := by
  have h := Subgroup.card_ker_mul_card_of_surjective E.surj
  rw [← h, S3_card]

theorem comm_mem_ker_of_sq {g : G} (hg : E.π g ^ 2 = 1) (v : G) : ⁅g, v⁆ ∈ E.π.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (S3_central _ hg _).symm

section Finite

variable [Finite G]

theorem card_sylow (P : Sylow 2 G) : Nat.card P = 8 := by
  rw [Sylow.card_eq_multiplicity, E.card_eq]
  have hodd : ¬ 2 ∣ Nat.card E.π.ker := by
    rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr E.odd
  have hne : Nat.card E.π.ker ≠ 0 := Nat.card_pos.ne'
  have h24 : Nat.factorization 24 2 = 3 := by
    have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow,
      Nat.Prime.factorization Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]
  rw [Nat.factorization_mul hne (by norm_num), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, h24]
  norm_num

theorem commutator_eq {P : Subgroup G} (hP : IsPGroup 2 P) (hc : Nat.card P = 8) {w : G}
    (hw : w ∈ normalizer (P : Set G)) (h1 : E.π w ≠ 1) (h3 : E.π w ^ 3 = 1) :
    ⁅P, zpowers w⁆ = P := by
  apply le_antisymm
  · exact comm_le_of_le_normalizer (Subgroup.zpowers_le.mpr hw)
  · intro p hp
    have hq : E.π p ∈ Q8 := E.map_le_Q8 hP ⟨p, hp, rfl⟩
    obtain ⟨h₁, hh₁, h₂, hh₂, hh⟩ := S3_comm_gen (E.π w) h3 h1 (E.π p) hq
    obtain ⟨a₁, ha₁, rfl⟩ := E.exists_mem_of_mem_Q8 hP hc hh₁
    obtain ⟨a₂, ha₂, rfl⟩ := E.exists_mem_of_mem_Q8 hP hc hh₂
    have hmem : ⁅a₁, w⁆ * ⁅a₂, w⁆ ∈ ⁅P, zpowers w⁆ :=
      mul_mem (Subgroup.commutator_mem_commutator ha₁ (Subgroup.mem_zpowers w))
        (Subgroup.commutator_mem_commutator ha₂ (Subgroup.mem_zpowers w))
    have hmemP : ⁅a₁, w⁆ * ⁅a₂, w⁆ ∈ P :=
      comm_le_of_le_normalizer (Subgroup.zpowers_le.mpr hw) hmem
    have himg : E.π (⁅a₁, w⁆ * ⁅a₂, w⁆) = E.π p := by
      rw [hh, map_mul, map_commutatorElement, map_commutatorElement]
    have := E.inj_on hP hmemP hp himg
    rw [← this]
    exact hmem

omit [Finite G] in
theorem w3_comm {P : Subgroup G} (hP : IsPGroup 2 P) {w : G} (hw : w ∈ normalizer (P : Set G))
    (h3 : E.π w ^ 3 = 1) {a : G} (ha : a ∈ P) : w ^ 3 * a = a * w ^ 3 := by
  have hw3 : w ^ 3 ∈ normalizer (P : Set G) := pow_mem hw 3
  have hcm : ⁅a, w ^ 3⁆ ∈ P := comm_mem_of_mem_normalizer ha hw3
  have h1 : E.π ⁅a, w ^ 3⁆ = E.π 1 := by
    rw [map_commutatorElement, map_pow, h3, commutatorElement_one_right, map_one]
  have h2 := E.inj_on hP hcm (one_mem P) h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

theorem nonab {P : Subgroup G} (hP : IsPGroup 2 P) (hc : Nat.card P = 8) :
    ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  obtain ⟨q₁, q₂, h₁, h₂, hne⟩ := S3_nonab
  obtain ⟨a, ha, rfl⟩ := E.exists_mem_of_mem_Q8 hP hc h₁
  obtain ⟨b, hb, rfl⟩ := E.exists_mem_of_mem_Q8 hP hc h₂
  refine ⟨a, ha, b, hb, fun h => hne ?_⟩
  rw [← map_mul, ← map_mul, h]

theorem exists_w (P : Sylow 2 G) : ∃ w ∈ normalizer ((P : Subgroup G) : Set G),
    (∃ k : ℕ, orderOf w = 3 ^ k) ∧ E.π w ≠ 1 ∧ E.π w ^ 3 = 1 := by
  set G2 : Subgroup G := Q8.comap E.π with hG2
  have : G2.Normal := Subgroup.Normal.comap inferInstance E.π
  have hPG2 : (P : Subgroup G) ≤ G2 := by
    intro a ha
    exact E.map_le_Q8 P.isPGroup' ⟨a, ha, rfl⟩
  have hF := Sylow.normalizer_sup_eq_top' P hPG2
  obtain ⟨t, ht3, ht1⟩ := S3_exists_order_three
  obtain ⟨g, rfl⟩ := E.surj t
  have hg : g ∈ normalizer (P : Set G) ⊔ G2 := by rw [hF]; trivial
  obtain ⟨n, hn0, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hn : n ∈ normalizer ((P : Subgroup G) : Set G) := hn0
  have hm4 : E.π m ^ 4 = 1 := hm
  have hn4 : E.π n ^ 4 ≠ 1 := by
    intro h
    have h4 : (E.π n * E.π m) ^ 4 = 1 := S3_mul_pow_four _ _ h hm4
    rw [← map_mul] at h4
    apply ht1
    calc E.π (n * m) = E.π (n * m) ^ 4 * (E.π (n * m) ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, ht3]; simp
  set n' := n ^ 4 with hn'
  have hn'N : n' ∈ normalizer ((P : Subgroup G) : Set G) := pow_mem hn 4
  have hπn'1 : E.π n' ≠ 1 := by rw [hn', map_pow]; exact hn4
  have hπn'3 : E.π n' ^ 3 = 1 := by
    rw [hn', map_pow, ← pow_mul]; exact S3_pow_twelve _
  have hord : orderOf n' ≠ 0 := (orderOf_pos n').ne'
  obtain ⟨b, M, hM3, hbM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord 3 (by norm_num)
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hbM
    exact hord hbM
  refine ⟨n' ^ M, pow_mem hn'N M, ⟨b, ?_⟩, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd hM0 (by rw [hbM]; exact dvd_mul_left _ _), hbM,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hM0)]
  · intro h
    rw [map_pow] at h
    have h3 : orderOf (E.π n') = 3 := orderOf_eq_prime hπn'3 hπn'1
    have : 3 ∣ M := by rw [← h3]; exact orderOf_dvd_of_pow_eq_one h
    exact hM3 this
  · rw [map_pow, ← pow_mul, mul_comm, pow_mul, hπn'3, one_pow]

theorem T_analysis {T : Subgroup G} (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥) {w : G}
    (hw : w ∈ normalizer (T : Set G)) (h1 : E.π w ≠ 1) (h3 : E.π w ^ 3 = 1)
    (hc : ⁅T, zpowers w⁆ = T) : Nat.card T = 8 ∧ ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a := by
  have h2 : ∃ a ∈ T, E.π a ^ 2 ≠ 1 := by
    by_contra hcon0
    have hcon : ∀ a ∈ T, E.π a ^ 2 = 1 := fun a ha => by
      by_contra h
      exact hcon0 ⟨a, ha, h⟩
    apply hT0
    rw [← hc, eq_bot_iff]
    refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
    have h1' : ⁅a, b⁆ ∈ T :=
      comm_mem_of_mem_normalizer ha ((Subgroup.zpowers_le.mpr hw) hb)
    have h2' : E.π ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (S3_central _ (hcon a ha) _).symm
    have := E.inj_on hT h1' (one_mem T) (by rw [h2', map_one])
    simp [this]
  obtain ⟨a, ha, ha2⟩ := h2
  have ha4 : E.π a ^ 4 = 1 := E.map_le_Q8 hT ⟨a, ha, rfl⟩
  have hw1 : w * a * w⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hw a).mp ha
  have hw2 : w * (w * a * w⁻¹) * w⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hw _).mp hw1
  have hQ : Q8 ≤ T.map E.π := by
    intro q hq
    obtain ⟨u, hu, v, hv, huv⟩ := S3_gen_Q8 (E.π w) (E.π a) q h3 h1 ha4 ha2 hq
    have hmem : ∀ z ∈ [(1 : S3), E.π a, (E.π a)⁻¹, E.π w * E.π a * (E.π w)⁻¹,
        (E.π w * E.π a * (E.π w)⁻¹)⁻¹, E.π w * (E.π w * E.π a * (E.π w)⁻¹) * (E.π w)⁻¹,
        (E.π w * (E.π w * E.π a * (E.π w)⁻¹) * (E.π w)⁻¹)⁻¹], z ∈ T.map E.π := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      have hmap : ∀ x ∈ T, E.π x ∈ T.map E.π := fun x hx => ⟨x, hx, rfl⟩
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hmap a ha
      · exact inv_mem (hmap a ha)
      · have := hmap _ hw1; simpa [map_mul, map_inv] using this
      · have := inv_mem (hmap _ hw1); simpa [map_mul, map_inv] using this
      · have := hmap _ hw2; simpa [map_mul, map_inv] using this
      · have := inv_mem (hmap _ hw2); simpa [map_mul, map_inv] using this
    rw [huv]
    exact mul_mem (hmem u hu) (hmem v hv)
  have hEq : T.map E.π = Q8 := le_antisymm (E.map_le_Q8 hT) hQ
  have hcard : Nat.card T = 8 := by rw [← E.card_map hT, hEq, card_Q8]
  refine ⟨hcard, ?_⟩
  exact E.nonab hT hcard

theorem exists_three_elt_lift {a : S3} (ha : a ^ 3 = 1) :
    ∃ u : G, (∃ k : ℕ, u ^ 3 ^ k = 1) ∧ E.π u = a := by
  obtain ⟨u₀, rfl⟩ := E.surj a
  have hord : orderOf u₀ ≠ 0 := (orderOf_pos u₀).ne'
  obtain ⟨b, M, hM3, hbM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord 3 (by norm_num)
  refine ⟨u₀ ^ (M * M), ⟨b, ?_⟩, ?_⟩
  · rw [← pow_mul]
    have : M * M * 3 ^ b = (3 ^ b * M) * M := by ring
    rw [this, pow_mul, ← hbM, pow_orderOf_eq_one, one_pow]
  · rw [map_pow]
    have h1 : M * M % 3 = 1 := by
      have : M % 3 = 1 ∨ M % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [pow_eq_pow_mod _ ha, h1, pow_one]

theorem gen3 {H : Subgroup G} (hker : ∀ g ∈ E.π.ker, g ∈ H)
    (h3 : ∀ g : G, (∃ k : ℕ, g ^ 3 ^ k = 1) → g ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨a, ha, b, hb, c, hc, hg⟩ := S3_prod_three (E.π g)
  obtain ⟨ua, hua, hπa⟩ := E.exists_three_elt_lift ha
  obtain ⟨ub, hub, hπb⟩ := E.exists_three_elt_lift hb
  obtain ⟨uc, huc, hπc⟩ := E.exists_three_elt_lift hc
  have hk : (ua * ub * uc)⁻¹ * g ∈ E.π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hπa, hπb, hπc, ← hg,
      inv_mul_cancel]
  have := mul_mem (mul_mem (mul_mem (h3 _ hua) (h3 _ hub)) (h3 _ huc)) (hker _ hk)
  rwa [mul_inv_cancel_left] at this

omit [Finite G] in
theorem two_elt_mem_of_normal {M : Subgroup G} [M.Normal] {m : G} (hm : m ∈ M)
    (hm2 : E.π m ^ 2 ≠ 1) {y : G} {j : ℕ} (hy : y ^ 2 ^ j = 1) : y ∈ M := by
  have hQ : ∀ q ∈ Q8, ∃ m' ∈ M, E.π m' = q := by
    intro q hq
    obtain ⟨h₁, -, h₂, -, hh⟩ := S3_normal_closure _ hm2 q hq
    obtain ⟨g₁, rfl⟩ := E.surj h₁
    obtain ⟨g₂, rfl⟩ := E.surj h₂
    have hc : ∀ g : G, ⁅g, m⁆ ∈ M := fun g => by
      rw [commutatorElement_def]
      exact mul_mem (Subgroup.Normal.conj_mem inferInstance m hm g) (inv_mem hm)
    refine ⟨⁅g₁, m⁆ * ⁅g₂, m⁆, mul_mem (hc g₁) (hc g₂), ?_⟩
    rw [map_mul, map_commutatorElement, map_commutatorElement, ← hh]
  have hy4 : E.π y ∈ Q8 := E.pow_four_of_two_pow hy
  obtain ⟨m', hm', hπ⟩ := hQ _ hy4
  have hk : m'⁻¹ * y ∈ E.π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, inv_mul_cancel]
  have hkN : m'⁻¹ * y ∈ normalizer (M : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact Subgroup.mem_top _
  exact mem_of_mul_odd hm' hkN (by group) (E.odd_orderOf_of_mem_ker hk) hy

theorem exists_mul_of_two_elt {P : Subgroup G} (hP : IsPGroup 2 P) (hc : Nat.card P = 8) {y : G}
    {j : ℕ} (hy : y ^ 2 ^ j = 1) : ∃ a ∈ P, ∃ k ∈ E.π.ker, y = a * k := by
  obtain ⟨a, ha, hπ⟩ := E.exists_mem_of_mem_Q8 hP hc (E.pow_four_of_two_pow hy)
  refine ⟨a, ha, a⁻¹ * y, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, inv_mul_cancel]

end Finite

end Ext

end SL23

end CFSG.GH74.GLS.Balance
