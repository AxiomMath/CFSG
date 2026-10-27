module

public import CFSG.ClassicalInvolution.Q3.TL4D1Facts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G]

abbrev oddGen (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {g : G | g ∈ X ∧ Odd (orderOf g)}

structure D1Pack (X : Subgroup G) : Prop where
  normal : ∀ N : Subgroup G, N ≤ X → (∀ x ∈ X, ∀ y ∈ N, x * y * x⁻¹ ∈ N) →
    IsPGroup 2 ↥N ∨ N = X
  perfect : ⁅X, X⁆ = X
  odd : X ≤ oddGen X
  not_two : ¬ IsPGroup 2 ↥X

theorem oddGen_le (X : Subgroup G) : oddGen X ≤ X :=
  Subgroup.closure_le _ |>.mpr fun _ hg => hg.1

theorem mem_oddGen {X : Subgroup G} {g : G} (hg : g ∈ X) (ho : Odd (orderOf g)) : g ∈ oddGen X :=
  Subgroup.subset_closure ⟨hg, ho⟩

theorem conj_mem_oddGen {X : Subgroup G} {x : G} (hx : x ∈ X) {y : G} (hy : y ∈ oddGen X) :
    x * y * x⁻¹ ∈ oddGen X := by
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
    refine mem_oddGen (X.mul_mem (X.mul_mem hx hg.1) (X.inv_mem hx)) ?_
    have h1 := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective g
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    rw [h1]
    exact hg.2
  | one => simp
  | mul a b _ _ ha hb =>
    have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

theorem eq_one_of_odd_of_pow_two {g : G} (ho : Odd (orderOf g)) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g = 1 := by
  have h1 : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr ho)) dvd_rfl
    (orderOf_dvd_of_pow_eq_one hk)
  exact orderOf_eq_one_iff.mp h1

variable [Finite G]

theorem isPGroup_of_oddGen {X : Subgroup G} (h : IsPGroup 2 ↥(oddGen X)) : IsPGroup 2 ↥X := by
  rintro ⟨x, hx⟩
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hodd : Odd (orderOf (x ^ 2 ^ k)) := by
    refine hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
    rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
  obtain ⟨j, hj⟩ := h ⟨x ^ 2 ^ k, mem_oddGen (X.pow_mem hx _) hodd⟩
  have hj' : (x ^ 2 ^ k) ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have h1 := eq_one_of_odd_of_pow_two hodd hj'
  exact ⟨k, Subtype.ext (by simpa using h1)⟩

omit [Finite G] in
theorem three_dvd_of_e8Struct {X E : Subgroup G} (hE : E8Struct X E) : 3 ∣ Nat.card ↥X := by
  have h168 : 168 ∣ Nat.card ↥X := by
    rw [← hE.index]
    exact Subgroup.index_dvd_card _
  exact (by norm_num : (3 : ℕ) ∣ 168).trans h168

theorem not_isPGroup_two_of_three_dvd {X : Subgroup G} (h3 : 3 ∣ Nat.card ↥X) :
    ¬ IsPGroup 2 ↥X := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  rw [hk] at h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem le_oddGen_of_normal {X : Subgroup G}
    (hN : ∀ N : Subgroup G, N ≤ X → (∀ x ∈ X, ∀ y ∈ N, x * y * x⁻¹ ∈ N) →
      IsPGroup 2 ↥N ∨ N = X) (h2 : ¬ IsPGroup 2 ↥X) : X ≤ oddGen X := by
  rcases hN (oddGen X) (oddGen_le X) fun x hx y hy => conj_mem_oddGen hx hy with h | h
  · exact absurd (isPGroup_of_oddGen h) h2
  · exact h.ge

theorem D1Pack.of_e8 (hN : E8NormalFact) (hP : E8PerfectFact) {X E : Subgroup G}
    (hE : E8Struct X E) : D1Pack X where
  normal := hN G X E hE
  perfect := hP G X E hE
  odd := le_oddGen_of_normal (hN G X E hE)
    (not_isPGroup_two_of_three_dvd (three_dvd_of_e8Struct hE))
  not_two := not_isPGroup_two_of_three_dvd (three_dvd_of_e8Struct hE)

end CFSG.ClassicalInvolution.Q3.TL4
