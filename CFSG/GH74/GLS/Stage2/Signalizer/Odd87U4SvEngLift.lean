module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87NatMod
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups commutatorElement

section Card

variable {p f : ℕ} {K : Type} [Field K]

theorem card_hypSU_four (h : UnitaryFieldData p f K) :
    Nat.card ↥(hypSU h 2 0) =
      (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) := by
  have := h.finite
  have hn : Module.finrank K (HypIndex 2 0 → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h (hypForm_isSymm h)
    (hypForm_separatingLeft h) hn (by norm_num)).2.1
  have hprod : ∏ i ∈ Finset.Icc 2 4, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) *
        (((p ^ f : ℕ) : ℤ) ^ 4 - 1) := by
    rw [show Finset.Icc 2 4 = {2, 3, 4} by rfl, Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num)]
    ring
  rw [hprod] at hSU
  have hcard : Nat.card ↥(hypSU h 2 0) = Nat.card (sesqSpecialUnitaryGroup (hypForm h 2 0)) :=
    card_gramSU h (hypGram 2 0 K)
  rw [hcard]
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  have hq4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow _ _ hq
  zify [hq2, hq4]
  rw [hSU]
  norm_num
  ring

end Card

section Lift

variable {p₀ f₀ : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p₀ f₀ K)

theorem hypScalars_pow_four {z : ↥(hypSU h 2 0)} (hz : z ∈ hypScalars h 2 0) : z ^ 4 = 1 := by
  obtain ⟨c, -, hc4, hz⟩ := hz
  have hc : c ^ 4 = 1 := by simpa using hc4
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, hz, ← map_pow, hc, map_one]
  rfl

theorem u4_exists_lift {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup (hypPSU h 2 0)}
    (hX : IsPGroup p ↥X) :
    ∃ X₀ : Subgroup ↥(hypSU h 2 0), IsPGroup p ↥X₀ ∧ X₀.map (hypProj h 2 0) = X ∧
      ∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ normalizer (X : Set (hypPSU h 2 0)) →
        g ∈ normalizer (X₀ : Set ↥(hypSU h 2 0)) := by
  have hker : (hypProj h 2 0).ker ≤ Subgroup.center ↥(hypSU h 2 0) := by
    rw [ker_hypProj]
    exact normOneScalars_le_center h _ _
  have hcop : Nat.Coprime p (Nat.card (hypProj h 2 0).ker) := by
    have hp : p.Prime := Fact.out
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (hypProj h 2 0).ker) p hdvd
    have hz4 : (z : ↥(hypSU h 2 0)) ^ 4 = 1 :=
      hypScalars_pow_four h (((SetLike.ext_iff.1 (ker_hypProj h 2 0)) _).1 z.2)
    have h1 : orderOf (z : ↥(hypSU h 2 0)) ∣ 4 := orderOf_dvd_of_pow_eq_one hz4
    rw [Subgroup.orderOf_coe, hz] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      (hp.dvd_of_dvd_pow (n := 2) (by simpa using h1)))
  obtain ⟨P, hP, hPY, hPX⟩ := NatMod.exists_lift_isPGroup (hypProj h 2 0)
    (hypProj_surjective h 2 0) hX
  refine ⟨P, hP, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hPY hg
    · intro hx
      obtain ⟨g, hg, hgx⟩ := hPX x hx
      exact ⟨g, hg, hgx⟩
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact NatMod.conj_mem_of_mem_normalizer hP hPY hPX hker hcop hg hy
    · intro hy
      have := NatMod.conj_mem_of_mem_normalizer hP hPY hPX hker hcop (c := g⁻¹)
        (by rw [map_inv]; exact inv_mem hg) hy
      simpa [mul_assoc] using this

end Lift

section Three

variable {p₀ f₀ : ℕ} {K : Type} [Field K]

theorem card_hypSU_four_three (h : UnitaryFieldData p₀ f₀ K) (hq : p₀ ^ f₀ = 3) :
    Nat.card ↥(hypSU h 2 0) = 13063680 := by
  rw [card_hypSU_four, hq]
  norm_num

theorem prime_eq_five_or_seven {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : p ∣ 13063680) : p = 5 ∨ p = 7 := by
  have h12 : (13063680 : ℕ) = 2 ^ 9 * 3 ^ 6 * 5 * 7 := by norm_num
  rw [h12] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)) hp2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)) hp3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)

theorem u4_cyclic_three (h : UnitaryFieldData p₀ f₀ K) (hq : p₀ ^ f₀ = 3) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {X₀ : Subgroup ↥(hypSU h 2 0)} (hX : IsPGroup p ↥X₀) :
    IsCyclic ↥X₀ := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hdvd : Nat.card X₀ ∣ 13063680 :=
    card_hypSU_four_three h hq ▸ Subgroup.card_subgroup_dvd_card X₀
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have h1 : Nat.card X₀ = 1 := by simpa using hn
    have : Subsingleton X₀ := (Nat.card_eq_one_iff_unique.1 h1).1
    infer_instance
  have hpd : p ∣ 13063680 := (dvd_pow_self p hn0.ne').trans (hn ▸ hdvd)
  have h57 := prime_eq_five_or_seven hp hp2 hp3 hpd
  have hn1 : n = 1 := by
    by_contra hne
    have h2 : 2 ≤ n := by omega
    have hsq : p ^ 2 ∣ 13063680 := (pow_dvd_pow p h2).trans (hn ▸ hdvd)
    rcases h57 with rfl | rfl <;> norm_num at hsq
  exact isCyclic_of_prime_card (by rw [hn, hn1, pow_one])

end Three

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
