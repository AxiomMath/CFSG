module

public import CFSG.GH74.GLS.Prop27.Defs
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic
public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.GH74.GLS.Prop27

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.E2 CFSG.Blueprint Subgroup Assembly.LowTwoRank

private theorem card_of_shapeL28 {K : Type} [Group K] (h : ShapeL28 K) : Nat.card K = 504 := by
  rw [card_of_lieModel_PSL (by norm_num) h]
  decide

private theorem card_of_shapeL33 {K : Type} [Group K] (h : ShapeL33 K) : Nat.card K = 5616 := by
  rw [card_of_lieModel_PSL (by norm_num) h]
  decide

private theorem card_of_shapeU33 {K : Type} [Group K] (h : ShapeU33 K) : Nat.card K = 6048 := by
  rw [card_of_lieModel_PSU (by norm_num) (by norm_num) h]
  decide

private theorem card_of_shapeSz8
    {K : Type} [Group K] (h : ShapeSz8 K) : Nat.card K = 29120 := by
  rw [card_of_lieModel_twistedB2 h]
  decide

private theorem card_of_shapeM11
    {K : Type} [Group K] (h : ShapeM11 K) : Nat.card K = 7920 :=
  card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 h

private theorem card_quotient_center_of_center_eq_bot {K : Type} [Group K] (h : center K = ⊥) :
    Nat.card (K ⧸ center K) = Nat.card K := by
  have h1 : Nat.card (center K) = 1 := by rw [h, Subgroup.card_bot]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [h1, mul_one] at h2
  exact h2.symm

private theorem card_eq_card_quotient_center_mul_two {K : Type} [Group K]
    (h : Nat.card (center K) = 2) : Nat.card K = Nat.card (K ⧸ center K) * 2 := by
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rwa [h] at h2

theorem card_quotient_of_shapes7
    {K : Type} [Group K] [Finite K] (h : Shapes7 K) :
    Nat.card (K ⧸ center K) ∈ ({504, 5616, 6048, 29120, 7920, 95040} : Finset ℕ) := by
  rcases h with ⟨hc, h | h | h | h | h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · rw [card_quotient_center_of_center_eq_bot hc, card_of_shapeL28 h]
    decide
  · rw [card_quotient_center_of_center_eq_bot hc, card_of_shapeL33 h]
    decide
  · rw [card_quotient_center_of_center_eq_bot hc, card_of_shapeU33 h]
    decide
  · rw [card_quotient_center_of_center_eq_bot hc, card_of_shapeSz8 h]
    decide
  · rw [card_quotient_center_of_center_eq_bot hc, card_of_shapeM11 h]
    decide
  · rw [card_of_isSporadic_M12 h]
    decide
  · rw [card_of_lieModel_twistedB2 h]
    decide

theorem card_of_shapes7
    {K : Type} [Group K] [Finite K] (h : Shapes7 K) :
    Nat.card K ∈ ({504, 5616, 6048, 29120, 7920, 190080, 58240} : Finset ℕ) := by
  rcases h with ⟨-, h | h | h | h | h⟩ | ⟨-, hz, h⟩ | ⟨-, hz, h⟩
  · rw [card_of_shapeL28 h]
    decide
  · rw [card_of_shapeL33 h]
    decide
  · rw [card_of_shapeU33 h]
    decide
  · rw [card_of_shapeSz8 h]
    decide
  · rw [card_of_shapeM11 h]
    decide
  · rw [card_eq_card_quotient_center_mul_two hz, card_of_isSporadic_M12 h]
    decide
  · rw [card_eq_card_quotient_center_mul_two hz, card_of_lieModel_twistedB2 h]
    decide

private theorem ordA_one_of_odd {q : ℕ} (hq : Odd q) :
    CFSG.Open.ordA 1 q = q * (q ^ 2 - 1) / 2 := by
  have h2 : 2 ∣ q - 1 := by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨k, by omega⟩
  simp [CFSG.Open.ordA, Nat.gcd_eq_left h2]

theorem false_of_lieModel_psl2_odd_of_shapes7
    {K : Type} [Group K] [Finite K] (h : Shapes7 K)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hL : LieModel K .PSL 2 p f) : False := by
  have hcard : Nat.card K = CFSG.Open.ordA 1 (p ^ f) := card_of_lieModel_PSL (by norm_num) hL
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hmem := card_of_shapes7 h
  rw [hcard, ordA_one_of_odd hodd] at hmem
  generalize p ^ f = q at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hb : q * (q ^ 2 - 1) ≤ 380161 := by omega
  have hle : q ≤ 80 := by
    by_contra hgt
    have h1 : 81 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 81 * (81 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right h1 1)
    omega
  interval_cases q <;> omega

theorem card_quotient_ne_L34_of_shapes7
    {K : Type} [Group K] [Finite K] (h : Shapes7 K) :
    Nat.card (K ⧸ center K) ≠ 20160 := by
  intro h20
  have hmem := card_quotient_of_shapes7 h
  rw [h20] at hmem
  revert hmem
  decide

end CFSG.GH74.GLS.Prop27
