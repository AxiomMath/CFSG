module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

theorem nonempty_mulEquiv_elem2 {G : Type*} [Group G] (n : ℕ) (hsq : ∀ g : G, g * g = 1)
    (hcard : Nat.card G = 2 ^ n) : Nonempty (G ≃* Elem2 n) := by
  have hinv : ∀ g : G, g⁻¹ = g := fun g => by
    rw [inv_eq_iff_mul_eq_one]; exact hsq g
  have hcomm : ∀ g h : G, g * h = h * g := by
    intro g h
    calc g * h = (g * h)⁻¹ := eq_inv_of_mul_eq_one_left (hsq (g * h))
      _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
      _ = h * g := by rw [hinv h, hinv g]
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  haveI : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero n (by norm_num))
  have hsmul : ∀ x : Additive G, (2 : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    simp [pow_two, hsq x.toMul]
  letI : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule (n := 2) hsmul
  haveI : Fintype (Additive G) := Fintype.ofFinite (Additive G)
  have hcard' : Fintype.card (Additive G) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr Additive.toMul]
    exact hcard
  have hfr : Module.finrank (ZMod 2) (Additive G) = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive G)
    rw [hcard', ZMod.card] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive G) hfr
  exact ⟨AddEquiv.toMultiplicativeRight b.equivFun.toAddEquiv⟩

theorem mem_closure_pair_iff {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {x : G} :
    x ∈ closure ({a, b} : Set G) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hba : ∀ y, b * (a * y) = a * (b * y) := fun y => by rw [← mul_assoc, ← hab, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, ha, hb, ha', hba, hab.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hai, hbi, mul_inv_rev, hab.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem card_closure_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card ↥(closure ({a, b} : Set G)) = 4 := by
  have hset : (closure ({a, b} : Set G) : Set G) = ({1, a, b, a * b} : Set G) := by
    ext x
    change x ∈ closure ({a, b} : Set G) ↔ x ∈ ({1, a, b, a * b} : Set G)
    rw [mem_closure_pair_iff ha hb hab]
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hab1 : a ≠ a * b := by
    intro h
    have hb_eq_one : b = 1 := by
      calc b = 1 * b := by rw [one_mul]
        _ = (a * a) * b := by rw [ha]
        _ = a * (a * b) := by rw [mul_assoc]
        _ = a * a := by rw [← h]
        _ = 1 := ha
    exact hb1 hb_eq_one
  have hba1 : b ≠ a * b := by
    intro h
    have ha_eq_one : a = 1 := by
      calc a = 1 * a := by rw [one_mul]
        _ = (b * b) * a := by rw [hb]
        _ = b * (b * a) := by rw [mul_assoc]
        _ = b * (a * b) := by rw [hab.symm]
        _ = b * b := by rw [← h]
        _ = 1 := hb
    exact ha1 ha_eq_one
  have h1ab : (1 : G) ≠ a * b := by
    intro h
    have hba : b = a := by
      calc b = 1 * b := by rw [one_mul]
        _ = (a * a) * b := by rw [ha]
        _ = a * (a * b) := by rw [mul_assoc]
        _ = a * 1 := by rw [← h]
        _ = a := by rw [mul_one]
    exact hne hba.symm
  have h1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
    simp [ha1.symm, hb1.symm, h1ab]
  have h2 : a ∉ ({b, a * b} : Set G) := by
    simp [hne, hab1]
  have h3 : b ∉ ({a * b} : Set G) := by
    simpa using hba1
  calc Nat.card ↥(closure ({a, b} : Set G))
      = ((closure ({a, b} : Set G) : Set G)).ncard := Nat.card_coe_set_eq _
    _ = ({1, a, b, a * b} : Set G).ncard := by rw [hset]
    _ = 4 := by
      rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
        Set.ncard_insert_of_notMem h3, Set.ncard_singleton]

theorem nonempty_mulEquiv_elem2_closure_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nonempty (↥(closure ({a, b} : Set G)) ≃* Elem2 2) := by
  have hsq_ab : (a * b) * (a * b) = 1 := by
    have hba : Commute b a := (commute_iff_eq b a).mpr hab.symm
    rw [hba.mul_mul_mul_comm a b, ha, hb, one_mul]
  have hsq : ∀ g : ↥(closure ({a, b} : Set G)), g * g = 1 := by
    intro g
    apply Subtype.ext
    change (g : G) * (g : G) = 1
    rcases (mem_closure_pair_iff ha hb hab).1 g.2 with h | h | h | h
    · rw [h]; exact one_mul 1
    · rw [h]; exact ha
    · rw [h]; exact hb
    · rw [h]; exact hsq_ab
  have hcard : Nat.card ↥(closure ({a, b} : Set G)) = 2 ^ 2 := by
    rw [card_closure_pair ha hb hab ha1 hb1 hne]; norm_num
  exact nonempty_mulEquiv_elem2 2 hsq hcard

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
