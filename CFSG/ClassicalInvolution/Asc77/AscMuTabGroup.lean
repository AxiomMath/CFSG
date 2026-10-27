module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace MuTab

section Generated

variable {Q : Type*} [Group Q]

theorem eq_one_or_eq_of_mem_closure_single {d : Q} (h2 : d * d = 1) {x : Q}
    (hx : x ∈ Subgroup.closure ({d} : Set Q)) : x = 1 ∨ x = d := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact Or.inr (Set.mem_singleton_iff.mp hx)
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (by rw [hx, hy, one_mul])
    · exact Or.inr (by rw [hx, hy, one_mul])
    · exact Or.inr (by rw [hx, hy, mul_one])
    · exact Or.inl (by rw [hx, hy, h2])
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (by rw [hx, inv_one])
    · exact Or.inr (by rw [hx, inv_eq_of_mul_eq_one_right h2])

theorem nonempty_mulEquiv_z2 {d : Q} (h2 : d * d = 1) (h1 : d ≠ 1)
    (hcl : Subgroup.closure ({d} : Set Q) = ⊤) : Nonempty (Q ≃* Multiplicative (ZMod 2)) := by
  classical
  have hall : ∀ x : Q, x = 1 ∨ x = d := fun x =>
    eq_one_or_eq_of_mem_closure_single h2 (hcl ▸ Subgroup.mem_top x)
  let e : Q ≃ Bool :=
    { toFun := fun x => decide (x = d)
      invFun := fun b => if b then d else 1
      left_inv := fun x => by
        rcases hall x with hx | hx
        · rw [hx]; simp [Ne.symm h1]
        · rw [hx]; simp
      right_inv := fun b => by
        cases b
        · simp [Ne.symm h1]
        · simp }
  have hcard : Nat.card Q = 2 := by rw [Nat.card_congr e]; simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic Q := isCyclic_of_prime_card hcard
  have : IsCyclic (Multiplicative (ZMod 2)) := inferInstance
  exact ⟨mulEquivOfCyclicCardEq (by rw [hcard]; simp)⟩

theorem mul_mul_self_of_commute {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : (a * b) * (a * b) = 1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by simp only [mul_assoc]
    _ = 1 := by rw [ha, hb, one_mul]

theorem mem_closure_pair_commuting {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {x : Q} (hx : x ∈ Subgroup.closure ({a, b} : Set Q)) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
  have e3 : (a * b) * a = b := by rw [hab, mul_assoc, ha, mul_one]
  have e4 : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
  have e5 := mul_mul_self_of_commute ha hb hab
  have hba : b * a = a * b := hab.symm
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl (Set.mem_singleton_iff.mp hx)))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [ha, hb, hba, e1, e2, e3, e4, e5]
  | inv x _ hx =>
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right e5)))

theorem nonempty_mulEquiv_klein {a b : Q} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (hcl : Subgroup.closure ({a, b} : Set Q) = ⊤) :
    Nonempty (Q ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
  have hall : ∀ x : Q, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := fun x =>
    mem_closure_pair_commuting ha hb hab (hcl ▸ Subgroup.mem_top x)
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have := eq_inv_of_mul_eq_one_left h
    rw [inv_eq_of_mul_eq_one_right hb] at this
    exact this)
  have hab_a : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab_b : a * b ≠ b := fun h => ha1 (by simpa using h)
  have hcard : Nat.card Q = 4 := by
    have : (Set.univ : Set Q) = {1, a, b, a * b} := by
      ext x
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
      exact hall x
    rw [← Set.ncard_univ, this]
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm ha1, Ne.symm hb1, Ne.symm hab1]),
      Set.ncard_insert_of_notMem (by simp [hne, Ne.symm hab_a]), Set.ncard_pair (Ne.symm hab_b)]
  have : Nontrivial Q := ⟨⟨a, 1, ha1⟩⟩
  have hexp : Monoid.exponent Q = 2 := by
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    refine orderOf_eq_prime ?_ hg
    rcases hall g with hg' | hg' | hg' | hg' <;> rw [hg', pow_two]
    · exact absurd hg' hg
    · exact ha
    · exact hb
    · exact mul_mul_self_of_commute ha hb hab
  have : IsKleinFour Q := ⟨hcard, hexp⟩
  exact IsKleinFour.nonempty_mulEquiv

end Generated

@[expose] def Indep3 {Q : Type*} [Group Q] (a b c : Q) : Prop :=
  a * a = 1 ∧ b * b = 1 ∧ c * c = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1 ∧ a * b = b * a ∧ a * c = c * a ∧
    b * c = c * b ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b

theorem Indep3.map {Q X : Type*} [Group Q] [Group X] (φ : Q ≃* X) {a b c : Q}
    (h : Indep3 a b c) : Indep3 (φ a) (φ b) (φ c) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have e1 : φ a * φ a = 1 := by rw [← map_mul, h1, map_one]
  have e2 : φ b * φ b = 1 := by rw [← map_mul, h2, map_one]
  have e3 : φ c * φ c = 1 := by rw [← map_mul, h3, map_one]
  refine ⟨e1, e2, e3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => h4 (φ.injective (by rw [h, map_one]))
  · exact fun h => h5 (φ.injective (by rw [h, map_one]))
  · exact fun h => h6 (φ.injective (by rw [h, map_one]))
  · rw [← map_mul, ← map_mul, h7]
  · rw [← map_mul, ← map_mul, h8]
  · rw [← map_mul, ← map_mul, h9]
  · exact fun h => h10 (φ.injective h)
  · exact fun h => h11 (φ.injective h)
  · exact fun h => h12 (φ.injective h)
  · exact fun h => h13 (φ.injective (by rw [map_mul]; exact h))

@[expose] def indepB {Q : Type*} [Group Q] [DecidableEq Q] (a b c : Q) : Bool :=
  decide (a * a = 1) && decide (b * b = 1) && decide (c * c = 1) && decide (a ≠ 1) &&
    decide (b ≠ 1) && decide (c ≠ 1) && decide (a * b = b * a) && decide (a * c = c * a) &&
    decide (b * c = c * b) && decide (a ≠ b) && decide (c ≠ a) && decide (c ≠ b) &&
    decide (c ≠ a * b)

theorem indepB_of_indep3 {Q : Type*} [Group Q] [DecidableEq Q] {a b c : Q}
    (h : Indep3 a b c) : indepB a b c = true := by
  simp only [indepB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact h

theorem noIndep3_z2 : ∀ a b c : Multiplicative (ZMod 2), ¬ Indep3 a b c := fun a b c h => by
  have h0 : ∀ a b c : Multiplicative (ZMod 2), indepB a b c = false := by decide +kernel
  have := indepB_of_indep3 h
  rw [h0] at this
  exact Bool.false_ne_true this

theorem noIndep3_perm3 : ∀ a b c : Equiv.Perm (Fin 3), ¬ Indep3 a b c := fun a b c h => by
  have h0 : ∀ a b c : Equiv.Perm (Fin 3), indepB a b c = false := by decide +kernel
  have := indepB_of_indep3 h
  rw [h0] at this
  exact Bool.false_ne_true this

theorem noIndep3_klein : ∀ a b c : Multiplicative (ZMod 2 × ZMod 2), ¬ Indep3 a b c :=
  fun a b c h => by
    have h0 : ∀ a b c : Multiplicative (ZMod 2 × ZMod 2), indepB a b c = false := by
      decide +kernel
    have := indepB_of_indep3 h
    rw [h0] at this
    exact Bool.false_ne_true this

theorem noIndep3_perm4 : ∀ a b c : Equiv.Perm (Fin 4), ¬ Indep3 a b c := fun a b c h => by
  have h0 : ∀ a b c : Equiv.Perm (Fin 4), indepB a b c = false := by decide +kernel
  have := indepB_of_indep3 h
  rw [h0] at this
  exact Bool.false_ne_true this

theorem not_indep3_z2 {Q : Type*} [Group Q] (φ : Q ≃* Multiplicative (ZMod 2)) {a b c : Q} :
    ¬ Indep3 a b c := fun h => noIndep3_z2 _ _ _ (h.map φ)

theorem not_indep3_perm3 {Q : Type*} [Group Q] (φ : Q ≃* Equiv.Perm (Fin 3)) {a b c : Q} :
    ¬ Indep3 a b c := fun h => noIndep3_perm3 _ _ _ (h.map φ)

theorem not_indep3_klein {Q : Type*} [Group Q] (φ : Q ≃* Multiplicative (ZMod 2 × ZMod 2))
    {a b c : Q} : ¬ Indep3 a b c := fun h => noIndep3_klein _ _ _ (h.map φ)

theorem not_indep3_perm4 {Q : Type*} [Group Q] (φ : Q ≃* Equiv.Perm (Fin 4)) {a b c : Q} :
    ¬ Indep3 a b c := fun h => noIndep3_perm4 _ _ _ (h.map φ)

@[expose] def Invols (X : Type*) [Group X] : Type _ := {x : X // x * x = 1 ∧ x ≠ 1}

instance (X : Type*) [Group X] [Finite X] : Finite (Invols X) := by
  unfold Invols
  infer_instance

theorem natCard_invols_perm4 : Nat.card (Invols (Equiv.Perm (Fin 4))) = 9 := by
  unfold Invols
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem natCard_invols_perm3 : Nat.card (Invols (Equiv.Perm (Fin 3))) = 3 := by
  unfold Invols
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem natCard_invols_klein : Nat.card (Invols (Multiplicative (ZMod 2 × ZMod 2))) = 3 := by
  unfold Invols
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem natCard_invols_z2 : Nat.card (Invols (Multiplicative (ZMod 2))) = 1 := by
  unfold Invols
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem not_ten_involutions {Q X : Type*} [Group Q] [Group X] [Finite X] (φ : Q ≃* X)
    (hX : Nat.card (Invols X) ≤ 9) (f : Fin 10 → Q) (hf : Function.Injective f)
    (h1 : ∀ i, f i * f i = 1) (h2 : ∀ i, f i ≠ 1) : False := by
  let g : Fin 10 → Invols X := fun i =>
    ⟨φ (f i), by rw [← map_mul, h1 i, map_one], fun h => h2 i (φ.injective (by
      rw [h, map_one]))⟩
  have hinj : Function.Injective g := by
    intro i j hij
    exact hf (φ.injective (congrArg Subtype.val hij))
  have h10 := Nat.card_le_card_of_injective g hinj
  rw [Nat.card_eq_fintype_card (α := Fin 10), Fintype.card_fin] at h10
  omega

theorem card_z2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp

theorem card_perm3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

theorem card_klein : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_perm4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

end MuTab

end CFSG.ClassicalInvolution.Asc77
