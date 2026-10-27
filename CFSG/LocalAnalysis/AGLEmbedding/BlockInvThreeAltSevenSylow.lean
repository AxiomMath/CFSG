module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeBasic

public section

namespace CFSG.AGLEmbedding.AltSevenInv

open Equiv Equiv.Perm

@[expose] def r : Perm (Fin 7) := swap 1 2 * swap 2 3 * swap 3 4 * swap 5 6

@[expose] def s : Perm (Fin 7) := swap 1 3 * swap 5 6

@[expose] def p0List : List (Perm (Fin 7)) :=
  [1, r, r * r, r * r * r, s, s * r, s * r * r, s * r * r * r]

theorem p0_check :
    (p0List.all fun a => p0List.all fun b => p0List.contains (a * b)) &&
    p0List.all (fun a => decide (sign a = 1)) &&
    p0List.all (fun a => decide (a * a * a * a = 1)) &&
    p0List.all (fun a => decide (a * a = 1) || decide (a = r) || decide (a = r * r * r)) =
      true := by
  decide +kernel

theorem p0_closed : ∀ a ∈ p0List, ∀ b ∈ p0List, a * b ∈ p0List := by
  have h := p0_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.1.1

theorem p0_sign : ∀ a ∈ p0List, sign a = 1 := by
  have h := p0_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

theorem p0_pow4 : ∀ a ∈ p0List, a * a * a * a = 1 := by
  have h := p0_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem p0_four : ∀ a ∈ p0List, a * a ≠ 1 → a = r ∨ a = r * r * r := by
  have h := p0_check
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  intro a ha ha2
  rcases h.2 a ha with (h1 | h1) | h1
  · exact absurd h1 ha2
  · exact Or.inl h1
  · exact Or.inr h1

theorem p0_card : p0List.toFinset.card = 8 := by decide +kernel

theorem r_pow : r * r ≠ 1 ∧ r * r * r * (r * r * r) ≠ 1 ∧ r * r * r * r = 1 := by
  decide +kernel

theorem p0_rels : s * (s * r) = r ∧ s * (s * r * r * r) = r * r * r ∧ s * (r * r) = s * r * r ∧
    s * (s * r * r) = r * r ∧ s * r * r * (s * r) = r * r * r ∧
    s * r * r * (s * r * r * r) = r ∧ s * r * r * (r * r) = s ∧ s * r * (r * r) = s * r * r * r ∧
    s * r * (s * r * r * r) = r * r ∧ s * r * r * r * (r * r) = s * r := by
  decide +kernel

@[expose] def P0 : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {g | (g : Perm (Fin 7)) ∈ p0List}
  mul_mem' ha hb := p0_closed _ ha _ hb
  one_mem' := List.mem_cons_self
  inv_mem' {a} ha := by
    have hinv : (a : Perm (Fin 7))⁻¹ = a * a * a :=
      inv_eq_of_mul_eq_one_right (by simpa only [mul_assoc] using p0_pow4 _ ha)
    change (a : Perm (Fin 7))⁻¹ ∈ p0List
    rw [hinv]
    exact p0_closed _ (p0_closed _ ha _ ha) _ ha

theorem card_P0 : Nat.card P0 = 8 := by
  have e : P0 ≃ p0List.toFinset :=
    { toFun := fun g => ⟨(g : alternatingGroup (Fin 7)), List.mem_toFinset.mpr g.2⟩
      invFun := fun σ => ⟨⟨σ, mem_alternatingGroup.mpr (p0_sign _ (List.mem_toFinset.mp σ.2))⟩,
        List.mem_toFinset.mp σ.2⟩
      left_inv := fun g => rfl
      right_inv := fun σ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, p0_card]

theorem isPGroup_P0 : IsPGroup 2 P0 := IsPGroup.of_card (n := 3) (by rw [card_P0]; norm_num)

theorem not_two_dvd_index_P0 : ¬ 2 ∣ P0.index := by
  have h := Subgroup.card_mul_index P0
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rw [card_P0, hA] at h
  have : P0.index = 315 := by omega
  rw [this]
  decide

@[expose] def inT (T : Subgroup (alternatingGroup (Fin 7))) (σ : Perm (Fin 7)) : Prop :=
  ∃ h : σ ∈ alternatingGroup (Fin 7), (⟨σ, h⟩ : alternatingGroup (Fin 7)) ∈ T

section Inner

variable {T : Subgroup (alternatingGroup (Fin 7))}

theorem inT_coe {x : alternatingGroup (Fin 7)} : inT T x ↔ x ∈ T :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem inT_mul {a b : Perm (Fin 7)} (ha : inT T a) (hb : inT T b) : inT T (a * b) := by
  obtain ⟨ha', ha⟩ := ha
  obtain ⟨hb', hb⟩ := hb
  exact ⟨_, T.mul_mem ha hb⟩

theorem inT_one : inT T 1 := ⟨one_mem _, T.one_mem⟩

theorem mem_p0_of_inT (hTP : T ≤ P0) {σ : Perm (Fin 7)} (h : inT T σ) : σ ∈ p0List := by
  obtain ⟨hσ, h⟩ := h
  exact hTP h

theorem mem_normalizer_of_list {E : List (Perm (Fin 7))} (hE : ∀ σ, inT T σ ↔ σ ∈ E)
    (g : alternatingGroup (Fin 7))
    (hg : ∀ σ ∈ E, (g : Perm (Fin 7)) * σ * (g : Perm (Fin 7))⁻¹ ∈ E) :
    g ∈ Subgroup.normalizer (T : Set (alternatingGroup (Fin 7))) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  have h1 := (hE _).mp (inT_coe.mpr hn)
  have h2 := (hE _).mpr (hg _ h1)
  show g * n * g⁻¹ ∈ T
  refine inT_coe.mp ?_
  simpa using h2

@[expose] def witCheck (E : List (Perm (Fin 7))) (a g : Perm (Fin 7)) : Bool :=
  decide (sign a = 1) && decide (sign g = 1) &&
    E.all (fun σ => E.contains (a * σ * a⁻¹)) && E.all (fun σ => E.contains (g * σ * g⁻¹)) &&
    decide (a * a * a = 1) && decide (a ≠ 1) && decide (g * a * g⁻¹ = a⁻¹)

theorem invThree_of_witCheck {E : List (Perm (Fin 7))} (hE : ∀ σ, inT T σ ↔ σ ∈ E)
    (a g : Perm (Fin 7)) (h : witCheck E a g = true) :
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) := by
  simp only [witCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨ha, hg⟩, haE⟩, hgE⟩, ha3⟩, ha1⟩, hinv⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨⟨a, mem_alternatingGroup.mpr ha⟩, mem_normalizer_of_list hE _ haE,
    ⟨g, mem_alternatingGroup.mpr hg⟩, mem_normalizer_of_list hE _ hgE, ?_, ?_⟩
  · refine orderOf_eq_prime (Subtype.ext ?_) (fun h => ha1 (congrArg Subtype.val h))
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ, pow_two, ha3]
  · exact Subtype.ext (by simpa using hinv)

end Inner

end CFSG.AGLEmbedding.AltSevenInv
