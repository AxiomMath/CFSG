module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2V4

public section

namespace CFSG.ComponentClassification.AS81.Sec2V4

open Equiv

theorem exists_ne_ne : ∀ i a : Fin 5, ∃ j, j ≠ i ∧ j ≠ a := by
  decide

theorem eq_one_of_act_eq {π : Perm (Fin 5)} (h : ∀ v, IsEven v → act π v = v) : π = 1 := by
  refine Equiv.ext fun i => ?_
  rw [Perm.one_apply]
  by_contra hne
  obtain ⟨j, hji, hja⟩ := exists_ne_ne i (π i)
  have h1 := congrFun (h (pair i j) (isEven_pair i j)) (π i)
  rw [act_pair] at h1
  have hij : π i ≠ π j := fun e => hji (π.injective e).symm
  simp only [pair, Pi.add_apply, Pi.single_apply, ↓reduceIte, hij, hne, Ne.symm hja] at h1
  exact absurd h1 (by decide)

@[expose] def invConj : List (Perm (Fin 5) × Perm (Fin 5)) :=
  [(swap 0 1, 1), (swap 0 2, swap 1 2), (swap 0 3, swap 1 3), (swap 0 4, swap 1 4),
    (swap 1 2, swap 0 2), (swap 1 3, swap 0 3), (swap 1 4, swap 0 4),
    (swap 2 3, swap 0 2 * swap 1 3), (swap 2 4, swap 0 2 * swap 1 4),
    (swap 3 4, swap 0 3 * swap 1 4), (swap 0 1 * swap 2 3, 1), (swap 0 1 * swap 2 4, swap 3 4),
    (swap 0 1 * swap 3 4, swap 2 4), (swap 0 2 * swap 1 3, swap 0 3),
    (swap 0 2 * swap 1 4, swap 0 3 * swap 3 4), (swap 0 2 * swap 3 4, swap 0 3 * swap 1 4),
    (swap 0 3 * swap 1 2, swap 0 2), (swap 0 3 * swap 1 4, swap 0 2 * swap 2 4),
    (swap 0 3 * swap 2 4, swap 0 2 * swap 1 4), (swap 0 4 * swap 1 2, swap 0 2 * swap 3 4),
    (swap 0 4 * swap 1 3, swap 0 3 * swap 2 4), (swap 0 4 * swap 2 3, swap 1 4),
    (swap 1 2 * swap 3 4, swap 0 2 * swap 0 4), (swap 1 3 * swap 2 4, swap 0 3 * swap 0 4),
    (swap 1 4 * swap 2 3, swap 0 4)]

@[expose] def invList : List (Perm (Fin 5)) := 1 :: invConj.map Prod.fst

@[expose] def checkInvList : Bool :=
  (permsOfList (List.finRange 5)).all fun π =>
    !decide (π * π = 1) || invList.any fun x => decide (x = π)

theorem checkInvList_eq : checkInvList = true := by
  decide +kernel

theorem mem_invList {π : Perm (Fin 5)} (h : π * π = 1) : π ∈ invList := by
  have h1 := List.all_eq_true.mp checkInvList_eq π
    (mem_permsOfList_of_mem fun x _ => List.mem_finRange x)
  simp only [h, decide_true, Bool.not_true, Bool.false_or, List.any_eq_true,
    decide_eq_true_eq] at h1
  obtain ⟨x, hx, rfl⟩ := h1
  exact hx

@[expose] def checkInvConj : Bool :=
  invConj.all fun p => decide (p.2 * p.1 * p.2⁻¹ = swap 0 1) ||
    decide (p.2 * p.1 * p.2⁻¹ = swap 0 1 * swap 2 3)

theorem checkInvConj_eq : checkInvConj = true := by
  decide +kernel

theorem exists_conj_of_mul_self {π : Perm (Fin 5)} (h : π * π = 1) (h1 : π ≠ 1) :
    ∃ g : Perm (Fin 5), g * π * g⁻¹ = swap 0 1 ∨ g * π * g⁻¹ = swap 0 1 * swap 2 3 := by
  have hm := mem_invList h
  rw [invList, List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact absurd rfl h1
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  have h2 := List.all_eq_true.mp checkInvConj_eq p hp
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
  exact ⟨p.2, h2⟩

@[expose] def isDoubleB (x : Perm (Fin 5)) : Bool :=
  invConj.any fun p => decide (p.1 = x) && decide (p.2 * x * p.2⁻¹ = swap 0 1 * swap 2 3)

@[expose] def checkFour : Bool :=
  invList.all fun b => !decide ((swap 0 1 * b) * (swap 0 1 * b) = 1) || decide (b = 1) ||
    decide (swap 0 1 * b = 1) || isDoubleB b || isDoubleB (swap 0 1 * b)

theorem checkFour_eq : checkFour = true := by
  decide +kernel

theorem exists_conj_of_isDoubleB {x : Perm (Fin 5)} (h : isDoubleB x = true) :
    ∃ g : Perm (Fin 5), g * x * g⁻¹ = swap 0 1 * swap 2 3 := by
  simp only [isDoubleB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, -, -, hp⟩ := h
  exact ⟨p.2, hp⟩

theorem exists_conj_double {a b : Perm (Fin 5)} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (a * b) * (a * b) = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a * b ≠ 1) :
    (∃ g : Perm (Fin 5), g * a * g⁻¹ = swap 0 1 * swap 2 3) ∨
      (∃ g : Perm (Fin 5), g * b * g⁻¹ = swap 0 1 * swap 2 3) ∨
      ∃ g : Perm (Fin 5), g * (a * b) * g⁻¹ = swap 0 1 * swap 2 3 := by
  obtain ⟨g, hg | hg⟩ := exists_conj_of_mul_self ha ha1
  · set φ := MulAut.conj g with hφ
    have hc : ∀ x, φ x = g * x * g⁻¹ := fun x => MulAut.conj_apply g x
    have hga : φ a = swap 0 1 := by rw [hc, hg]
    have hb' : φ b * φ b = 1 := by rw [← map_mul, hb, map_one]
    have hab' : (swap 0 1 * φ b) * (swap 0 1 * φ b) = 1 := by
      rw [← hga, ← map_mul, ← map_mul, hab, map_one]
    have hb1' : φ b ≠ 1 := fun e => hb1 ((MulEquiv.map_eq_one_iff φ).mp e)
    have hab1' : swap 0 1 * φ b ≠ 1 := by
      rw [← hga, ← map_mul]
      exact fun e => hab1 ((MulEquiv.map_eq_one_iff φ).mp e)
    have h4 := List.all_eq_true.mp checkFour_eq (φ b) (mem_invList hb')
    simp only [hab', hb1', hab1', decide_true, decide_false, Bool.not_true, Bool.false_or,
      Bool.or_eq_true] at h4
    rcases h4 with h4 | h4
    · obtain ⟨k, hk⟩ := exists_conj_of_isDoubleB h4
      refine Or.inr (Or.inl ⟨k * g, ?_⟩)
      rw [← hk, hc]
      group
    · obtain ⟨k, hk⟩ := exists_conj_of_isDoubleB h4
      refine Or.inr (Or.inr ⟨k * g, ?_⟩)
      rw [← hk, ← hga, ← map_mul, hc]
      group
  · exact Or.inl ⟨g, hg⟩

@[expose] def checkThree : Bool :=
  [swap 0 1, swap 0 1 * swap 2 3].all fun a => invList.all fun b =>
    !decide ((a * b) * (a * b) = 1) || decide (b = 1) || decide (a * b = 1) ||
      invList.all fun c => !decide ((a * c) * (a * c) = 1) || !decide ((b * c) * (b * c) = 1) ||
        decide (c = 1) || decide (a * c = 1) || decide (b * c = 1) || decide (a * b * c = 1)

theorem checkThree_eq : checkThree = true := by
  decide +kernel

theorem dep_of_three_aux {a b c : Perm (Fin 5)}
    (ha : a = swap 0 1 ∨ a = swap 0 1 * swap 2 3) (hb : b * b = 1) (hc : c * c = 1)
    (hab : (a * b) * (a * b) = 1) (hac : (a * c) * (a * c) = 1) (hbc : (b * c) * (b * c) = 1) :
    b = 1 ∨ a * b = 1 ∨ c = 1 ∨ a * c = 1 ∨ b * c = 1 ∨ a * b * c = 1 := by
  have ha' : a ∈ [swap 0 1, swap 0 1 * swap 2 3] := by
    rcases ha with rfl | rfl <;> simp
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp checkThree_eq a ha') b (mem_invList hb)
  simp only [hab, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    or_assoc] at h1
  rcases h1 with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  have h2 := h1 c (mem_invList hc)
  simp only [hac, hbc, not_true, false_or] at h2
  exact Or.inr (Or.inr h2)

theorem dep_of_three {a b c : Perm (Fin 5)} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : (a * b) * (a * b) = 1) (hac : (a * c) * (a * c) = 1) (hbc : (b * c) * (b * c) = 1) :
    a = 1 ∨ b = 1 ∨ a * b = 1 ∨ c = 1 ∨ a * c = 1 ∨ b * c = 1 ∨ a * b * c = 1 := by
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  obtain ⟨g, hg⟩ := exists_conj_of_mul_self ha ha1
  set φ := MulAut.conj g with hφ
  have hc' : ∀ x, φ x = g * x * g⁻¹ := fun x => MulAut.conj_apply g x
  have he : ∀ x, φ x = 1 ↔ x = 1 := fun x => MulEquiv.map_eq_one_iff φ
  have hsq : ∀ x : Perm (Fin 5), x * x = 1 → φ x * φ x = 1 := fun x hx => by
    rw [← map_mul, hx, map_one]
  have hga : φ a = swap 0 1 ∨ φ a = swap 0 1 * swap 2 3 := by rw [hc']; exact hg
  have h := dep_of_three_aux hga (hsq b hb) (hsq c hc) (by rw [← map_mul]; exact hsq _ hab)
    (by rw [← map_mul]; exact hsq _ hac) (by rw [← map_mul]; exact hsq _ hbc)
  simp only [← map_mul, he] at h
  exact Or.inr h

@[expose] def HighRank (π : Perm (Fin 5)) : Prop :=
  ∃ v₁ v₂ : Fin 5 → ZMod 2, IsEven v₁ ∧ IsEven v₂ ∧ v₁ + act π v₁ ≠ 0 ∧ v₂ + act π v₂ ≠ 0 ∧
    v₁ + act π v₁ ≠ v₂ + act π v₂

theorem highRank_double : HighRank (swap 0 1 * swap 2 3) :=
  ⟨pair 0 4, pair 2 4, isEven_pair 0 4, isEven_pair 2 4, by decide, by decide, by decide⟩

theorem eq_zero_of_act_eq_zero {π : Perm (Fin 5)} {v : Fin 5 → ZMod 2} (h : act π v = 0) :
    v = 0 := by
  rw [← act_inv_act π v, h, act_zero]

theorem highRank_of_conj {π g : Perm (Fin 5)} (h : g * π * g⁻¹ = swap 0 1 * swap 2 3) :
    HighRank π := by
  obtain ⟨v₁, v₂, h1, h2, h3, h4, h5⟩ := highRank_double
  have hπ : π = g⁻¹ * (swap 0 1 * swap 2 3) * g := by rw [← h]; group
  have e : ∀ v, act g⁻¹ v + act π (act g⁻¹ v) =
      act g⁻¹ (v + act (swap 0 1 * swap 2 3) v) := by
    intro v
    rw [act_add, ← act_mul, ← act_mul, hπ]
    congr 2
    group
  refine ⟨act g⁻¹ v₁, act g⁻¹ v₂, isEven_act h1 _, isEven_act h2 _, ?_, ?_, ?_⟩
  · rw [e]
    exact fun h0 => h3 (eq_zero_of_act_eq_zero h0)
  · rw [e]
    exact fun h0 => h4 (eq_zero_of_act_eq_zero h0)
  · rw [e, e]
    intro h0
    apply h5
    have := congrArg (act g) h0
    rwa [act_act_inv, act_act_inv] at this

end CFSG.ComponentClassification.AS81.Sec2V4
