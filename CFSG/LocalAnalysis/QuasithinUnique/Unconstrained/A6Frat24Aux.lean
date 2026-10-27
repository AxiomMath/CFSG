module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_5

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type} [Group G]

theorem mem_normalizer_of_conjugate_eq {Q : Subgroup G} {x s : G}
    (h : CFSG.conjugate Q x = CFSG.conjugate Q s) :
    x * s⁻¹ ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  have e1 : s⁻¹ * q * s ∈ CFSG.conjugate Q s ↔ q ∈ Q := by
    rw [mem_conjugate_iff]
    have : s * (s⁻¹ * q * s) * s⁻¹ = q := by group
    rw [this]
  have e2 : s⁻¹ * q * s ∈ CFSG.conjugate Q x ↔ x * (s⁻¹ * q * s) * x⁻¹ ∈ Q := mem_conjugate_iff
  rw [← e1, ← h, e2]
  have : x * (s⁻¹ * q * s) * x⁻¹ = x * s⁻¹ * q * (x * s⁻¹)⁻¹ := by group
  rw [this]

theorem four_subgroup_elems [Finite G] {E : Subgroup G} (hE : Nat.card E = 4) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a * a = 1)
    (hb2 : b * b = 1) : ∀ x ∈ E, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, hbinv]
  have hab2 : a * b ≠ a := by
    intro h
    exact hb1 (mul_eq_left.mp h)
  have hab3 : a * b ≠ b := by
    intro h
    exact ha1 (mul_eq_right.mp h)
  set T : Set G := {1, a, b, a * b} with hT
  have hTcard : T.ncard = 4 := by
    have h3 : ({b, a * b} : Set G).ncard = 2 := Set.ncard_pair (Ne.symm hab3)
    have h2 : ({a, b, a * b} : Set G).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, h3]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, hab2.symm⟩
    show ({1, a, b, a * b} : Set G).ncard = 4
    rw [Set.ncard_insert_of_notMem, h2]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
  have hTE : T ⊆ (E : Set G) := by
    intro x hx
    simp only [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact ha
    · exact hb
    · exact E.mul_mem ha hb
  have hEcard : (E : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hE
  have hEq : T = (E : Set G) :=
    Set.eq_of_subset_of_ncard_le hTE (by rw [hTcard, hEcard]) (Set.toFinite _)
  intro x hx
  have : x ∈ T := by rw [hEq]; exact hx
  simpa [hT] using this

theorem four_set_ncard {a b : G} [Finite G] (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hb2 : b * b = 1) : ({1, a, b, a * b} : Set G).ncard = 4 := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, hbinv]
  have hab2 : a * b ≠ a := fun h => hb1 (mul_eq_left.mp h)
  have hab3 : a * b ≠ b := fun h => ha1 (mul_eq_right.mp h)
  have h3 : ({b, a * b} : Set G).ncard = 2 := Set.ncard_pair (Ne.symm hab3)
  have h2 : ({a, b, a * b} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, h3]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hab, hab2.symm⟩
  rw [Set.ncard_insert_of_notMem, h2]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨ha1.symm, hb1.symm, hab1.symm⟩

theorem exists_four_subgroup [Finite G] {a b : G} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hc : a * b = b * a) :
    ∃ E : Subgroup G, (∀ x, x ∈ E ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ∧ IsFourSubgroup E := by
  have hba : b * a = a * b := hc.symm
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have haab : a * (a * b) = b := by rw [← mul_assoc, ha2, one_mul]
  have hbab : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb2, mul_one]
  have habb : a * b * b = a := by rw [mul_assoc, hb2, mul_one]
  have haba : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha2, one_mul]
  have habab : a * b * (a * b) = 1 := by rw [mul_assoc, hbab, ha2]
  have hbinv' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right habab
  let E : Subgroup G :=
    { carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
      mul_mem' := by
        rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl)
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp [ha2]
        · simp
        · simp [haab]
        · simp
        · simp [hba]
        · simp [hb2]
        · simp [hbab]
        · simp
        · simp [haba]
        · simp [habb]
        · simp [habab]
      one_mem' := Or.inl rfl
      inv_mem' := by
        rintro x (rfl | rfl | rfl | rfl)
        · simp
        · simp [hainv]
        · simp [hbinv]
        · simp [hbinv'] }
  have hmem : ∀ x, x ∈ E ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := fun x => Iff.rfl
  refine ⟨E, hmem, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    apply Subtype.ext
    show x * y = y * x
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | rfl | simp | exact hc | exact hba | simp [haab, haba] | simp [hbab, habb]
  · rcases (hmem x).1 hx with rfl | rfl | rfl | rfl
    · simp
    · simpa [sq] using ha2
    · simpa [sq] using hb2
    · simpa [sq] using habab
  · have hset : (E : Set G) = {1, a, b, a * b} := Set.ext fun x => Iff.rfl
    calc Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq (E : Set G)
      _ = ({1, a, b, a * b} : Set G).ncard := by rw [hset]
      _ = 4 := four_set_ncard ha1 hb1 hab hb2

theorem exists_mem_ne_two [Finite G] {E : Subgroup G} (hE : Nat.card E = 4) (a b : G) :
    ∃ x ∈ E, x ≠ a ∧ x ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (E : Set G) ⊆ {a, b} := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (hcon x hx hxa)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({a, b} : Set G).ncard ≤ 2 := by
    calc ({a, b} : Set G).ncard ≤ ({b} : Set G).ncard + 1 := Set.ncard_insert_le a {b}
      _ = 2 := by rw [Set.ncard_singleton]
  have h3 : (E : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hE
  omega

end Generic

section CP

variable {G : Type*} [Group G] [Finite G]

theorem cp_contra {T S Q U : Subgroup G} (hT : IsPGroup 2 T) (hUS : U ≤ S) (hST : S ≤ T)
    (hU : IsSylowTwoOf U (Subgroup.normalizer (Q : Set G))) {x' : G} (hx'T : x' ∈ T)
    (hx'Q : x' ∈ Subgroup.normalizer (Q : Set G)) : x' ∈ S := by
  set X : Subgroup G := U ⊔ Subgroup.zpowers x' with hX
  have hXT : X ≤ T := sup_le (hUS.trans hST) (Subgroup.zpowers_le.mpr hx'T)
  have hX2 : IsPGroup 2 X := hT.to_le hXT
  have hXN : X ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hU.le (Subgroup.zpowers_le.mpr hx'Q)
  have hXU : X = U := hU.eq_of_le le_sup_left hXN hX2
  have : x' ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers x')
  rw [hXU] at this
  exact hUS this

end CP

end CFSG.QuasithinUnique
