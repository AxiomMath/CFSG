module

public import CFSG.CGT.Timmesfeld75.Sec62Pair
public import CFSG.CGT.Timmesfeld75.Sec62Orbit

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ Y : Subgroup G} {n m : ℕ}

@[expose] def sec62Line (T T₁ : Subgroup G) : Set (Subgroup G) := insert T (conjSet T T₁)

@[expose] def sec62Pts (T T₁ T₂ : Subgroup G) : Set (Subgroup G) :=
  insert T₂ (⋃ Q ∈ sec62Line T T₁, conjSet T₂ Q)

omit [Finite G] in
theorem Sec62Ctx.mem_line (P : Sec62Ctx T T₁ Y n m) {Q : Subgroup G} (hQ : Q ∈ sec62Line T T₁) :
    IsConjPt T Y Q ∧ Q ≤ T ⊔ T₁ := by
  rcases hQ with rfl | ⟨t, ht, rfl⟩
  · exact ⟨IsConjPt.self, le_sup_left⟩
  · have htX : t ∈ T ⊔ T₁ := Subgroup.mem_sup_left ht
    obtain ⟨x₀, hx₀X, hx₀⟩ := P.ctx.sec3.conj
    refine ⟨⟨t * x₀, Y.mul_mem (P.hXY htX) (P.hXY hx₀X), ?_⟩,
      conjSubgroup_le_of_le_of_mem le_sup_right htX⟩
    rw [hx₀, conjSubgroup_conjSubgroup]

theorem Sec62Ctx.ncard_line (P : Sec62Ctx T T₁ Y n m) : (sec62Line T T₁).ncard = 2 ^ m + 1 := by
  have hconj : (conjSet T T₁).ncard = 2 ^ m := by
    have h := ncard_conjSet_mul_card T T₁
    rw [← P.ctx.mul_card_normIn] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hT : T ∉ conjSet T T₁ := by
    rintro ⟨t, ht, e⟩
    refine P.ctx.hy.pair.ne ?_
    have h1 := congrArg (conjSubgroup t⁻¹) e
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
    rw [← h1]
    exact mem_normalizer_iff_conjSubgroup_eq.1 (Subgroup.le_normalizer (T.inv_mem ht))
  rw [sec62Line, Set.ncard_insert_of_notMem hT (Set.toFinite _), hconj]

theorem Sec62Ctx.ncard_orbit (P : Sec62Ctx T T₁ Y n m) {Q : Subgroup G}
    (hT₂ : IsConjPt T Y T₂) (hQ : IsConjPt T Y Q) (hne : T₂ ≠ Q) :
    (conjSet T₂ Q).ncard = 2 ^ m := by
  have h := ncard_conjSet_mul_card T₂ Q
  rw [P.normIn_eq hT₂ hQ hne, P.card_inf_cfgM hT₂, hT₂.card_eq, ← P.ctx.mul_card_normIn] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem Sec62Ctx.disjoint_orbits (P : Sec62Ctx T T₁ Y n m) {Q Q' : Subgroup G}
    (hT₂ : IsConjPt T Y T₂) (hQ : IsConjPt T Y Q) (hQ' : IsConjPt T Y Q') (hQX : Q ≤ T ⊔ T₁)
    (hQ'X : Q' ≤ T ⊔ T₁) (hT₂X : ¬ T₂ ≤ T ⊔ T₁) (hne : Q ≠ Q') :
    Disjoint (conjSet T₂ Q) (conjSet T₂ Q') := by
  refine Set.disjoint_left.2 fun R hR hR' => ?_
  obtain ⟨s, hs, rfl⟩ := hR
  obtain ⟨s', hs', hss'⟩ := hR'
  have hQ'eq : Q' = conjSubgroup (s'⁻¹ * s) Q := by
    rw [← conjSubgroup_conjSubgroup, hss', conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one]
  have hu : s'⁻¹ * s ∈ T₂ := T₂.mul_mem (T₂.inv_mem hs') hs
  have hT₂Q : T₂ ≠ Q := fun h => hT₂X (h.le.trans hQX)
  have hle : Q ⊔ Q' ≤ T₂ ⊔ Q := by
    refine sup_le le_sup_right ?_
    rw [hQ'eq]
    exact conjSubgroup_le_of_le_of_mem le_sup_right (Subgroup.mem_sup_left hu)
  have heq : Q ⊔ Q' = T₂ ⊔ Q := Subgroup.eq_of_le_of_card_ge hle
    (by rw [P.card_sup_eq hT₂ hQ hT₂Q, P.card_sup_eq hQ hQ' hne])
  exact hT₂X ((le_sup_left : T₂ ≤ T₂ ⊔ Q).trans (heq.symm.le.trans (sup_le hQX hQ'X)))

omit [Finite G] in
theorem notMem_conjSet_self {X Q : Subgroup G} (hQX : Q ≤ X) (hT₂X : ¬ T₂ ≤ X) :
    T₂ ∉ conjSet T₂ Q := by
  rintro ⟨s, hs, e⟩
  have h1 := congrArg (conjSubgroup s⁻¹) e
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
  have h2 : conjSubgroup s⁻¹ T₂ = T₂ :=
    mem_normalizer_iff_conjSubgroup_eq.1 (Subgroup.le_normalizer (T₂.inv_mem hs))
  rw [h2] at h1
  exact hT₂X (h1.le.trans hQX)

theorem Sec62Ctx.ncard_pts (P : Sec62Ctx T T₁ Y n m) (hT₂ : IsConjPt T Y T₂)
    (hT₂X : ¬ T₂ ≤ T ⊔ T₁) : (sec62Pts T T₁ T₂).ncard = (2 ^ m + 1) * 2 ^ m + 1 := by
  have hU := ncard_biUnion_const (Set.toFinite (sec62Line T T₁)) (s := fun Q => conjSet T₂ Q)
    (m := 2 ^ m)
    (fun Q hQ Q' hQ' hne => P.disjoint_orbits hT₂ (P.mem_line hQ).1 (P.mem_line hQ').1
      (P.mem_line hQ).2 (P.mem_line hQ').2 hT₂X hne)
    (fun Q hQ => P.ncard_orbit hT₂ (P.mem_line hQ).1 (fun h => hT₂X (h.le.trans (P.mem_line hQ).2)))
  have hnot : T₂ ∉ ⋃ Q ∈ sec62Line T T₁, conjSet T₂ Q := by
    intro hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨Q, hQ, hmem⟩ := hmem
    exact notMem_conjSet_self (P.mem_line hQ).2 hT₂X hmem
  rw [sec62Pts, Set.ncard_insert_of_notMem hnot (Set.toFinite _), hU, P.ncard_line]

end CFSG.CGT.Timmesfeld75
