module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.Quasithin.Background.SmithB42Disp

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

theorem card_mul_card_le_card_sup_mul_card_inf {G : Type*} [Group G] [Finite G]
    (Λ B : Subgroup G) :
    Nat.card Λ * Nat.card B ≤ Nat.card (Λ ⊔ B : Subgroup G) * Nat.card (Λ ⊓ B : Subgroup G) :=
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.card_mul_card_le_sup_inf Λ B

theorem weight_le_weight_sup {G B Λ : Subgroup (MulAut V)} (hB : IsFFStarOffender G B) :
    Nat.card Λ * Nat.card (fixV Λ) ≤
      Nat.card (Λ ⊔ B : Subgroup (MulAut V)) * Nat.card (fixV (Λ ⊔ B)) := by
  have : Finite (MulAut V) := B42Disp.finite_mulAut
  have h1 := card_mul_card_le_card_sup_mul_card_inf Λ B
  obtain ⟨h2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (fixV Λ) (fixV B)
    (fun x _ y _ => mul_comm x y)
  have hle : fixV Λ ⊔ fixV B ≤ fixV (Λ ⊓ B) :=
    sup_le (B1.fixV_le_fixV inf_le_left) (B1.fixV_le_fixV inf_le_right)
  have h3 := Subgroup.card_le_of_le hle
  have h4 := hB.2.2.2 (Λ ⊓ B) inf_le_right
  rw [B42Disp.fixV_sup]
  have hpos1 : 0 < Nat.card (Λ ⊓ B : Subgroup (MulAut V)) := Nat.card_pos
  have hpos2 : 0 < Nat.card (fixV Λ ⊔ fixV B : Subgroup V) := Nat.card_pos
  have hbd : Nat.card (Λ ⊓ B : Subgroup (MulAut V)) * Nat.card (fixV Λ ⊔ fixV B : Subgroup V) ≤
      Nat.card B * Nat.card (fixV B) := (Nat.mul_le_mul_left _ h3).trans h4
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos hpos1 hpos2)
  calc Nat.card Λ * Nat.card (fixV Λ) * (Nat.card (Λ ⊓ B : Subgroup (MulAut V)) *
        Nat.card (fixV Λ ⊔ fixV B : Subgroup V))
      ≤ Nat.card Λ * Nat.card (fixV Λ) * (Nat.card B * Nat.card (fixV B)) :=
        Nat.mul_le_mul_left _ hbd
    _ = (Nat.card Λ * Nat.card B) *
        (Nat.card (fixV Λ ⊔ fixV B : Subgroup V) * Nat.card (fixV Λ ⊓ fixV B : Subgroup V)) := by
        rw [h2]
        ring
    _ ≤ (Nat.card (Λ ⊔ B : Subgroup (MulAut V)) * Nat.card (Λ ⊓ B : Subgroup (MulAut V))) *
        (Nat.card (fixV Λ ⊔ fixV B : Subgroup V) * Nat.card (fixV Λ ⊓ fixV B : Subgroup V)) :=
        Nat.mul_le_mul_right _ h1
    _ = Nat.card (Λ ⊔ B : Subgroup (MulAut V)) * Nat.card (fixV Λ ⊓ fixV B : Subgroup V) *
        (Nat.card (Λ ⊓ B : Subgroup (MulAut V)) * Nat.card (fixV Λ ⊔ fixV B : Subgroup V)) := by
        ring

theorem card_le_weight_closure_conj {G A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    (ks : List (MulAut V)) (hks : ∀ k ∈ ks, k ∈ G) :
    Nat.card V ≤ Nat.card (Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹}) *
      Nat.card (fixV (Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹})) := by
  induction ks with
  | nil =>
    have h : {y : MulAut V | ∃ k ∈ ([] : List (MulAut V)), ∃ a ∈ A, y = k * a * k⁻¹} = ∅ := by
      ext y
      simp
    rw [h, Subgroup.closure_empty, B1.card_bot_mul_card_fixV]
  | cons k ks ih =>
    have ih' := ih (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
    set Λ := Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹} with hΛ
    have hset : {y | ∃ k' ∈ k :: ks, ∃ a ∈ A, y = k' * a * k'⁻¹} =
        {y | ∃ k' ∈ ks, ∃ a ∈ A, y = k' * a * k'⁻¹} ∪ (B1.conjAut k A : Set (MulAut V)) := by
      ext y
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union, SetLike.mem_coe,
        B1.mem_conjAut]
      constructor
      · rintro ⟨k', hk' | hk', a, ha, rfl⟩
        · subst hk'
          right
          simpa [mul_assoc] using ha
        · exact Or.inl ⟨k', hk', a, ha, rfl⟩
      · rintro (⟨k', hk', a, ha, rfl⟩ | h)
        · exact ⟨k', Or.inr hk', a, ha, rfl⟩
        · exact ⟨k, Or.inl rfl, k⁻¹ * y * k, h, by group⟩
    have hcl : Subgroup.closure {y | ∃ k' ∈ k :: ks, ∃ a ∈ A, y = k' * a * k'⁻¹} =
        Λ ⊔ B1.conjAut k A := by
      rw [hset, Subgroup.closure_union, Subgroup.closure_eq]
    rw [hcl]
    exact ih'.trans (weight_le_weight_sup
      (B1.isFFStarOffender_conjAut hA (hks k List.mem_cons_self)))

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
