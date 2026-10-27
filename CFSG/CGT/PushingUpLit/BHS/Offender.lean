module

public import CFSG.CGT.PushingUpLit.BHS.Replacement

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.B1

variable {V : Type*} [CommGroup V]

@[expose] def IsOff (A : Subgroup (MulAut V)) : Prop :=
  IsFFStarOffender (⊤ : Subgroup (MulAut V)) A

@[expose] def IsOffStar (A : Subgroup (MulAut V)) : Prop :=
  IsOff A ∧ Nat.card V < wt A

theorem offender_iff {G A : Subgroup (MulAut V)} :
    IsFFStarOffender G A ↔ A ≤ G ∧ IsOff A :=
  ⟨fun h => ⟨h.1, ⟨le_top, h.2⟩⟩, fun h => ⟨h.1, h.2.2⟩⟩

@[expose] noncomputable def offMax (G : Subgroup (MulAut V)) : ℕ :=
  sSup {n | ∃ A : Subgroup (MulAut V), A ≤ G ∧ IsOff A ∧ wt A = n}

@[expose] def IsAOff (G A : Subgroup (MulAut V)) : Prop :=
  A ≤ G ∧ IsOff A ∧ wt A = offMax G ∧
    ∀ B : Subgroup (MulAut V), B ≤ A → IsOff B → wt B = offMax G → B = A

theorem isElemAbelian2_mono' {A B : Subgroup (MulAut V)} (h : IsElemAbelian2 A) (hBA : B ≤ A) :
    IsElemAbelian2 B :=
  ⟨fun a ha b hb => h.1 a (hBA ha) b (hBA hb), fun a ha => h.2 a (hBA ha)⟩

section Lemma28

variable [Finite V]

theorem card_sup_eq_relIndex_mul (W Y : Subgroup V) :
    Nat.card ↥(W ⊔ Y) = Y.relIndex W * Nat.card Y := by
  have h1 := card_sup_mul_card_inf' (X := W) (Y := Y) (fun x _ y _ => mul_comm x y)
  have h2 := Subgroup.relIndex_mul_card Y W
  rw [inf_comm] at h2
  have hpos : 0 < Nat.card ↥(W ⊓ Y) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, ← h2]
  ring

omit [Finite V] in
theorem relIndex_cenIn_mul_card (A : Subgroup (MulAut V)) (W : Subgroup V) :
    (cenIn A W).relIndex A * Nat.card (cenIn A W) = Nat.card A := by
  have := Subgroup.relIndex_mul_card (cenIn A W) A
  rwa [inf_eq_left.2 (cenIn_le A W)] at this

theorem IsOff.card_le_wt {A : Subgroup (MulAut V)} (hA : IsOff A) : Nat.card V ≤ wt A := by
  have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
  rwa [card_bot_mul_card_fixV] at this

theorem offender_chain {A : Subgroup (MulAut V)} (hA : IsOff A) (W : Subgroup V) :
    Nat.card (cenIn A W) * ((fixV A).relIndex W * Nat.card (fixV A)) ≤ wt (cenIn A W) ∧
      wt (cenIn A W) ≤ wt A ∧
      wt A = Nat.card (cenIn A W) * ((cenIn A W).relIndex A * Nat.card (fixV A)) := by
  have hA₀ : cenIn A W ≤ A := cenIn_le A W
  have h2 : W ⊔ fixV A ≤ fixV (cenIn A W) :=
    sup_le (fun w hw a ha => ha.2 w hw) (fixV_le_fixV hA₀)
  refine ⟨?_, hA.card_le hA₀, ?_⟩
  · rw [← card_sup_eq_relIndex_mul]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le h2)
  · unfold wt
    rw [← relIndex_cenIn_mul_card A W]
    ring

theorem offender_card_le {A : Subgroup (MulAut V)} (hA : IsOff A) (W : Subgroup V) :
    (fixV A).relIndex W ≤ (cenIn A W).relIndex A := by
  obtain ⟨h1, h2, h3⟩ := offender_chain hA W
  have h5 : Nat.card (cenIn A W) * ((fixV A).relIndex W * Nat.card (fixV A)) ≤
      Nat.card (cenIn A W) * ((cenIn A W).relIndex A * Nat.card (fixV A)) := by
    rw [← h3]
    exact h1.trans h2
  have h6 := Nat.le_of_mul_le_mul_left h5 Nat.card_pos
  exact Nat.le_of_mul_le_mul_right h6 Nat.card_pos

theorem offender_card_lt_or {A : Subgroup (MulAut V)} (hA : IsOffStar A) (W : Subgroup V) :
    (fixV A).relIndex W < (cenIn A W).relIndex A ∨ IsOffStar (cenIn A W) := by
  by_cases hlt : (fixV A).relIndex W < (cenIn A W).relIndex A
  · exact Or.inl hlt
  right
  have hA₀ : cenIn A W ≤ A := cenIn_le A W
  have heq : (fixV A).relIndex W = (cenIn A W).relIndex A :=
    le_antisymm (offender_card_le hA.1 W) (not_lt.1 hlt)
  obtain ⟨h1, h2, h3⟩ := offender_chain hA.1 W
  rw [heq, ← h3] at h1
  have hw : wt (cenIn A W) = wt A := le_antisymm h2 h1
  refine ⟨⟨le_top, ?_, isElemAbelian2_mono' hA.1.2.2.1 hA₀, fun B hB => ?_⟩, ?_⟩
  · intro hbot
    have : wt (cenIn A W) = Nat.card V := by
      unfold wt
      rw [hbot, Subgroup.card_bot, one_mul, B1.fixV_bot, Subgroup.card_top]
    rw [hw] at this
    exact absurd hA.2 (by omega)
  · have := hA.1.card_le (hB.trans hA₀)
    unfold wt at hw
    rw [hw]
    exact this
  · rw [hw]
    exact hA.2

end Lemma28

end CFSG.CGT.PushingUpLit.BHS
