module

public import CFSG.CGT.PushingUpLit.BHS.Offender
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def JSplit (X B : Subgroup (MulAut V)) : Prop :=
  ∃ X₀ : Subgroup (MulAut V), X₀ ≤ X ∧ X₀ ≠ X ∧ wt X ≤ wt X₀ ∧ X ≤ B ⊔ X₀

theorem jSplit_of_cen {X B : Subgroup (MulAut V)} {W : Subgroup V} (hXoff : IsOff X)
    (hBX : B ≤ X) (hidx : (fixV X).relIndex W = (cenIn X W).relIndex X)
    (hdec : ∀ x ∈ X, ∃ b ∈ B, ∀ w ∈ W, x w = b w) (hB : ∃ b ∈ B, ∃ w ∈ W, b w ≠ w) :
    ∃ X₀ : Subgroup (MulAut V), X₀ ≤ X ∧ X₀ ≠ X ∧ wt X ≤ wt X₀ ∧ X ≤ B ⊔ X₀ := by
  refine ⟨cenIn X W, cenIn_le X W, ?_, ?_, ?_⟩
  · intro heq
    obtain ⟨b, hb, w, hw, hne⟩ := hB
    have : b ∈ cenIn X W := by rw [heq]; exact hBX hb
    exact hne (this.2 w hw)
  · obtain ⟨h1, -, h3⟩ := offender_chain hXoff W
    rw [hidx] at h1
    rw [h3]
    exact h1
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := hdec x hx
    have hx₀ : b⁻¹ * x ∈ cenIn X W := by
      refine ⟨X.mul_mem (X.inv_mem (hBX hb)) hx, fun w hw => ?_⟩
      show (b⁻¹ * x) w = w
      rw [MulAut.mul_apply, hxb w hw]
      exact MulAut.inv_apply_self V b w
    have : x = b * (b⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hb hx₀

theorem jSplit_of_point {X : Subgroup (MulAut V)} {b₀ : MulAut V} (hb₀ : b₀ ∈ X) {w₁ : V}
    (hb₀w : b₀ w₁ ≠ w₁) (hx : ∀ x ∈ X, x w₁ = w₁ ∨ (b₀ * x) w₁ = w₁) :
    ∃ X₀ : Subgroup (MulAut V), X₀ ≤ X ∧ X₀ ≠ X ∧ wt X ≤ wt X₀ ∧
      X ≤ Subgroup.zpowers b₀ ⊔ X₀ := by
  classical
  set X₀ : Subgroup (MulAut V) := X ⊓ MulAction.stabilizer (MulAut V) w₁ with hX₀
  have hmem : ∀ x, x ∈ X₀ ↔ x ∈ X ∧ x w₁ = w₁ := fun x => by
    rw [hX₀, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  have hX₀X : X₀ ≤ X := inf_le_left
  have hne : X₀ ≠ X := by
    intro heq
    have : b₀ ∈ X₀ := heq ▸ hb₀
    exact hb₀w ((hmem b₀).1 this).2
  have hsplit : ∀ x ∈ X, x ∈ X₀ ∨ b₀ * x ∈ X₀ := by
    intro x hxX
    rcases hx x hxX with h | h
    · exact Or.inl ((hmem x).2 ⟨hxX, h⟩)
    · exact Or.inr ((hmem _).2 ⟨X.mul_mem hb₀ hxX, h⟩)
  refine ⟨X₀, hX₀X, hne, ?_, ?_⟩
  ·
    have hcard : Nat.card X ≤ Nat.card X₀ + Nat.card X₀ := by
      rw [← Nat.card_sum]
      let f : X → X₀ ⊕ X₀ := fun x =>
        if h : (x : MulAut V) ∈ X₀ then Sum.inl ⟨x, h⟩ else
          Sum.inr ⟨b₀ * x, (hsplit x x.2).resolve_left h⟩
      refine Nat.card_le_card_of_injective f ?_
      intro x y hxy
      by_cases hx₀ : (x : MulAut V) ∈ X₀ <;> by_cases hy₀ : (y : MulAut V) ∈ X₀ <;>
        simp only [f, hx₀, hy₀, dite_true, dite_false] at hxy
      · exact Subtype.ext (congrArg (fun z : X₀ => (z : MulAut V)) (Sum.inl.inj hxy))
      · exact absurd hxy (by simp)
      · exact absurd hxy (by simp)
      · have := congrArg (fun z : X₀ => (z : MulAut V)) (Sum.inr.inj hxy)
        exact Subtype.ext (mul_left_cancel this)
    have hrel := Subgroup.relIndex_mul_card (H := X₀) (K := X)
    rw [inf_eq_left.2 hX₀X] at hrel
    have hrel2 : X₀.relIndex X ≤ 2 := by
      by_contra h3
      push Not at h3
      have : 2 * Nat.card X₀ + Nat.card X₀ ≤ Nat.card X := by
        rw [← hrel]
        nlinarith
      have hpos : 0 < Nat.card X₀ := Nat.card_pos
      omega
    have hrel1 : X₀.relIndex X ≠ 1 := fun h1 =>
      hne (le_antisymm hX₀X (Subgroup.relIndex_eq_one.1 h1))
    have hrel0 : X₀.relIndex X ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hrel
      exact Nat.card_pos.ne' hrel.symm
    have hcardX : Nat.card X = 2 * Nat.card X₀ := by
      have h2 : X₀.relIndex X = 2 := by omega
      rw [← hrel, h2]
    have hfix : fixV X ≤ fixV X₀ := fun v hv x hx => hv x (hX₀X hx)
    have hw₁X₀ : w₁ ∈ fixV X₀ := fun x hx => ((hmem x).1 hx).2
    have hw₁X : w₁ ∉ fixV X := fun h => hb₀w (h b₀ hb₀)
    have hrelV := Subgroup.relIndex_mul_card (H := fixV X) (K := fixV X₀)
    rw [inf_eq_left.2 hfix] at hrelV
    have hrelV1 : (fixV X).relIndex (fixV X₀) ≠ 1 := fun h1 =>
      hw₁X ((Subgroup.relIndex_eq_one.1 h1) hw₁X₀)
    have hrelV0 : (fixV X).relIndex (fixV X₀) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hrelV
      exact Nat.card_pos.ne' hrelV.symm
    have hge2 : 2 ≤ (fixV X).relIndex (fixV X₀) := by omega
    unfold wt
    calc Nat.card X * Nat.card (fixV X) = 2 * Nat.card X₀ * Nat.card (fixV X) := by rw [hcardX]
      _ ≤ Nat.card X₀ * ((fixV X).relIndex (fixV X₀) * Nat.card (fixV X)) := by
        have h1 : 2 * Nat.card (fixV X) ≤ (fixV X).relIndex (fixV X₀) * Nat.card (fixV X) :=
          Nat.mul_le_mul_right _ hge2
        calc 2 * Nat.card X₀ * Nat.card (fixV X) = Nat.card X₀ * (2 * Nat.card (fixV X)) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ h1
      _ = Nat.card X₀ * Nat.card (fixV X₀) := by rw [hrelV]
  · intro x hxX
    rcases hsplit x hxX with h | h
    · exact Subgroup.mem_sup_right h
    · have : x = b₀⁻¹ * (b₀ * x) := by group
      rw [this]
      exact Subgroup.mul_mem_sup (Subgroup.inv_mem _ (Subgroup.mem_zpowers b₀)) h

end CFSG.CGT.PushingUpLit.BHS5
