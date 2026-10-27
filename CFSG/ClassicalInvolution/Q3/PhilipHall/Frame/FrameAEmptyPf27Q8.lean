module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.IndexNormal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Out

@[expose] def Idx2 (A : Type) [Group A] : Type := {H : Subgroup A // Nat.card A = 2 * Nat.card H}

section Generic

variable {A B : Type} [Group A] [Group B]

instance [Finite A] : Finite (Idx2 A) :=
  haveI : Finite (Subgroup A) :=
    Finite.of_injective (SetLike.coe : Subgroup A → Set A) SetLike.coe_injective
  inferInstanceAs (Finite {H : Subgroup A // Nat.card A = 2 * Nat.card H})

def Idx2.congr (e : A ≃* B) : Idx2 A ≃ Idx2 B where
  toFun H := ⟨H.1.map e.toMonoidHom, by
    rw [Subgroup.card_map_of_injective e.injective, ← Nat.card_congr e.toEquiv]
    exact H.2⟩
  invFun H := ⟨H.1.map e.symm.toMonoidHom, by
    rw [Subgroup.card_map_of_injective e.symm.injective, Nat.card_congr e.toEquiv]
    exact H.2⟩
  left_inv H := by
    apply Subtype.ext
    apply Subgroup.ext
    intro x
    simp [Subgroup.mem_map_equiv]
  right_inv H := by
    apply Subtype.ext
    apply Subgroup.ext
    intro x
    simp [Subgroup.mem_map_equiv]

theorem Idx2.congr_mem (e : A ≃* B) (H : Idx2 A) (x : B) :
    x ∈ (Idx2.congr e H).1 ↔ e.symm x ∈ H.1 :=
  Subgroup.mem_map_equiv

theorem Idx2.congr_symm_mem (e : A ≃* B) (H : Idx2 B) (y : A) :
    y ∈ ((Idx2.congr e).symm H).1 ↔ e y ∈ H.1 := by
  show y ∈ H.1.map e.symm.toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp

def Idx2.act : MulAut A →* Equiv.Perm (Idx2 A) where
  toFun α := (Idx2.congr (A := A) (B := A) α)
  map_one' := by
    apply Equiv.ext
    intro H
    apply Subtype.ext
    apply Subgroup.ext
    intro x
    exact Idx2.congr_mem (A := A) (B := A) 1 H x
  map_mul' α β := by
    apply Equiv.ext
    intro H
    apply Subtype.ext
    apply Subgroup.ext
    intro x
    show x ∈ (Idx2.congr (A := A) (B := A) (α * β) H).1 ↔
      x ∈ (Idx2.congr (A := A) (B := A) α (Idx2.congr (A := A) (B := A) β H)).1
    rw [Idx2.congr_mem, Idx2.congr_mem, Idx2.congr_mem]
    rfl

theorem Idx2.act_apply (α : MulAut A) (H : Idx2 A) (x : A) :
    x ∈ (Idx2.act α H).1 ↔ α.symm x ∈ H.1 :=
  Idx2.congr_mem (A := A) (B := A) α H x

theorem Idx2.normal [Finite A] (H : Idx2 A) : H.1.Normal := by
  have h1 : H.1.index = 2 := by
    have h0 := H.1.card_mul_index
    have h2 := H.2
    have hpos : 0 < Nat.card H.1 := Nat.card_pos
    have : Nat.card H.1 * H.1.index = Nat.card H.1 * 2 := by omega
    exact Nat.eq_of_mul_eq_mul_left hpos this
  exact Subgroup.normal_of_index_eq_two h1

theorem Idx2.act_inner [Finite A] (g : A) : Idx2.act (MulAut.conj g) = 1 := by
  apply Equiv.ext
  intro H
  apply Subtype.ext
  apply Subgroup.ext
  intro x
  have := H.normal
  rw [Idx2.act_apply]
  show _ ↔ x ∈ H.1
  have e : (MulAut.conj g).symm x = g⁻¹ * x * g := by
    simp [MulAut.conj_symm_apply]
  rw [e]
  constructor
  · intro h
    have := H.normal.conj_mem _ h g
    simpa [mul_assoc] using this
  · intro h
    have := H.normal.conj_mem x h g⁻¹
    simpa using this

end Generic

section Q8

abbrev Q8 : Type := QuaternionGroup 2

@[expose] def IdxFin (s : Finset Q8) : Prop :=
  (1 : Q8) ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧ (∀ a ∈ s, a⁻¹ ∈ s) ∧ s.card = 4

instance (s : Finset Q8) : Decidable (IdxFin s) :=
  inferInstanceAs (Decidable ((1 : Q8) ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) ∧
    (∀ a ∈ s, a⁻¹ ∈ s) ∧ s.card = 4))

theorem card_idxFin : Fintype.card {s : Finset Q8 // IdxFin s} = 3 := by decide +kernel

@[expose] def mkSub (s : Finset Q8) (hs : IdxFin s) : Subgroup Q8 where
  carrier := {x | x ∈ s}
  one_mem' := hs.1
  mul_mem' := fun {a b} ha hb => hs.2.1 a ha b hb
  inv_mem' := fun {a} ha => hs.2.2.1 a ha

theorem card_mkSub (s : Finset Q8) (hs : IdxFin s) : Nat.card (mkSub s hs) = s.card := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (p := fun x => x ∈ mkSub s hs)
    (q := fun x => x ∈ s) (fun x => Iff.rfl)), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem card_q8 : Nat.card Q8 = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

open Classical in
noncomputable def idx2Q8Equiv : Idx2 Q8 ≃ {s : Finset Q8 // IdxFin s} where
  toFun H := ⟨Finset.univ.filter (fun x => x ∈ H.1), by
    refine ⟨by simp [H.1.one_mem], ?_, ?_, ?_⟩
    · intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
      exact H.1.mul_mem ha hb
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
      exact H.1.inv_mem ha
    · have h2 := H.2
      have hc : Nat.card H.1 = (Finset.univ.filter (fun x => x ∈ H.1)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have := card_q8
      omega⟩
  invFun s := ⟨mkSub s.1 s.2, by
    rw [card_mkSub, s.2.2.2.2, card_q8]⟩
  left_inv H := by
    apply Subtype.ext
    apply Subgroup.ext
    intro x
    simp [mkSub]
  right_inv s := by
    apply Subtype.ext
    ext x
    simp [mkSub]

theorem card_idx2_q8 : Nat.card (Idx2 Q8) = 3 := by
  rw [Nat.card_congr idx2Q8Equiv, Nat.card_eq_fintype_card, card_idxFin]

theorem card_idx2_of_equiv_q8 {A : Type} [Group A] (e : A ≃* Q8) : Nat.card (Idx2 A) = 3 := by
  rw [Nat.card_congr (Idx2.congr e), card_idx2_q8]

end Q8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Out
