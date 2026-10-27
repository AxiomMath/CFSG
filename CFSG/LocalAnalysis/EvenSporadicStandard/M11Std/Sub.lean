module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Setting

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

@[expose] def subOf (p : SMod → Prop) (hmul : ∀ x y, p x → p y → p (SMod.mul x y))
    (hone : p SMod.one) (hinv : ∀ x, p x → p (SMod.inv x)) : Subgroup G where
  carrier := {g | ∃ x, p x ∧ H.psi x = g}
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨SMod.mul x y, hmul x y hx hy, H.psi_mul x y⟩
  one_mem' := ⟨SMod.one, hone, H.psi_one⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨SMod.inv x, hinv x hx, H.psi_inv x⟩

theorem card_subOf (p : SMod → Prop) [DecidablePred p] (hmul hone hinv) :
    Nat.card (H.subOf p hmul hone hinv) = (Finset.univ.filter p).card := by
  have e : {x : SMod // p x} ≃ H.subOf p hmul hone hinv :=
    Equiv.ofBijective (fun x => ⟨H.psi x.1, x.1, x.2, rfl⟩)
      ⟨fun x y h => Subtype.ext (H.psi_injective (congrArg Subtype.val h)), by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

@[expose] def S : Subgroup G :=
  H.subOf (fun _ => True) (fun _ _ _ _ => trivial) trivial (fun _ _ => trivial)

@[expose] def W : Subgroup G :=
  H.subOf SMod.inW SMod.inW_mul (by decide) SMod.inW_inv

@[expose] def E1 : Subgroup G :=
  H.subOf SMod.inE1 SMod.inE1_mul (by decide) SMod.inE1_inv

@[expose] def E2 : Subgroup G :=
  H.subOf SMod.inE2 SMod.inE2_mul (by decide) SMod.inE2_inv

@[expose] def H0 : Subgroup G :=
  H.subOf SMod.inH SMod.inH_mul (by decide) SMod.inH_inv

theorem card_S : Nat.card H.S = 32 := by
  rw [S, card_subOf]; decide

theorem card_W : Nat.card H.W = 4 := by
  rw [W, card_subOf]; exact SMod.card_inW

theorem card_E1 : Nat.card H.E1 = 8 := by
  rw [E1, card_subOf]; exact SMod.card_inE1

theorem card_H0 : Nat.card H.H0 = 16 := by
  rw [H0, card_subOf]; exact SMod.card_inH

theorem psi_mem_S (x : SMod) : H.psi x ∈ H.S := ⟨x, trivial, rfl⟩

theorem mem_S {g : G} : g ∈ H.S ↔ ∃ x, H.psi x = g := ⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ =>
  ⟨x, trivial, h⟩⟩

theorem psi_tt : H.psi SMod.tt = H.t := by
  simp [psi, psiN, SMod.tt]

theorem psi_bb : H.psi SMod.bb = H.b := by
  simp [psi, psiN, SMod.bb]

theorem psi_aa : H.psi SMod.aa = H.a := by
  simp [psi, psiN, SMod.aa]

theorem psi_zz : H.psi SMod.zz = H.a ^ 4 := by
  simp [psi, psiN, SMod.zz]

theorem t_mem_S : H.t ∈ H.S := H.psi_tt ▸ H.psi_mem_S _
theorem a_mem_S : H.a ∈ H.S := H.psi_aa ▸ H.psi_mem_S _
theorem b_mem_S : H.b ∈ H.S := H.psi_bb ▸ H.psi_mem_S _
theorem t_mem_W : H.t ∈ H.W := ⟨SMod.tt, by decide, H.psi_tt⟩
theorem z_mem_W : H.a ^ 4 ∈ H.W := ⟨SMod.zz, by decide, H.psi_zz⟩
theorem W_le_S : H.W ≤ H.S := fun _ ⟨x, _, h⟩ => ⟨x, trivial, h⟩
theorem H0_le_S : H.H0 ≤ H.S := fun _ ⟨x, _, h⟩ => ⟨x, trivial, h⟩
theorem W_le_E1 : H.W ≤ H.E1 := fun _ ⟨x, hx, h⟩ => ⟨x, SMod.inW_inE1 x hx, h⟩
theorem W_le_E2 : H.W ≤ H.E2 := fun _ ⟨x, hx, h⟩ => ⟨x, SMod.inW_inE2 x hx, h⟩

end Setting

end CFSG.EvenSporadicStandard.M11Std
