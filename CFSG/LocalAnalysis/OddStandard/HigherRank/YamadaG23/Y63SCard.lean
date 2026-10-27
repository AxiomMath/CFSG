module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63MSub

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Y63Chk

variable {D : Data} [Group Y63TG]

theorem y63_card_list {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ a ∈ l, a < 512) :
    Nat.card {x : Y63TG // x.val ∈ l} = l.length := by
  classical
  let e : {x : Y63TG // x.val ∈ l} ≃ ↥l.toFinset :=
    { toFun := fun x => ⟨x.1.val, List.mem_toFinset.mpr x.2⟩
      invFun := fun a => ⟨⟨a.1, hlt a.1 (List.mem_toFinset.mp a.2)⟩, List.mem_toFinset.mp a.2⟩
      left_inv := fun x => rfl
      right_inv := fun a => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

@[expose] def y63ListSub (hmul : ∀ x y : Y63TG, (x * y).val = D.mt x.val y.val)
    (h1 : (1 : Y63TG).val = 0) (hI : D.InvSpec) {l : List ℕ} (h0 : 0 ∈ l)
    (hcl : ∀ a ∈ l, ∀ b ∈ l, D.mt a b ∈ l) (hinv : ∀ a ∈ l, D.iv a ∈ l) : Subgroup Y63TG where
  carrier := {x | x.val ∈ l}
  mul_mem' := fun {a b} ha hb => by
    show (a * b).val ∈ l
    rw [hmul]
    exact hcl _ ha _ hb
  one_mem' := by
    show (1 : Y63TG).val ∈ l
    rw [h1]
    exact h0
  inv_mem' := fun {a} ha => by
    show (a⁻¹).val ∈ l
    rw [y63_inv_val hmul h1 hI]
    exact hinv _ ha

theorem mem_y63ListSub (hmul : ∀ x y : Y63TG, (x * y).val = D.mt x.val y.val)
    (h1 : (1 : Y63TG).val = 0) (hI : D.InvSpec) {l : List ℕ} (h0 : 0 ∈ l)
    (hcl : ∀ a ∈ l, ∀ b ∈ l, D.mt a b ∈ l) (hinv : ∀ a ∈ l, D.iv a ∈ l) (x : Y63TG) :
    x ∈ y63ListSub hmul h1 hI h0 hcl hinv ↔ x.val ∈ l :=
  Iff.rfl

theorem y63ListSub_card (hmul : ∀ x y : Y63TG, (x * y).val = D.mt x.val y.val)
    (h1 : (1 : Y63TG).val = 0) (hI : D.InvSpec) {l : List ℕ} (h0 : 0 ∈ l)
    (hcl : ∀ a ∈ l, ∀ b ∈ l, D.mt a b ∈ l) (hinv : ∀ a ∈ l, D.iv a ∈ l) (hnd : l.Nodup)
    (hlt : ∀ a ∈ l, a < 512) : Nat.card ↥(y63ListSub hmul h1 hI h0 hcl hinv) = l.length := by
  rw [← y63_card_list hnd hlt]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => mem_y63ListSub hmul h1 hI h0 hcl hinv x))

end CFSG.OddStandard.HigherRank.YamadaG23
