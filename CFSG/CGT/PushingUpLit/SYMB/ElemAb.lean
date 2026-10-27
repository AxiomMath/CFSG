module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.CGT.PushingUpLit.BHS.Defs
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped Pointwise

variable {Γ : Type} [Group Γ]

theorem elemAb_comm {A : Subgroup Γ} (h : IsElemAbelian 2 A) {a b : Γ} (ha : a ∈ A)
    (hb : b ∈ A) : a * b = b * a := CFSG.Open.IsElemAbelian.comm h ha hb

theorem elemAb_sq {A : Subgroup Γ} (h : IsElemAbelian 2 A) {a : Γ} (ha : a ∈ A) :
    a * a = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one h ha

theorem isElemAbelian_of_le' {A B : Subgroup Γ} (h : IsElemAbelian 2 B) (hAB : A ≤ B) :
    IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono h hAB

theorem isElemAbelian_sup_of_commute {C D : Subgroup Γ} (hC : IsElemAbelian 2 C)
    (hD : IsElemAbelian 2 D) (h : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c) :
    IsElemAbelian 2 (C ⊔ D) := CFSG.Open.IsElemAbelian.sup_of_commute hC hD h

variable [Finite Γ] {T : Subgroup Γ}

theorem maxElemAb_le_of_commute {A X : Subgroup Γ} (hA : IsMaxElemAbelian T A)
    (hX : IsElemAbelian 2 X) (hXT : X ≤ T) (h : ∀ x ∈ X, ∀ a ∈ A, x * a = a * x) : X ≤ A := by
  have hj : IsElemAbelian 2 (A ⊔ X) :=
    isElemAbelian_sup_of_commute hA.2.1 hX fun a ha x hx => (h x hx a ha).symm
  have hle : Nat.card ↥(A ⊔ X) ≤ Nat.card ↥A := hA.2.2 _ (sup_le hA.1 hXT) hj
  have heq : A ⊔ X = A := (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm
  exact heq ▸ le_sup_right

omit [Finite Γ] in
theorem isMaxElemAbelian_of_card_eq {A B : Subgroup Γ} (hA : IsMaxElemAbelian T A)
    (hBT : B ≤ T) (hB : IsElemAbelian 2 B) (hcard : Nat.card ↥B = Nat.card ↥A) :
    IsMaxElemAbelian T B :=
  ⟨hBT, hB, fun B' hB'T hB' => by rw [hcard]; exact hA.2.2 B' hB'T hB'⟩

end CFSG.CGT.PushingUpLit.SYMB
