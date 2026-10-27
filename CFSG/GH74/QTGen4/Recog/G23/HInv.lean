module

public import CFSG.Quasithin.Recognition.G23TypeDefs

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Quasithin.G23Type

variable {G : Type} [Group G]

theorem exists_invol_not_mem [Finite G] {T K : Subgroup G}
    (hK : Nat.card {k : ↥K // orderOf k = 2} ≤ 19)
    (hcount : 19 < Nat.card {t : ↥T // orderOf t = 2}) :
    ∃ w ∈ T, orderOf w = 2 ∧ w ∉ K := by
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  have hord : ∀ t : {t : ↥T // orderOf t = 2}, orderOf (t.1 : G) = 2 := fun t => by
    rw [Subgroup.orderOf_coe]; exact t.2
  let f : {t : ↥T // orderOf t = 2} → {k : ↥K // orderOf k = 2} := fun t =>
    ⟨⟨(t.1 : G), hne _ t.1.2 (hord t)⟩, by rw [Subgroup.orderOf_mk]; exact hord t⟩
  have hinj : Function.Injective f := by
    intro t s h
    exact Subtype.ext (Subtype.ext (congrArg (fun x => x.1.1) h))
  have hle : Nat.card {t : ↥T // orderOf t = 2} ≤ Nat.card {k : ↥K // orderOf k = 2} :=
    Nat.card_le_card_of_injective f hinj
  omega

theorem G23One.exists_invol_outside [Finite G] {H H₁ H₂ T : Subgroup G} (_hH : G23One H H₁ H₂)
    (hK : Nat.card {k : ↥(H₁ ⊔ H₂) // orderOf k = 2} ≤ 19)
    (hcount : 19 < Nat.card {t : ↥T // orderOf t = 2}) :
    ∃ w ∈ T, orderOf w = 2 ∧ w ∉ H₁ ⊔ H₂ :=
  exists_invol_not_mem hK hcount

end CFSG.GH74.QTGen4.Recog.G23
