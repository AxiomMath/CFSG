module

public import CFSG.GH74.QTGen4.Recog.Ku.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

variable {G : Type} [Group G]

namespace KuA6Model

variable {E W V2 N : Subgroup G} {z : G}

theorem Φ_zero (Ψ : KuA6Model E W V2 N z) : Ψ.Φ 0 = 1 := by
  have h := Ψ.add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := Ψ.Φ 0) (by rw [mul_one]; exact h.symm)

theorem card_E (Ψ : KuA6Model E W V2 N z) : Nat.card E = 16 := by
  have hbij : Function.Bijective (fun v : SpV => (⟨Ψ.Φ v, Ψ.mem v⟩ : E)) := by
    constructor
    · intro v w hvw
      exact Ψ.inj (congrArg Subtype.val hvw)
    · rintro ⟨x, hx⟩
      obtain ⟨v, rfl⟩ := Ψ.surj x hx
      exact ⟨v, rfl⟩
  have h16 : Nat.card SpV = 16 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [← h16]
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

end KuA6Model

end CFSG.GH74.QTGen4.Ku
