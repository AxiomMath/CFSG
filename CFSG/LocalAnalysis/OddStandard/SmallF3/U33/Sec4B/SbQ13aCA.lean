module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem ut3_card_cent : ∀ x : UT3 F4c, (∃ g : UT3 F4c, g * x ≠ x * g) →
    Fintype.card {y : UT3 F4c // y * x = x * y} = 16 := by
  decide +kernel

theorem card_cent_of_equiv {T : Type} [Group T] (e : T ≃* SylSL3_4) {x : T}
    (hx : ∃ g : T, g * x ≠ x * g) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set T)) = 16 := by
  let f : T ≃* UT3 F4c := e.trans sylLCongr
  obtain ⟨g, hg⟩ := hx
  have hg' : f g * f x ≠ f x * f g := by
    intro h
    apply hg
    apply f.injective
    rw [map_mul, map_mul]
    exact h
  have hc := ut3_card_cent (f x) ⟨f g, hg'⟩
  rw [← Nat.card_eq_fintype_card] at hc
  rw [← hc]
  apply Nat.card_congr
  refine Equiv.subtypeEquiv f.toEquiv ?_
  intro y
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    show f y * f x = f x * f y
    rw [← map_mul, ← map_mul, h]
  · intro h
    apply f.injective
    rw [map_mul, map_mul]
    exact h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
