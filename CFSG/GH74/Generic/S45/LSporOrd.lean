module

public import CFSG.GH74.Generic.S45.LSporRows
public import CFSG.GH74.Generic.S45.LSporMathA
public import CFSG.GH74.Generic.S45.LSporMathB
public import CFSG.GH74.Generic.S45.LSporJ3

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.GH74.Uniqueness.Bender

theorem sporRow_of_cls_list {s : TauCeti.SporadicName} (cs : List ℕ)
    (hcl : ∀ (S : Type) [Group S], (S ≃* NativeSporadic.Carrier s) → ∀ α : MulAut S, α * α = 1 →
      α ≠ 1 → OrdClosable (Nat.card ↥(autFixed α)) ∨ Nat.card ↥(autFixed α) ∈ cs)
    (hcs : ∀ c ∈ cs, SporRowCls s c) : SporRow s := by
  intro K _ _ y L hyp hS
  obtain ⟨e⟩ := hS
  obtain ⟨yb, Lb, q, hyb, hQ, -⟩ := hyp.quot_data
  rcases hcl _ e yb hQ.sq hQ.ne with hc | hc
  · exact false_of_fixed_card hQ hc
  · exact hcs _ hc K y L hyp ⟨e⟩ yb hyb rfl

theorem sporRow_m11 :
    SporRow .M11 :=
  sporRow_of_cls_list [] (fun S _ e α h2 h1 => Or.inl (by
    have e' : S ≃* NativeSporadic.M11 := e
    rw [← card_fixed_congr' e' α]
    rw [LAlt.m11_fixed_card (MulAut.congr e' α) (by rw [← map_mul, h2, map_one]) (by
      intro h
      exact h1 ((MulAut.congr e').injective (by rw [h, map_one])))]
    exact ordClosable_48)) (fun c hc => by simp at hc)

theorem sporRow_m22 :
    SporRow .M22 :=
  sporRow_of_cls_list [] (fun S _ e α h2 h1 => Or.inl (by
    have e' : S ≃* NativeSporadic.M22 := e
    rw [← card_fixed_congr' e' α]
    rcases m22_fixed_card (MulAut.congr e' α) (by rw [← map_mul, h2, map_one]) (by
      intro h
      exact h1 ((MulAut.congr e').injective (by rw [h, map_one]))) with h | h | h <;> rw [h]
    · exact ordClosable_384
    · exact ordClosable_320
    · exact ordClosable_1344)) (fun c hc => by simp at hc)

theorem sporRow_m23 :
    SporRow .M23 :=
  sporRow_of_cls_list [] (fun S _ e α h2 h1 => Or.inl (by
    have e' : S ≃* NativeSporadic.M23 := e
    rw [← card_fixed_congr' e' α]
    rw [LAlt.m23_fixed_card (MulAut.congr e' α) (by rw [← map_mul, h2, map_one]) (by
      intro h
      exact h1 ((MulAut.congr e').injective (by rw [h, map_one])))]
    exact ordClosable_2688)) (fun c hc => by simp at hc)

theorem sporRow_j3
    (h : SporRowCls .J3 1920) :
    SporRow .J3 :=
  sporRow_of_cls_list [1920] (fun S _ e α h2 h1 => by
    rcases j3_fixed_card e α h2 h1 with hc | hc
    · exact Or.inr (by rw [hc]; simp)
    · exact Or.inl (by rw [hc]; exact ordClosable_2448)) (fun c hc => by
      simp only [List.mem_singleton] at hc
      rw [hc]
      exact h)

end CFSG.GH74.Generic.S45
