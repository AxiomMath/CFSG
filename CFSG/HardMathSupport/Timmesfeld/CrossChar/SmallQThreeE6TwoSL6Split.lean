module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoSL6

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

theorem dCert_of_pl {Zs W : List (List ℕ)} {L35 L02 L41 : List (ℕ × ℕ)}
    (h35 : pl Zs 3 5 = L35) (h02 : pl Zs 0 2 = L02) (h41 : pl Zs 4 1 = L41)
    (h : (L35.all fun x35 => L02.all fun x02 => L41.all fun x41 =>
      certM Zs W (asm3 x35 x02 x41)) = true) : dCert Zs W = true := by
  rw [dCert, h35, h02, h41]
  exact h

theorem all_append_of {α : Type*} {f : α → Bool} {l₁ l₂ : List α} (h₁ : l₁.all f = true)
    (h₂ : l₂.all f = true) : (l₁ ++ l₂).all f = true := by
  rw [List.all_append, h₁, h₂, Bool.and_self]

theorem all_single_append_of {α β : Type*} {a : α} {g : α → β → Bool} {A B : List β}
    (h₁ : ([a].all fun x => A.all (g x)) = true) (h₂ : ([a].all fun x => B.all (g x)) = true) :
    ([a].all fun x => (A ++ B).all (g x)) = true := by
  simp only [List.all_cons, List.all_nil, Bool.and_true, List.all_append] at h₁ h₂ ⊢
  rw [h₁, h₂, Bool.and_self]

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
