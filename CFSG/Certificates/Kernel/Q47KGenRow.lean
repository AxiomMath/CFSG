module

public section

namespace CFSG.KC.Q47K

@[expose] def RowQ {α : Type} (N : Nat) (T : Nat → Nat) (mulP : Nat → Nat → Nat) (M : Nat → α)
    (mulM : α → α → α) (R : α → α → Prop) (y : Nat) : Prop :=
  ∃ i < N, T i = y ∧ ∀ j < N, ∃ f < N, T f = mulP y (T j) ∧ R (M f) (mulM (M i) (M j))

theorem rowQ_zero {α : Type} {N : Nat} {T : Nat → Nat} {mulP : Nat → Nat → Nat} {M : Nat → α}
    {mulM : α → α → α} {R : α → α → Prop} (hN : 0 < N)
    (hid : ∀ j < N, mulP (T 0) (T j) = T j ∧ R (M j) (mulM (M 0) (M j))) :
    RowQ N T mulP M mulM R (T 0) :=
  ⟨0, hN, rfl, fun j hj => ⟨j, hj, (hid j hj).1.symm, (hid j hj).2⟩⟩

theorem rowQ_step {α : Type} {N ng : Nat} {T G : Nat → Nat} {e : Nat → Nat → Nat}
    {mulP : Nat → Nat → Nat} {M : Nat → α} {mulM : α → α → α} {R : α → α → Prop} {V : α → Prop}
    (hV : ∀ i < N, V (M i)) (hVm : ∀ a b, V a → V b → V (mulM a b))
    (hsymm : ∀ a b, V a → V b → R a b → R b a)
    (htrans : ∀ a b c, V a → V b → V c → R a b → R b c → R a c)
    (hleft : ∀ a b c, V a → V b → V c → R a b → R (mulM c a) (mulM c b))
    (hright : ∀ a b c, V a → V b → V c → R a b → R (mulM a c) (mulM b c))
    (hassocM : ∀ a b c, mulM (mulM a b) c = mulM a (mulM b c))
    (hassocP : ∀ k < ng, ∀ i < N, ∀ j < N, mulP (mulP (G k) (T i)) (T j) =
      mulP (G k) (mulP (T i) (T j)))
    (hrow : ∀ k < ng, ∀ j < N, e j k < N ∧ T (e j k) = mulP (G k) (T j) ∧
      R (M (e j k)) (mulM (M (e 0 k)) (M j))) (hN : 0 < N) :
    ∀ y, RowQ N T mulP M mulM R y → ∀ k < ng, RowQ N T mulP M mulM R (mulP (G k) y) := by
  rintro y ⟨i, hi, rfl, hy⟩ k hk
  obtain ⟨hi1, hiT, hiR⟩ := hrow k hk i hi
  refine ⟨e i k, hi1, hiT, fun j hj => ?_⟩
  obtain ⟨f1, hf1, hT1, hR1⟩ := hy j hj
  obtain ⟨hf2, hfT, hfR⟩ := hrow k hk f1 hf1
  refine ⟨e f1 k, hf2, by rw [hfT, hT1, hassocP k hk i hi j hj], ?_⟩
  have Vg := hV _ (hrow k hk 0 hN).1
  have Vi := hV i hi
  have Vj := hV j hj
  have Vf1 := hV f1 hf1
  have Vi' := hV _ hi1
  have Vgi := hVm _ _ Vg Vi
  have h2 : R (mulM (M (e 0 k)) (M f1)) (mulM (mulM (M (e 0 k)) (M i)) (M j)) := by
    rw [hassocM]
    exact hleft _ _ _ Vf1 (hVm _ _ Vi Vj) Vg hR1
  have h3 : R (mulM (mulM (M (e 0 k)) (M i)) (M j)) (mulM (M (e i k)) (M j)) :=
    hright _ _ _ Vgi Vi' Vj (hsymm _ _ Vi' Vgi hiR)
  exact htrans _ _ _ (hV _ hf2) (hVm _ _ Vg Vf1) (hVm _ _ Vi' Vj) hfR
    (htrans _ _ _ (hVm _ _ Vg Vf1) (hVm _ _ Vgi Vj) (hVm _ _ Vi' Vj) h2 h3)

end CFSG.KC.Q47K

end
