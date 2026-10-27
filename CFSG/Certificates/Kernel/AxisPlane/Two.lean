module

public import CFSG.Certificates.Kernel.AxisPlane.Glue

public section

namespace CFSG.KC.AxisPlane

theorem planesOK_two {A B : Array Nat} {opss : List (List Nat)} {rA rB Ls Qs : List Nat}
    {Rss : List (List Nat)} {lams sizes : List Nat}
    (C : PlanesChk opss [rA, rB] Ls Qs Rss lams sizes) (hm : opss.length = 2)
    (hA : A = rA.toArray) (hB : B = rB.toArray) :
    PlanesOK #[A, B] opss [rA, rB] Ls Qs Rss lams sizes := by
  subst hA hB
  refine ⟨C, hm.symm, fun g hg => ?_⟩
  have : g = 0 ∨ g = 1 := by simp at hg; omega
  rcases this with rfl | rfl <;> rfl

theorem orbits_two {A B : Array Nat} {opss : List (List Nat)} {rA rB Ls Qs : List Nat}
    {Rss : List (List Nat)} {lams sizes : List Nat} {n : Nat} {lam size : Nat → Nat}
    (C : PlanesChk opss [rA, rB] Ls Qs Rss lams sizes) (hm : opss.length = 2)
    (hA : A = rA.toArray) (hB : B = rB.toArray)
    (hl : (List.range n).map lam = lams) (hs : (List.range n).map size = sizes) :
    ∀ r < n, natOrbit #[A, B] (lam r) ⊆ Set.Iio (2 ^ 24) ∧
      (natOrbit #[A, B] (lam r)).ncard = size r ∧
      ∀ r' < n, r ≠ r' → Disjoint (natOrbit #[A, B] (lam r)) (natOrbit #[A, B] (lam r')) := by
  have H := planesOK_two C hm hA hB
  have hn : lams.length = n := by rw [← hl, List.length_map, List.length_range]
  have hlam : ∀ r < n, lams.getD r 0 = lam r := fun r hr => by
    rw [← hl]
    simp [List.getD_eq_getElem?_getD, hr]
  have hsz : ∀ r < n, sizes.getD r 0 = size r := fun r hr => by
    rw [← hs]
    simp [List.getD_eq_getElem?_getD, hr]
  intro r hr
  obtain ⟨h1, h2, h3⟩ := orbits_of_planesOK H (r := r) (by omega)
  rw [hlam r hr] at h1 h2 h3
  refine ⟨h1, h2.trans (hsz r hr), fun r' hr' hne => ?_⟩
  have := h3 r' (by omega) hne
  rwa [hlam r' hr'] at this

end CFSG.KC.AxisPlane

end
