module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessA

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

@[expose] def wordEval {M : Type*} [Monoid M] (w : List (Fin 3)) (h : Fin 3 → M) : M :=
  w.foldl (fun acc l => acc * h l) 1

theorem foldl_map_hom {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (h : Fin 3 → M)
    (w : List (Fin 3)) : ∀ y : M,
      f (w.foldl (fun acc l => acc * h l) y) = w.foldl (fun acc l => acc * f (h l)) (f y) := by
  induction w with
  | nil => intro y; rfl
  | cons l w ih => intro y; simp only [List.foldl_cons]; rw [ih, map_mul]

theorem map_wordEval {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (h : Fin 3 → M)
    (w : List (Fin 3)) : f (wordEval w h) = wordEval w (fun l => f (h l)) := by
  unfold wordEval
  rw [foldl_map_hom, map_one]

theorem eq_of_words {M N : Type*} [Monoid M] [Monoid N] (f g : M →* N) (h : Fin 3 → M)
    (hw : ∀ x : M, ∃ w : List (Fin 3), x = wordEval w h) (hf : ∀ l, f (h l) = g (h l)) : f = g := by
  ext x
  obtain ⟨w, rfl⟩ := hw x
  rw [map_wordEval, map_wordEval]
  congr 1
  funext l
  exact hf l

section Restriction

variable {G : Type*} [Group G]

@[expose] def restrictHom {A S : Subgroup G} (hSA : S ≤ A) (θ : MulAut ↥A)
    (hθ : ∀ m : ↥A, (m : G) ∈ S ↔ ((θ m : ↥A) : G) ∈ S) : ↥S →* ↥S where
  toFun x := ⟨((θ ⟨(x : G), hSA x.2⟩ : ↥A) : G), (hθ ⟨(x : G), hSA x.2⟩).mp x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have h : (⟨((x : G) * (y : G)), hSA (S.mul_mem x.2 y.2)⟩ : ↥A) =
        ⟨(x : G), hSA x.2⟩ * ⟨(y : G), hSA y.2⟩ := rfl
    rw [h, map_mul]
    rfl

theorem restrictHom_eq_of {A S : Subgroup G} (hSA : S ≤ A) (θ : MulAut ↥A)
    (hθ : ∀ m : ↥A, (m : G) ∈ S ↔ ((θ m : ↥A) : G) ∈ S) (f : ↥S → ↥S)
    (hf : ∀ (b : ↥S) (m : ↥A), (m : G) = (b : G) → ((θ m : ↥A) : G) = ((f b : ↥S) : G))
    (x : ↥S) : restrictHom hSA θ hθ x = f x := by
  apply Subtype.ext
  exact hf x ⟨(x : G), hSA x.2⟩ rfl

theorem restrictHom_coe_of {A S : Subgroup G} (hSA : S ≤ A) (θ : MulAut ↥A)
    (hθ : ∀ m : ↥A, (m : G) ∈ S ↔ ((θ m : ↥A) : G) ∈ S) (x : ↥S) (m : ↥A)
    (h : (m : G) = (x : G)) :
    ((restrictHom hSA θ hθ x : ↥S) : G) = ((θ m : ↥A) : G) := by
  have hm : (⟨(x : G), hSA x.2⟩ : ↥A) = m := Subtype.ext h.symm
  show ((θ ⟨(x : G), hSA x.2⟩ : ↥A) : G) = _
  rw [hm]

end Restriction

end CFSG.GH74.QTGen4.DSGen4.L34
