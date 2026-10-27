module

public import CFSG.Fischer.Uniq.Cover

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y} {P : Type} {M : LocalModel P}

@[expose] def compSet (E : Set X) (d : X) : Set E :=
  {e | (e : X) = d ∨ (e : X) ∈ LocalClass E d ∨ (e : X) ∈ farSet E d}

@[expose] def compGraph (E : Set X) (d : X) : SimpleGraph (compSet E d) :=
  (commGraph E).induce (compSet E d)

theorem compGraph_adj {d : X} {a b : compSet E d} :
    (compGraph E d).Adj a b ↔ ((a : E) : X) ≠ b ∧ ((a : E) : X) * b = b * a := by
  rw [compGraph, SimpleGraph.induce_adj, commGraph_adj_iff]

theorem Pair.mem_compSet_iff_reachable (hP : Pair X E) {d : X} (hd : d ∈ E) (e : E) :
    e ∈ compSet E d ↔ (commGraph E).Reachable ⟨d, hd⟩ e := by
  rw [Pair.reachable_iff hP]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h.2.1, h.2.2⟩)
  · rintro (h | h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨e.2, h.1, h.2⟩)

theorem compSet_eq_univ {d : X}
    (h : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).Nonempty) : compSet E d = Set.univ := by
  ext e
  simp only [Set.mem_univ, iff_true]
  by_cases h0 : (e : X) = d
  · exact Or.inl h0
  · by_cases h1 : (e : X) * d = d * e
    · exact Or.inr (Or.inl ⟨e.2, h0, h1⟩)
    · exact Or.inr (Or.inr ⟨e.2, h1, h e e.2 h1⟩)

@[expose] noncomputable def compGraphIsoTop {d : X} (h : compSet E d = Set.univ) :
    compGraph E d ≃g commGraph E where
  toEquiv := Equiv.subtypeUnivEquiv fun e => by rw [h]; trivial
  map_rel_iff' := Iff.rfl

theorem compGraphIsoTop_apply {d : X} (h : compSet E d = Set.univ) (e : compSet E d) :
    compGraphIsoTop h e = e := rfl

theorem mem_farSet_of_mem_compSet {d : X} {e : E} (he : e ∈ compSet E d)
    (h1 : (e : X) * d ≠ d * e) : (e : X) ∈ farSet E d := by
  rcases he with h | h | h
  · exact absurd (by rw [h]) h1
  · exact absurd h.2.2 h1
  · exact h

theorem mem_compSet_of_mem_localClass {d : X} {e : E} (he : (e : X) ∈ LocalClass E d) :
    e ∈ compSet E d :=
  Or.inr (Or.inl he)

section Piece

variable {d : X} {d' : Y} (hd : d ∈ E) (hd' : d' ∈ F)
  (L : LocalPoints M E d) (L' : LocalPoints M F d') (βA : farSet E d ≃ farSet F d')

noncomputable def pieceMap (e : compSet E d) : compSet F d' := by
  classical
  exact if h0 : ((e : E) : X) = d then ⟨⟨d', hd'⟩, Or.inl rfl⟩
    else if h1 : ((e : E) : X) * d = d * e then
      ⟨⟨(L'.χ.symm (L.χ ⟨e, (e : E).2, h0, h1⟩) : Y), (L'.χ.symm _).2.1⟩,
        Or.inr (Or.inl (L'.χ.symm _).2)⟩
    else ⟨⟨βA ⟨e, mem_farSet_of_mem_compSet e.2 h1⟩, (βA _).2.1⟩, Or.inr (Or.inr (βA _).2)⟩

theorem pieceMap_d {e : compSet E d} (he : (e : E) = ⟨d, hd⟩) :
    (((pieceMap hd' L L' βA e : compSet F d') : F) : Y) = d' := by
  have h0 : ((e : E) : X) = d := congrArg Subtype.val he
  unfold pieceMap
  simp [h0]

theorem pieceMap_star {e : compSet E d} (he : ((e : E) : X) ∈ LocalClass E d) :
    (((pieceMap hd' L L' βA e : compSet F d') : F) : Y) = L'.χ.symm (L.χ ⟨_, he⟩) := by
  unfold pieceMap
  simp only [he.2.1, dite_false, he.2.2, dite_true]

theorem pieceMap_far {e : compSet E d} (hed : ((e : E) : X) * d ≠ d * e) :
    (((pieceMap hd' L L' βA e : compSet F d') : F) : Y) =
      βA ⟨_, mem_farSet_of_mem_compSet e.2 hed⟩ := by
  have h0 : ((e : E) : X) ≠ d := fun h => hed (by rw [h])
  unfold pieceMap
  simp only [h0, dite_false, hed]

theorem cls (e : compSet E d) :
    ((e : E) : X) = d ∨ ((e : E) : X) ∈ LocalClass E d ∨ ((e : E) : X) * d ≠ d * e := by
  by_cases h0 : ((e : E) : X) = d
  · exact Or.inl h0
  · by_cases h1 : ((e : E) : X) * d = d * e
    · exact Or.inr (Or.inl ⟨(e : E).2, h0, h1⟩)
    · exact Or.inr (Or.inr h1)

include hd in
theorem pieceMap_cases (e : compSet E d) :
    (((e : E) : X) = d ∧ (((pieceMap hd' L L' βA e : compSet F d') : F) : Y) = d') ∨
    (∃ he : ((e : E) : X) ∈ LocalClass E d,
      (((pieceMap hd' L L' βA e : compSet F d') : F) : Y) = L'.χ.symm (L.χ ⟨_, he⟩)) ∨
    (∃ hed : ((e : E) : X) * d ≠ d * e,
      (((pieceMap hd' L L' βA e : compSet F d') : F) : Y) =
        βA ⟨_, mem_farSet_of_mem_compSet e.2 hed⟩) := by
  rcases cls e with h | h | h
  · exact Or.inl ⟨h, pieceMap_d hd hd' L L' βA (Subtype.ext h)⟩
  · exact Or.inr (Or.inl ⟨h, pieceMap_star hd' L L' βA h⟩)
  · exact Or.inr (Or.inr ⟨h, pieceMap_far hd' L L' βA h⟩)

theorem pieceMap_inv (e : compSet E d) :
    pieceMap hd L' L βA.symm (pieceMap hd' L L' βA e) = e := by
  apply Subtype.ext
  apply Subtype.ext
  rcases pieceMap_cases hd hd' L L' βA e with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [pieceMap_d hd' hd L' L βA.symm (Subtype.ext h'), h]
  · have h2 : (((pieceMap hd' L L' βA e : compSet F d') : F) : Y) ∈ LocalClass F d' := by
      rw [h']; exact (L'.χ.symm _).2
    rw [pieceMap_star hd L' L βA.symm h2]
    have : (⟨_, h2⟩ : LocalClass F d') = L'.χ.symm (L.χ ⟨_, h⟩) := Subtype.ext h'
    rw [this]
    simp
  · have h2 : (((pieceMap hd' L L' βA e : compSet F d') : F) : Y) * d' ≠
        d' * ((pieceMap hd' L L' βA e : compSet F d') : F) := by
      rw [h']; exact (βA _).2.2.1
    rw [pieceMap_far hd L' L βA.symm h2]
    have : (⟨_, mem_farSet_of_mem_compSet (pieceMap hd' L L' βA e).2 h2⟩ : farSet F d') =
        βA ⟨_, mem_farSet_of_mem_compSet e.2 h⟩ := Subtype.ext h'
    rw [this]
    simp

@[expose] noncomputable def pieceEquiv : compSet E d ≃ compSet F d' where
  toFun := pieceMap hd' L L' βA
  invFun := pieceMap hd L' L βA.symm
  left_inv := pieceMap_inv hd hd' L L' βA
  right_inv := by
    intro f
    have := pieceMap_inv hd' hd L' L βA.symm f
    simpa using this

variable (hπ : ∀ c, L'.muImg (βA c) = L.muImg c)
  (hadj : ∀ c c', (farGraph E d).Adj c c' ↔ (farGraph F d').Adj (βA c) (βA c'))

include hπ in
theorem star_far_comm {e : X} (he : e ∈ LocalClass E d) (c : farSet E d) :
    e * c = c * e ↔
      (L'.χ.symm (L.χ ⟨e, he⟩) : Y) * βA c = βA c * L'.χ.symm (L.χ ⟨e, he⟩) := by
  have h1 : e * c = c * e ↔ L.χ ⟨e, he⟩ ∈ L.muImg c := by
    rw [L.mem_muImg, Equiv.symm_apply_apply]
    constructor
    · intro h
      exact ⟨he.1, fun hec => c.2.2.1 (by rw [← hec]; exact he.2.2), h⟩
    · intro h; exact h.2.2
  have h2 : (L'.χ.symm (L.χ ⟨e, he⟩) : Y) * βA c = βA c * L'.χ.symm (L.χ ⟨e, he⟩) ↔
      L.χ ⟨e, he⟩ ∈ L'.muImg (βA c) := by
    rw [L'.mem_muImg]
    constructor
    · intro h
      refine ⟨(L'.χ.symm _).2.1, fun hec => (βA c).2.2.1 ?_, h⟩
      rw [← hec]; exact (L'.χ.symm _).2.2.2
    · intro h; exact h.2.2
  rw [h1, h2, hπ]

theorem rel_symm {G : Type} [Group G] (a b : G) :
    (a ≠ b ∧ a * b = b * a) ↔ (b ≠ a ∧ b * a = a * b) :=
  ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

include hπ in
theorem rel_star_far {e : X} (he : e ∈ LocalClass E d) (c : farSet E d) :
    (e ≠ c ∧ e * c = c * e) ↔
      ((L'.χ.symm (L.χ ⟨e, he⟩) : Y) ≠ βA c ∧
        (L'.χ.symm (L.χ ⟨e, he⟩) : Y) * βA c = βA c * L'.χ.symm (L.χ ⟨e, he⟩)) := by
  have hne1 : e ≠ c := fun h => c.2.2.1 (by rw [← h]; exact he.2.2)
  have hne2 : (L'.χ.symm (L.χ ⟨e, he⟩) : Y) ≠ βA c := fun h =>
    (βA c).2.2.1 (by rw [← h]; exact (L'.χ.symm _).2.2.2)
  rw [and_iff_right hne1, and_iff_right hne2]
  exact star_far_comm L L' βA hπ he c

theorem rel_star_star {e₁ e₂ : X} (h₁ : e₁ ∈ LocalClass E d) (h₂ : e₂ ∈ LocalClass E d) :
    (e₁ ≠ e₂ ∧ e₁ * e₂ = e₂ * e₁) ↔
      ((L'.χ.symm (L.χ ⟨e₁, h₁⟩) : Y) ≠ L'.χ.symm (L.χ ⟨e₂, h₂⟩) ∧
        (L'.χ.symm (L.χ ⟨e₁, h₁⟩) : Y) * L'.χ.symm (L.χ ⟨e₂, h₂⟩) =
          L'.χ.symm (L.χ ⟨e₂, h₂⟩) * L'.χ.symm (L.χ ⟨e₁, h₁⟩)) := by
  have hχ1 := L.comm ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  have hχ2 := L'.comm (L'.χ.symm (L.χ ⟨e₁, h₁⟩)) (L'.χ.symm (L.χ ⟨e₂, h₂⟩))
  simp only [Equiv.apply_symm_apply] at hχ2
  have hne : e₁ ≠ e₂ ↔ ((L'.χ.symm (L.χ ⟨e₁, h₁⟩) : Y) ≠ L'.χ.symm (L.χ ⟨e₂, h₂⟩)) := by
    constructor
    · intro h h'
      apply h
      have := (L'.χ.symm.injective.comp L.χ.injective) (Subtype.ext h')
      exact congrArg Subtype.val this
    · intro h h'
      apply h
      have : (⟨e₁, h₁⟩ : LocalClass E d) = ⟨e₂, h₂⟩ := Subtype.ext h'
      rw [this]
  rw [hne, hχ1, ← hχ2]

include hd hπ hadj in
theorem pieceMap_adj (e₁ e₂ : compSet E d) :
    (compGraph E d).Adj e₁ e₂ ↔
      (compGraph F d').Adj (pieceMap hd' L L' βA e₁) (pieceMap hd' L L' βA e₂) := by
  rw [compGraph_adj, compGraph_adj]
  rcases pieceMap_cases hd hd' L L' βA e₁ with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
    rcases pieceMap_cases hd hd' L L' βA e₂ with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
    rw [b1, b2]
  · rw [a1, a2]; simp
  · rw [a1]
    exact iff_of_true ⟨a2.2.1.symm, a2.2.2.symm⟩
      ⟨(L'.χ.symm _).2.2.1.symm, (L'.χ.symm _).2.2.2.symm⟩
  · rw [a1]
    exact iff_of_false (fun h => a2 h.2.symm) (fun h => (βA _).2.2.1 h.2.symm)
  · rw [a2]
    exact iff_of_true ⟨a1.2.1, a1.2.2⟩ ⟨(L'.χ.symm _).2.2.1, (L'.χ.symm _).2.2.2⟩
  · exact rel_star_star L L' a1 a2
  · exact rel_star_far L L' βA hπ a1 ⟨_, mem_farSet_of_mem_compSet e₂.2 a2⟩
  · rw [a2]
    exact iff_of_false (fun h => a1 h.2) (fun h => (βA _).2.2.1 h.2)
  · rw [rel_symm, rel_symm (βA _ : Y)]
    exact rel_star_far L L' βA hπ a2 ⟨_, mem_farSet_of_mem_compSet e₁.2 a1⟩
  · exact hadj ⟨_, mem_farSet_of_mem_compSet e₁.2 a1⟩ ⟨_, mem_farSet_of_mem_compSet e₂.2 a2⟩

include hπ hadj in
@[expose] noncomputable def compGraphIso : compGraph E d ≃g compGraph F d' where
  toEquiv := pieceEquiv hd hd' L L' βA
  map_rel_iff' {e₁ e₂} := (pieceMap_adj hd hd' L L' βA hπ hadj e₁ e₂).symm

theorem compGraphIso_apply (e : compSet E d) :
    compGraphIso hd hd' L L' βA hπ hadj e = pieceMap hd' L L' βA e := rfl

end Piece

end CFSG.Fischer
