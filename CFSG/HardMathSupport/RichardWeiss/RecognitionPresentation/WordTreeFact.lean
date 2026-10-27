module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.WordTree

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

open CFSG.CosetTable

variable {k : ℕ}

@[expose] def CollapseFact (S : List (Fin k)) (rels : List (FreeGroup (Fin k))) : Prop :=
  (genSub {r : FreeGroup (Fin k) | r ∈ (rels.map FreeGroup.toWord).map FreeGroup.mk} S).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin k) | r ∈ (rels.map FreeGroup.toWord).map FreeGroup.mk} S).index ≤ 1

@[expose] def Tree.okF (S : List (Fin k)) (d : Fin k) : Tree k → List (FreeGroup (Fin k)) → Prop
  | .collapse _, rels => CollapseFact S rels
  | .success t, rels => (t.elt * FreeGroup.of d) ^ 2 ∈ rels
  | .branch c1 c2 t0 t1 t2 t3 t4 t5, rels =>
      t0.okF S d (alt c1.elt c2.elt 0 ++ rels) ∧ t1.okF S d (alt c1.elt c2.elt 1 ++ rels) ∧
      t2.okF S d (alt c1.elt c2.elt 2 ++ rels) ∧ t3.okF S d (alt c1.elt c2.elt 3 ++ rels) ∧
      t4.okF S d (alt c1.elt c2.elt 4 ++ rels) ∧ t5.okF S d (alt c1.elt c2.elt 5 ++ rels)

@[expose] def Tree.collapses : Tree k → List (FreeGroup (Fin k)) → List (List (FreeGroup (Fin k)))
  | .collapse _, rels => [rels]
  | .success _, _ => []
  | .branch c1 c2 t0 t1 t2 t3 t4 t5, rels =>
      t0.collapses (alt c1.elt c2.elt 0 ++ rels) ++ t1.collapses (alt c1.elt c2.elt 1 ++ rels) ++
      t2.collapses (alt c1.elt c2.elt 2 ++ rels) ++ t3.collapses (alt c1.elt c2.elt 3 ++ rels) ++
      t4.collapses (alt c1.elt c2.elt 4 ++ rels) ++ t5.collapses (alt c1.elt c2.elt 5 ++ rels)

@[expose] def Tree.succOk (d : Fin k) : Tree k → List (FreeGroup (Fin k)) → Bool
  | .collapse _, _ => true
  | .success t, rels => decide ((t.elt * FreeGroup.of d) ^ 2 ∈ rels)
  | .branch c1 c2 t0 t1 t2 t3 t4 t5, rels =>
      t0.succOk d (alt c1.elt c2.elt 0 ++ rels) && t1.succOk d (alt c1.elt c2.elt 1 ++ rels) &&
      t2.succOk d (alt c1.elt c2.elt 2 ++ rels) && t3.succOk d (alt c1.elt c2.elt 3 ++ rels) &&
      t4.succOk d (alt c1.elt c2.elt 4 ++ rels) && t5.succOk d (alt c1.elt c2.elt 5 ++ rels)

theorem Tree.okF_of (S : List (Fin k)) (d : Fin k) :
    ∀ (T : Tree k) (rels : List (FreeGroup (Fin k))), T.succOk d rels = true →
      (∀ rs ∈ T.collapses rels, CollapseFact S rs) → T.okF S d rels := by
  intro T
  induction T with
  | collapse cap =>
    intro rels _ h
    exact h rels (by simp [Tree.collapses])
  | success t =>
    intro rels hs _
    simp only [Tree.succOk, decide_eq_true_eq] at hs
    exact hs
  | branch c1 c2 t0 t1 t2 t3 t4 t5 ih0 ih1 ih2 ih3 ih4 ih5 =>
    intro rels hs h
    simp only [Tree.succOk, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨⟨⟨s0, s1⟩, s2⟩, s3⟩, s4⟩, s5⟩ := hs
    simp only [Tree.collapses, List.mem_append] at h
    exact ⟨ih0 _ s0 fun rs hr => h rs (by tauto), ih1 _ s1 fun rs hr => h rs (by tauto),
      ih2 _ s2 fun rs hr => h rs (by tauto), ih3 _ s3 fun rs hr => h rs (by tauto),
      ih4 _ s4 fun rs hr => h rs (by tauto), ih5 _ s5 fun rs hr => h rs (by tauto)⟩

theorem mem_closure_of_collapseFact {J : Type*} [Group J] (x : Fin k → J)
    (ws : List (FreeGroup (Fin k))) (hx : ∀ r ∈ ws, evalW x r = 1)
    (S : List (Fin k)) (d : Fin k) (h : CollapseFact S ws) :
    x d ∈ Subgroup.closure (x '' {s | s ∈ S}) := by
  obtain ⟨hfi, hidx⟩ := h
  set wsW := ws.map FreeGroup.toWord with hwsW
  set rels : Set (FreeGroup (Fin k)) := {r | r ∈ wsW.map FreeGroup.mk} with hrels
  have hrel : ∀ r ∈ rels, FreeGroup.lift x r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hw
    rw [FreeGroup.mk_toWord]
    exact hx r0 hr0
  let f := PresentedGroup.toGroup hrel
  have hf : ∀ i, f (PresentedGroup.of i) = x i := fun i => PresentedGroup.toGroup.of hrel
  have hidx1 : (genSub rels S).index = 1 := by
    have h0 : (genSub rels S).index ≠ 0 := hfi.index_ne_zero
    omega
  have htop : genSub rels S = ⊤ := Subgroup.index_eq_one.1 hidx1
  have hmem : (PresentedGroup.of d : PresentedGroup rels) ∈ genSub rels S := by
    rw [htop]; trivial
  have := Subgroup.mem_map_of_mem f hmem
  rw [genSub, MonoidHom.map_closure] at this
  rw [hf d] at this
  have himg : f '' ((fun x => (PresentedGroup.of x : PresentedGroup rels)) '' {x | x ∈ S}) =
      x '' {s | s ∈ S} := by
    rw [Set.image_image]
    exact Set.image_congr fun i _ => hf i
  rwa [himg] at this

theorem Tree.soundF {J : Type*} [Group J] (x : Fin k → J)
    (hconj : ∀ c1 c2 : CDesc k, PairAlt (evalW x c1.elt) (evalW x c2.elt))
    (S : List (Fin k)) (d : Fin k) :
    ∀ (T : Tree k) (rels : List (FreeGroup (Fin k))), (∀ r ∈ rels, evalW x r = 1) →
      T.okF S d rels →
      x d ∈ Subgroup.closure (x '' {s | s ∈ S}) ∨
        ∃ t ∈ T.succs, (evalW x t.elt * x d) ^ 2 = 1 := by
  intro T
  induction T with
  | collapse cap =>
    intro rels hrels hok
    exact Or.inl (mem_closure_of_collapseFact x rels hrels S d hok)
  | success t =>
    intro rels hrels hok
    right
    refine ⟨t, by simp [Tree.succs], ?_⟩
    have := hrels _ hok
    rwa [evalW_pow, evalW_mul, evalW_of] at this
  | branch c1 c2 t0 t1 t2 t3 t4 t5 ih0 ih1 ih2 ih3 ih4 ih5 =>
    intro rels hrels hok
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hok
    obtain ⟨i, hi⟩ := exists_alt_eval x c1 c2 (hconj c1 c2)
    have hnew : ∀ r ∈ alt c1.elt c2.elt i ++ rels, evalW x r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hi r hr
      · exact hrels r hr
    have hs : ∀ (u : Tree k) (t : CDesc k), t ∈ u.succs →
        u = t0 ∨ u = t1 ∨ u = t2 ∨ u = t3 ∨ u = t4 ∨ u = t5 →
        t ∈ (Tree.branch c1 c2 t0 t1 t2 t3 t4 t5).succs := by
      intro u t ht hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Tree.succs, ht]
    fin_cases i
    · rcases ih0 _ hnew h0 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs t0 t ht (by simp), h⟩
    · rcases ih1 _ hnew h1 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs t1 t ht (by simp), h⟩
    · rcases ih2 _ hnew h2 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs t2 t ht (by simp), h⟩
    · rcases ih3 _ hnew h3 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs t3 t ht (by simp), h⟩
    · rcases ih4 _ hnew h4 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs t4 t ht (by simp), h⟩
    · rcases ih5 _ hnew h5 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs t5 t ht (by simp), h⟩

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation
