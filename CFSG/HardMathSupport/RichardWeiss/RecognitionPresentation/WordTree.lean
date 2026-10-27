module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.PairAlt
public import CFSG.Certificates.CosetTablePresented
public import Mathlib.GroupTheory.FreeGroup.Reduce

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

open CFSG.CosetTable

structure CDesc (k : ℕ) where
  letter : Fin k × Bool
  conj : FreeGroup (Fin k)
  deriving DecidableEq

variable {k : ℕ}

@[expose] def CDesc.elt (c : CDesc k) : FreeGroup (Fin k) :=
  c.conj⁻¹ * FreeGroup.mk [c.letter] * c.conj

@[expose] def evalW {J : Type*} [Group J] (x : Fin k → J) (w : FreeGroup (Fin k)) : J :=
  FreeGroup.lift x w

theorem evalW_mul {J : Type*} [Group J] (x : Fin k → J) (a b : FreeGroup (Fin k)) :
    evalW x (a * b) = evalW x a * evalW x b := map_mul _ _ _

theorem evalW_inv {J : Type*} [Group J] (x : Fin k → J) (a : FreeGroup (Fin k)) :
    evalW x a⁻¹ = (evalW x a)⁻¹ := map_inv _ _

theorem evalW_pow {J : Type*} [Group J] (x : Fin k → J) (a : FreeGroup (Fin k)) (n : ℕ) :
    evalW x (a ^ n) = (evalW x a) ^ n := map_pow _ _ _

theorem evalW_of {J : Type*} [Group J] (x : Fin k → J) (i : Fin k) :
    evalW x (FreeGroup.of i) = x i := by simp [evalW]

theorem evalW_one {J : Type*} [Group J] (x : Fin k → J) : evalW x 1 = 1 := map_one _

theorem evalW_cdesc_elt {J : Type*} [Group J] (x : Fin k → J) (c : CDesc k) :
    evalW x c.elt =
      (evalW x c.conj)⁻¹ * evalW x (FreeGroup.mk [c.letter]) * evalW x c.conj := by
  simp only [CDesc.elt, evalW_mul, evalW_inv]

theorem evalW_letter {J : Type*} [Group J] (x : Fin k → J) (l : Fin k × Bool) :
    evalW x (FreeGroup.mk [l]) = if l.2 then x l.1 else (x l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  cases b <;> simp [evalW]

@[expose] def alt (p q : FreeGroup (Fin k)) : Fin 6 → List (FreeGroup (Fin k))
  | 0 => [p * q]
  | 1 => [p * q⁻¹]
  | 2 => [p * q * p⁻¹ * q⁻¹]
  | 3 => [(p * q) ^ 2]
  | 4 => [(p * q⁻¹) ^ 2]
  | 5 => [(p * q) ^ 5, (p * q * p * q⁻¹) ^ 2, (p * q⁻¹) ^ 5, (p * q⁻¹ * p * q) ^ 2]

inductive Tree (k : ℕ) where
  | collapse : ℕ → Tree k
  | success : CDesc k → Tree k
  | branch : CDesc k → CDesc k → Tree k → Tree k → Tree k → Tree k → Tree k → Tree k → Tree k

@[expose] def Tree.succs : Tree k → List (CDesc k)
  | .collapse _ => []
  | .success t => [t]
  | .branch _ _ t0 t1 t2 t3 t4 t5 =>
      t0.succs ++ t1.succs ++ t2.succs ++ t3.succs ++ t4.succs ++ t5.succs

@[expose] def Tree.ok (S : List (Fin k)) (d : Fin k) :
    Tree k → List (FreeGroup (Fin k)) → Bool
  | .collapse cap, rels =>
      check (presParams (rels.map FreeGroup.toWord) (S.map fun x => [(x, true)])) cap 1
  | .success t, rels => decide ((t.elt * FreeGroup.of d) ^ 2 ∈ rels)
  | .branch c1 c2 t0 t1 t2 t3 t4 t5, rels =>
      t0.ok S d (alt c1.elt c2.elt 0 ++ rels) && t1.ok S d (alt c1.elt c2.elt 1 ++ rels) &&
      t2.ok S d (alt c1.elt c2.elt 2 ++ rels) && t3.ok S d (alt c1.elt c2.elt 3 ++ rels) &&
      t4.ok S d (alt c1.elt c2.elt 4 ++ rels) && t5.ok S d (alt c1.elt c2.elt 5 ++ rels)

theorem mem_closure_of_check {J : Type*} [Group J] (x : Fin k → J)
    (ws : List (FreeGroup (Fin k))) (hx : ∀ r ∈ ws, evalW x r = 1)
    (S : List (Fin k)) (d : Fin k) {cap : ℕ}
    (h : check (presParams (ws.map FreeGroup.toWord) (S.map fun s => [(s, true)])) cap 1 = true) :
    x d ∈ Subgroup.closure (x '' {s | s ∈ S}) := by
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
  obtain ⟨hfi, hidx⟩ := index_le_presented wsW (S.map fun s => [(s, true)]) (genSub rels S)
    (by
      intro w hw
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hw
      exact Subgroup.subset_closure ⟨s, hs, rfl⟩) h
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

theorem exists_alt_eval {J : Type*} [Group J] (x : Fin k → J) (c1 c2 : CDesc k)
    (hpa : PairAlt (evalW x c1.elt) (evalW x c2.elt)) :
    ∃ i : Fin 6, ∀ r ∈ alt c1.elt c2.elt i, evalW x r = 1 := by
  set p := c1.elt
  set q := c2.elt
  rcases hpa with h | h | h | h | h | ⟨h1, h2, h3, h4⟩
  · refine ⟨0, ?_⟩
    intro r hr
    simp only [alt, List.mem_singleton] at hr
    subst hr
    rw [evalW_mul]; exact h
  · refine ⟨1, ?_⟩
    intro r hr
    simp only [alt, List.mem_singleton] at hr
    subst hr
    rw [evalW_mul, evalW_inv]; exact h
  · refine ⟨2, ?_⟩
    intro r hr
    simp only [alt, List.mem_singleton] at hr
    subst hr
    simp only [evalW_mul, evalW_inv]
    rw [h]
    group
  · refine ⟨3, ?_⟩
    intro r hr
    simp only [alt, List.mem_singleton] at hr
    subst hr
    rw [evalW_pow, evalW_mul]; exact h
  · refine ⟨4, ?_⟩
    intro r hr
    simp only [alt, List.mem_singleton] at hr
    subst hr
    rw [evalW_pow, evalW_mul, evalW_inv]; exact h
  · refine ⟨5, ?_⟩
    intro r hr
    simp only [alt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [evalW_pow, evalW_mul]; exact h1
    · simp only [evalW_pow, evalW_mul, evalW_inv]; exact h2
    · rw [evalW_pow, evalW_mul, evalW_inv]; exact h3
    · simp only [evalW_pow, evalW_mul, evalW_inv]; exact h4

theorem Tree.sound {J : Type*} [Group J] (x : Fin k → J)
    (hconj : ∀ c1 c2 : CDesc k, PairAlt (evalW x c1.elt) (evalW x c2.elt))
    (S : List (Fin k)) (d : Fin k) :
    ∀ (T : Tree k) (rels : List (FreeGroup (Fin k))), (∀ r ∈ rels, evalW x r = 1) →
      T.ok S d rels = true →
      x d ∈ Subgroup.closure (x '' {s | s ∈ S}) ∨
        ∃ t ∈ T.succs, (evalW x t.elt * x d) ^ 2 = 1 := by
  intro T
  induction T with
  | collapse cap =>
    intro rels hrels hok
    exact Or.inl (mem_closure_of_check x rels hrels S d hok)
  | success t =>
    intro rels hrels hok
    right
    refine ⟨t, by simp [Tree.succs], ?_⟩
    have hmem : (t.elt * FreeGroup.of d) ^ 2 ∈ rels := of_decide_eq_true hok
    have := hrels _ hmem
    rwa [evalW_pow, evalW_mul, evalW_of] at this
  | branch c1 c2 t0 t1 t2 t3 t4 t5 ih0 ih1 ih2 ih3 ih4 ih5 =>
    intro rels hrels hok
    simp only [Tree.ok, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hok
    obtain ⟨i, hi⟩ := exists_alt_eval x c1 c2 (hconj c1 c2)
    have hnew : ∀ r ∈ alt c1.elt c2.elt i ++ rels, evalW x r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hi r hr
      · exact hrels r hr
    have hs0 : ∀ t ∈ t0.succs, t ∈ (Tree.branch c1 c2 t0 t1 t2 t3 t4 t5).succs := by
      intro t ht; simp [Tree.succs, ht]
    have hs1 : ∀ t ∈ t1.succs, t ∈ (Tree.branch c1 c2 t0 t1 t2 t3 t4 t5).succs := by
      intro t ht; simp [Tree.succs, ht]
    have hs2 : ∀ t ∈ t2.succs, t ∈ (Tree.branch c1 c2 t0 t1 t2 t3 t4 t5).succs := by
      intro t ht; simp [Tree.succs, ht]
    have hs3 : ∀ t ∈ t3.succs, t ∈ (Tree.branch c1 c2 t0 t1 t2 t3 t4 t5).succs := by
      intro t ht; simp [Tree.succs, ht]
    have hs4 : ∀ t ∈ t4.succs, t ∈ (Tree.branch c1 c2 t0 t1 t2 t3 t4 t5).succs := by
      intro t ht; simp [Tree.succs, ht]
    have hs5 : ∀ t ∈ t5.succs, t ∈ (Tree.branch c1 c2 t0 t1 t2 t3 t4 t5).succs := by
      intro t ht; simp [Tree.succs, ht]
    fin_cases i
    · rcases ih0 _ hnew h0 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs0 t ht, h⟩
    · rcases ih1 _ hnew h1 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs1 t ht, h⟩
    · rcases ih2 _ hnew h2 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs2 t ht, h⟩
    · rcases ih3 _ hnew h3 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs3 t ht, h⟩
    · rcases ih4 _ hnew h4 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs4 t ht, h⟩
    · rcases ih5 _ hnew h5 with h | ⟨t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hs5 t ht, h⟩

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
