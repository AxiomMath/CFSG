module

public import CFSG.ClassicalInvolution.SmallCases.SmallWeylRootFamily

public section

namespace CFSG.ClassicalInvolution.SmallWeyl

@[expose] def elemC (i j : ℕ) (a : ℕ × ℕ) : ℕ × ℕ :=
  (a.1 ^^^ (((a.1 >>> j) % 2) <<< i), a.2 ^^^ (((a.2 >>> i) % 2) <<< j))

structure IsAutC (g : ℕ × ℕ → ℕ × ℕ) : Prop where
  valid : ∀ a ∈ allC 4, validC 4 (g a) = true
  invol : ∀ a ∈ allC 4, g (g a) = a
  pair : ∀ a ∈ allC 4, ∀ b ∈ allC 4, pairC (g a).2 (g b).1 = pairC a.2 b.1
  add : ∀ a ∈ allC 4, ∀ b ∈ allC 4, adjC a b = true → g (addC a b) = addC (g a) (g b)

@[expose] def elemV (i j v : ℕ) : ℕ := v ^^^ (((v >>> j) % 2) <<< i)

structure ElemOK (i j : ℕ) : Prop where
  lt : ∀ v < 16, elemV i j v < 16 ∧ elemV j i v < 16
  invol : ∀ v < 16, elemV i j (elemV i j v) = v ∧ elemV j i (elemV j i v) = v
  pair : ∀ f < 16, ∀ v < 16, pairC (elemV j i f) (elemV i j v) = pairC f v
  add : ∀ x < 16, ∀ y < 16, elemV i j (x ^^^ y) = elemV i j x ^^^ elemV i j y ∧
    elemV j i (x ^^^ y) = elemV j i x ^^^ elemV j i y
  zero : elemV i j 0 = 0 ∧ elemV j i 0 = 0

theorem validC_four_iff {a : ℕ × ℕ} :
    validC 4 a = true ↔ (0 < a.1 ∧ a.1 < 16 ∧ 0 < a.2 ∧ a.2 < 16) ∧ pairC a.2 a.1 = false := by
  simp [validC]

theorem isAutC_of_elemOK {i j : ℕ} (h : ElemOK i j) : IsAutC (elemC i j) := by
  have hv : ∀ a ∈ allC 4, 0 < a.1 ∧ a.1 < 16 ∧ 0 < a.2 ∧ a.2 < 16 ∧ pairC a.2 a.1 = false := by
    intro a ha
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := validC_four_iff.mp (mem_allC.mp ha)
    exact ⟨h1, h2, h3, h4, h5⟩
  have hne : ∀ v, 0 < v → v < 16 → 0 < elemV i j v ∧ 0 < elemV j i v := by
    intro v hv0 hv16
    refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, Nat.pos_of_ne_zero fun h0 => ?_⟩
    · have := (h.invol v hv16).1
      rw [h0, h.zero.1] at this
      omega
    · have := (h.invol v hv16).2
      rw [h0, h.zero.2] at this
      omega
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha b hb => ?_, fun a ha b hb _ => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hv a ha
    have e1 := h.lt a.1 h2
    have e2 := h.lt a.2 h4
    have e3 := hne a.1 h1 h2
    have e4 := hne a.2 h3 h4
    have e5 := h.pair a.2 h4 a.1 h2
    rw [validC_four_iff]
    refine ⟨⟨e3.1, e1.1, e4.2, e2.2⟩, ?_⟩
    show pairC (elemV j i a.2) (elemV i j a.1) = false
    rw [e5, h5]
  · obtain ⟨-, h1, -, h2, -⟩ := hv a ha
    exact Prod.ext (h.invol a.1 h1).1 (h.invol a.2 h2).2
  · obtain ⟨-, -, -, h1, -⟩ := hv a ha
    obtain ⟨-, h2, -⟩ := hv b hb
    exact h.pair a.2 h1 b.1 h2
  · obtain ⟨-, h1, -, h2, -⟩ := hv a ha
    obtain ⟨-, h3, -, h4, -⟩ := hv b hb
    exact Prod.ext (h.add a.1 h1 b.1 h3).1 (h.add a.2 h2 b.2 h4).2

private theorem isAutC_01 : IsAutC (elemC 0 1) :=
  isAutC_of_elemOK ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
private theorem isAutC_12 : IsAutC (elemC 1 2) :=
  isAutC_of_elemOK ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
private theorem isAutC_23 : IsAutC (elemC 2 3) :=
  isAutC_of_elemOK ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
private theorem isAutC_30 : IsAutC (elemC 3 0) :=
  isAutC_of_elemOK ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
private theorem isAutC_02 : IsAutC (elemC 0 2) :=
  isAutC_of_elemOK ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
private theorem isAutC_31 : IsAutC (elemC 3 1) :=
  isAutC_of_elemOK ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

@[expose] def stabGens : List (ℕ × ℕ → ℕ × ℕ) := [elemC 2 3, elemC 0 2, elemC 3 1]

@[expose] def allGens : List (ℕ × ℕ → ℕ × ℕ) :=
  stabGens ++ [elemC 0 1, elemC 1 2, elemC 3 0]

theorem isAutC_of_mem_allGens {g : ℕ × ℕ → ℕ × ℕ} (hg : g ∈ allGens) : IsAutC g := by
  simp only [allGens, stabGens, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl) | rfl | rfl | rfl
  · exact isAutC_23
  · exact isAutC_02
  · exact isAutC_31
  · exact isAutC_01
  · exact isAutC_12
  · exact isAutC_30

namespace IsAutC

variable {g : ℕ × ℕ → ℕ × ℕ} (hg : IsAutC g)
include hg

theorem adjC_eq {a b : ℕ × ℕ} (ha : validC 4 a = true) (hb : validC 4 b = true) :
    adjC (g a) (g b) = adjC a b := by
  have ha' := mem_allC.mpr ha
  have hb' := mem_allC.mpr hb
  simp only [adjC, hg.pair a ha' b hb', hg.pair b hb' a ha']

theorem injOn {R : Finset (ℕ × ℕ)} (hR : ∀ x ∈ R, validC 4 x = true) : Set.InjOn g R := by
  intro a ha b hb hab
  have h1 := hg.invol a (mem_allC.mpr (hR a ha))
  have h2 := hg.invol b (mem_allC.mpr (hR b hb))
  rw [← h1, ← h2, hab]

theorem codedSet_image {R : Finset (ℕ × ℕ)} (hR : CodedSet 4 R) : CodedSet 4 (R.image g) where
  valid := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hg.valid a (mem_allC.mpr (hR.valid a ha))
  closed := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rw [hg.adjC_eq (hR.valid a ha) (hR.valid b hb)] at hxy
    rw [← hg.add a (mem_allC.mpr (hR.valid a ha)) b (mem_allC.mpr (hR.valid b hb)) hxy]
    exact Finset.mem_image_of_mem _ (hR.closed a ha b hb hxy)
  sym := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rw [hg.pair a (mem_allC.mpr (hR.valid a ha)) b (mem_allC.mpr (hR.valid b hb)),
      hg.pair b (mem_allC.mpr (hR.valid b hb)) a (mem_allC.mpr (hR.valid a ha))]
    exact hR.sym a ha b hb
  conn := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    refine (hR.conn a ha b hb).lift g fun u v huv => ?_
    refine ⟨Finset.mem_image_of_mem _ huv.1, Finset.mem_image_of_mem _ huv.2.1, ?_⟩
    rw [hg.adjC_eq (hR.valid u huv.1) (hR.valid v huv.2.1)]
    exact huv.2.2

theorem goodSet_of_image {R : Finset (ℕ × ℕ)} (hR : CodedSet 4 R) {tab : List (ℕ × ℕ)}
    (h : GoodSet tab (R.image g)) : GoodSet tab R := by
  obtain ⟨e, he, hcard, hval⟩ := h
  have hinj := hg.injOn hR.valid
  refine ⟨e, he, ?_, fun p hp => ?_⟩
  · rw [← hcard, Finset.card_image_of_injOn hinj]
  · have hfilt : (R.image g).filter (fun q => q ≠ g p ∧ adjC (g p) q = false) =
        (R.filter fun q => q ≠ p ∧ adjC p q = false).image g := by
      ext q'
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, hne, hadj⟩
        refine ⟨q, ⟨hq, fun h => hne (h ▸ rfl), ?_⟩, rfl⟩
        rwa [hg.adjC_eq (hR.valid p hp) (hR.valid q hq)] at hadj
      · rintro ⟨q, ⟨hq, hne, hadj⟩, rfl⟩
        refine ⟨⟨q, hq, rfl⟩, fun h => hne (hinj hq hp h), ?_⟩
        rwa [hg.adjC_eq (hR.valid p hp) (hR.valid q hq)]
    rw [← Finset.card_image_of_injOn (f := g)
      (hinj.mono fun x hx => (Finset.mem_filter.mp hx).1), ← hfilt]
    exact hval _ (Finset.mem_image_of_mem _ hp)

end IsAutC

inductive Red (gens : List (ℕ × ℕ → ℕ × ℕ)) (a₀ b₀ : ℕ × ℕ) : ℕ × ℕ → ℕ × ℕ → Prop
  | base : Red gens a₀ b₀ a₀ b₀
  | step (g : ℕ × ℕ → ℕ × ℕ) (hg : g ∈ gens) {a b : ℕ × ℕ} :
      Red gens a₀ b₀ (g a) (g b) → Red gens a₀ b₀ a b

theorem Red.normalize {gens : List (ℕ × ℕ → ℕ × ℕ)} (hgens : ∀ g ∈ gens, IsAutC g)
    {a₀ b₀ a b : ℕ × ℕ} (h : Red gens a₀ b₀ a b) :
    ∀ R : Finset (ℕ × ℕ), CodedSet 4 R → a ∈ R → b ∈ R →
      ∃ R' : Finset (ℕ × ℕ), CodedSet 4 R' ∧ a₀ ∈ R' ∧ b₀ ∈ R' ∧
        ∀ tab, GoodSet tab R' → GoodSet tab R := by
  induction h with
  | base => exact fun R hR ha hb => ⟨R, hR, ha, hb, fun _ h => h⟩
  | @step g hg a b _ ih =>
    intro R hR ha hb
    obtain ⟨R', hR', h1, h2, h3⟩ := ih (R.image g) ((hgens g hg).codedSet_image hR)
      (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
    exact ⟨R', hR', h1, h2, fun tab h => (hgens g hg).goodSet_of_image hR (h3 tab h)⟩

theorem descent {X : Type*} {Q P : X → Prop} {gens : List (X → X)} {depth : X → ℕ} {x₀ : X}
    (hx₀ : P x₀) (hdesc : ∀ x, Q x → x ≠ x₀ → ∃ g ∈ gens, Q (g x) ∧ depth (g x) < depth x)
    (hstep : ∀ g ∈ gens, ∀ x, Q x → P (g x) → P x) : ∀ x, Q x → P x := by
  intro x
  induction h : depth x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hQ
    by_cases hx : x = x₀
    · rw [hx]
      exact hx₀
    · obtain ⟨g, hg, hQg, hlt⟩ := hdesc x hQ hx
      exact hstep g hg x hQ (ih (depth (g x)) (h ▸ hlt) (g x) rfl hQg)

@[expose] def lookupD (tab : List ((ℕ × ℕ) × ℕ)) (a : ℕ × ℕ) : ℕ :=
  tab.foldr (fun e r => if e.1 == a then e.2 else r) 0

@[expose] def depth1 : List ((ℕ × ℕ) × ℕ) := [
  ((1, 2), 0), ((1, 4), 4), ((1, 6), 1), ((1, 8), 4), ((1, 10), 3), ((1, 12), 3), ((1, 14), 2),
  ((2, 1), 8), ((2, 4), 7), ((2, 5), 7), ((2, 8), 7), ((2, 9), 7), ((2, 12), 6), ((2, 13), 6),
  ((3, 3), 7), ((3, 4), 6), ((3, 7), 6), ((3, 8), 6), ((3, 11), 6), ((3, 12), 5), ((3, 15), 5),
  ((4, 1), 7), ((4, 2), 4), ((4, 3), 6), ((4, 8), 7), ((4, 9), 6), ((4, 10), 6), ((4, 11), 5),
  ((5, 2), 3), ((5, 5), 6), ((5, 7), 5), ((5, 8), 6), ((5, 10), 6), ((5, 13), 5), ((5, 15), 4),
  ((6, 1), 7), ((6, 6), 5), ((6, 7), 7), ((6, 8), 6), ((6, 9), 6), ((6, 14), 6), ((6, 15), 6),
  ((7, 3), 6), ((7, 5), 7), ((7, 6), 4), ((7, 8), 5), ((7, 11), 5), ((7, 13), 6), ((7, 14), 5),
  ((8, 1), 7), ((8, 2), 4), ((8, 3), 6), ((8, 4), 6), ((8, 5), 7), ((8, 6), 5), ((8, 7), 6),
  ((9, 2), 1), ((9, 4), 5), ((9, 6), 2), ((9, 9), 5), ((9, 11), 4), ((9, 13), 4), ((9, 15), 3),
  ((10, 1), 7), ((10, 4), 7), ((10, 5), 8), ((10, 10), 6), ((10, 11), 7), ((10, 14), 5),
  ((10, 15), 6), ((11, 3), 6), ((11, 4), 6), ((11, 7), 7), ((11, 9), 7), ((11, 10), 5),
  ((11, 13), 6), ((11, 14), 4), ((12, 1), 6), ((12, 2), 3), ((12, 3), 5), ((12, 12), 5),
  ((12, 13), 6), ((12, 14), 4), ((12, 15), 5), ((13, 2), 2), ((13, 5), 5), ((13, 7), 4),
  ((13, 9), 6), ((13, 11), 5), ((13, 12), 4), ((13, 14), 3), ((14, 1), 6), ((14, 6), 4),
  ((14, 7), 6), ((14, 10), 5), ((14, 11), 6), ((14, 12), 6), ((14, 13), 7), ((15, 3), 5),
  ((15, 5), 6), ((15, 6), 3), ((15, 9), 6), ((15, 10), 4), ((15, 12), 5), ((15, 15), 6)]

@[expose] def depth2 : List ((ℕ × ℕ) × ℕ) := [
  ((2, 1), 0), ((2, 5), 1), ((2, 9), 3), ((2, 13), 2), ((3, 3), 7), ((3, 7), 6), ((3, 11), 6),
  ((3, 15), 5), ((6, 1), 3), ((6, 7), 5), ((6, 9), 6), ((6, 15), 4), ((7, 3), 6), ((7, 5), 4),
  ((7, 11), 5), ((7, 13), 5), ((10, 1), 1), ((10, 5), 2), ((10, 11), 4), ((10, 15), 3),
  ((11, 3), 6), ((11, 7), 7), ((11, 9), 5), ((11, 13), 4), ((14, 1), 2), ((14, 7), 4),
  ((14, 11), 5), ((14, 13), 3), ((15, 3), 5), ((15, 5), 3), ((15, 9), 4), ((15, 15), 6)]

private theorem check_fix : stabGens.all (fun g => g (1, 2) == (1, 2)) = true := by
  decide +kernel

private theorem check_depth1 : (allC 4).all (fun a => a == (1, 2) ||
    allGens.any fun g => lookupD depth1 (g a) < lookupD depth1 a) = true := by
  decide +kernel

private theorem check_depth2 : (allC 4).all (fun b => !adjC (1, 2) b || b == (2, 1) ||
    stabGens.any fun g => lookupD depth2 (g b) < lookupD depth2 b) = true := by
  decide +kernel

theorem red_of_adj {a b : ℕ × ℕ} (ha : validC 4 a = true) (hb : validC 4 b = true)
    (hab : adjC a b = true) : Red allGens (1, 2) (2, 1) a b := by
  have hfix : ∀ g ∈ stabGens, g (1, 2) = (1, 2) := by
    intro g hg
    have := List.all_eq_true.mp check_fix g hg
    simpa using this
  have hB : ∀ b, validC 4 b = true → adjC (1, 2) b = true →
      Red allGens (1, 2) (2, 1) (1, 2) b := by
    intro b
    refine descent (Q := fun b => validC 4 b = true ∧ adjC (1, 2) b = true)
      (P := fun b => Red allGens (1, 2) (2, 1) (1, 2) b) (gens := stabGens)
      (depth := lookupD depth2) (x₀ := (2, 1)) Red.base ?_ ?_ b |> fun h hv ha => h ⟨hv, ha⟩
    · intro x hx hne
      have := List.all_eq_true.mp check_depth2 x (mem_allC.mpr hx.1)
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, List.any_eq_true,
        decide_eq_true_eq] at this
      rcases this with (h1 | h1) | ⟨g, hg, hlt⟩
      · exact absurd hx.2 (by simp [h1])
      · exact absurd h1 hne
      · refine ⟨g, hg, ⟨?_, ?_⟩, hlt⟩
        · exact (isAutC_of_mem_allGens (List.mem_append_left _ hg)).valid x (mem_allC.mpr hx.1)
        · have hgA := isAutC_of_mem_allGens (List.mem_append_left _ hg)
          rw [← hfix g hg, hgA.adjC_eq (mem_allC.mp (by decide : (1, 2) ∈ allC 4)) hx.1]
          exact hx.2
    · intro g hg x hx hP
      refine Red.step g (List.mem_append_left _ hg) ?_
      rw [hfix g hg]
      exact hP
  have hA : ∀ a, validC 4 a = true → ∀ b, validC 4 b = true → adjC a b = true →
      Red allGens (1, 2) (2, 1) a b := by
    intro a
    refine descent (Q := fun a => validC 4 a = true)
      (P := fun a => ∀ b, validC 4 b = true → adjC a b = true → Red allGens (1, 2) (2, 1) a b)
      (gens := allGens) (depth := lookupD depth1) (x₀ := (1, 2)) hB ?_ ?_ a
    · intro x hx hne
      have := List.all_eq_true.mp check_depth1 x (mem_allC.mpr hx)
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq] at this
      rcases this with h1 | ⟨g, hg, hlt⟩
      · exact absurd h1 hne
      · exact ⟨g, hg, (isAutC_of_mem_allGens hg).valid x (mem_allC.mpr hx), hlt⟩
    · intro g hg x hx hP b hb hxb
      have hgA := isAutC_of_mem_allGens hg
      refine Red.step g hg (hP (g b) (hgA.valid b (mem_allC.mpr hb)) ?_)
      rw [hgA.adjC_eq hx hb]
      exact hxb
  exact hA a ha b hb hab

private def fam4 : List (List (ℕ × ℕ)) := [
  [(1, 2), (2, 1), (3, 3)],
  [(1, 2), (1, 6), (2, 1), (2, 5), (3, 3), (3, 7)],
  [(1, 2), (1, 10), (2, 1), (2, 9), (3, 3), (3, 11)],
  [(1, 2), (1, 14), (2, 1), (2, 13), (3, 3), (3, 15)],
  [(1, 2), (2, 1), (3, 3), (5, 2), (6, 1), (7, 3)],
  [(1, 2), (2, 1), (3, 3), (5, 10), (6, 9), (7, 11)],
  [(1, 2), (2, 1), (3, 3), (9, 2), (10, 1), (11, 3)],
  [(1, 2), (2, 1), (3, 3), (9, 6), (10, 5), (11, 7)],
  [(1, 2), (2, 1), (3, 3), (13, 2), (14, 1), (15, 3)],
  [(1, 2), (2, 1), (3, 3), (13, 14), (14, 13), (15, 15)],
  [
    (1, 2), (1, 14), (2, 1), (2, 13), (3, 3), (3, 15), (13, 2), (13, 14), (14, 1), (14, 13),
    (15, 3), (15, 15)],
  [(1, 2), (2, 1), (3, 3), (4, 8), (9, 6), (10, 5), (11, 7), (13, 14), (14, 13), (15, 15)],
  [(1, 2), (2, 1), (3, 3), (5, 10), (6, 9), (7, 11), (8, 4), (13, 14), (14, 13), (15, 15)],
  [
    (1, 2), (2, 1), (3, 3), (4, 8), (5, 10), (6, 9), (7, 11), (8, 4), (9, 6), (10, 5), (11, 7),
    (12, 12), (13, 14), (14, 13), (15, 15)],
  [
    (1, 2), (2, 1), (3, 3), (5, 2), (6, 1), (7, 3), (9, 2), (10, 1), (11, 3), (13, 2), (14, 1),
    (15, 3)],
  [
    (1, 2), (1, 6), (2, 1), (2, 5), (3, 3), (3, 7), (9, 2), (9, 6), (10, 1), (10, 5), (11, 3),
    (11, 7)],
  [(1, 2), (2, 1), (3, 3), (5, 10), (6, 9), (7, 11), (9, 6), (10, 5), (11, 7), (12, 12)],
  [
    (1, 2), (1, 10), (2, 1), (2, 9), (3, 3), (3, 11), (5, 2), (5, 10), (6, 1), (6, 9), (7, 3),
    (7, 11)],
  [
    (1, 2), (1, 6), (1, 10), (1, 14), (2, 1), (2, 5), (2, 9), (2, 13), (3, 3), (3, 7), (3, 11),
    (3, 15)]
]

private theorem familyOK_four : familyOK 4 30 fam4 = true := by decide +kernel

private theorem tableOK_four :
    tableOK [(1, 0), (3, 0), (6, 1), (10, 3), (12, 3), (15, 6)] fam4 = true := by
  decide +kernel

private theorem seed_mem : [(1, 2), (2, 1), (3, 3)] ∈ fam4 := by decide

theorem goodSet_four {R : Finset (ℕ × ℕ)} (hne : R.Nonempty) (hR : CodedSet 4 R) :
    GoodSet [(1, 0), (3, 0), (6, 1), (10, 3), (12, 3), (15, 6)] R := by
  by_cases hadj : ∃ a ∈ R, ∃ b ∈ R, adjC a b = true
  · obtain ⟨a, ha, b, hb, hab⟩ := hadj
    obtain ⟨R', hR', h1, h2, h3⟩ := (red_of_adj (hR.valid a ha) (hR.valid b hb) hab).normalize
      (fun g hg => isAutC_of_mem_allGens hg) R hR ha hb
    refine h3 _ (classification_of_family (d := 4) (by norm_num) familyOK_four tableOK_four hR' ?_)
    have h12 : adjC (1, 2) (2, 1) = true := by decide
    refine ⟨[(1, 2), (2, 1), (3, 3)], seed_mem, by simp, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact hR'.closed _ h1 _ h2 h12
  · push Not at hadj
    have hsingle : ∀ a ∈ R, ∀ b ∈ R, a = b := by
      intro a ha b hb
      have h := hR.conn a ha b hb
      induction h with
      | refl => rfl
      | @tail u v _ hstep _ => exact absurd (hadj u hstep.1 v hstep.2.1) (by simp [hstep.2.2])
    obtain ⟨p₀, hp₀⟩ := hne
    refine ⟨(1, 0), by simp, ?_, fun p hp => ?_⟩
    · exact Finset.card_eq_one.mpr ⟨p₀, Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hp₀, fun x hx => hsingle x hx p₀ hp₀⟩⟩
    · rw [Finset.card_eq_zero.mpr]
      exact Finset.filter_eq_empty_iff.mpr fun q hq hq' => hq'.1 (hsingle q hq p hp)

section Dimension

variable {A : Type*} [AddCommGroup A]

theorem rootSet_classification_four (h2 : ∀ x : A, x + x = 0) (hcard : Nat.card A = 16)
    (R : Finset (Datum A)) (hne : R.Nonempty) (hs : IsSymm R) (hc : IsClosed R)
    (hconn : IsConn R) :
    R.card = 1 ∨ (R.card = 3 ∧ ∀ p ∈ R, ∀ q ∈ R, p ≠ q → p.Adj q) ∨
      (R.card = 6 ∧ ∀ p ∈ R, ∃! q, q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q) ∨
      (R.card = 10 ∧ ∀ p ∈ R, Set.ncard {q | q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q} = 3) ∨
      (R.card = 12 ∧ ∀ p ∈ R, Set.ncard {q | q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q} = 3) ∨
      (R.card = 15 ∧ ∀ p ∈ R, Set.ncard {q | q ∈ R ∧ q ≠ p ∧ ¬ p.Adj q} = 6) := by
  obtain ⟨x, hx, hcd, hval⟩ := classification_of_card encOK_four
    (fun _ hne hR => goodSet_four hne hR) h2 (hcard.trans (by norm_num : 16 = 2 ^ 4)) R hne hs hc
    hconn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hcd
  · refine Or.inr (Or.inl ⟨hcd, fun p hp q hq hpq => ?_⟩)
    exact adj_of_ncard_eq_zero (hval p hp) q hq (Ne.symm hpq)
  · exact Or.inr (Or.inr (Or.inl ⟨hcd, fun p hp => existsUnique_of_ncard_eq_one (hval p hp)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hcd, hval⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hcd, hval⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hcd, hval⟩))))

end Dimension

end CFSG.ClassicalInvolution.SmallWeyl

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.SmallWeyl

variable {ι V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {T : RootFamily ι V}

theorem RootFamily.dataFinset_classification_four [Finite V] [Nonempty ι] (hT : T.Nondegenerate)
    (hV : Nat.card V = 16) :
    (T.dataFinset hT).card = 1 ∨ ((T.dataFinset hT).card = 3 ∧
      ∀ i j, T.datum hT i ≠ T.datum hT j → T.χ i (T.z j) = 1) ∨
      ((T.dataFinset hT).card = 6 ∧ ∀ i, ∃! q, q ∈ T.dataFinset hT ∧ q ≠ T.datum hT i ∧
        ¬ (T.datum hT i).Adj q) ∨
      ((T.dataFinset hT).card = 10 ∧ ∀ i, Set.ncard {q | q ∈ T.dataFinset hT ∧
        q ≠ T.datum hT i ∧ ¬ (T.datum hT i).Adj q} = 3) ∨
      ((T.dataFinset hT).card = 12 ∧ ∀ i, Set.ncard {q | q ∈ T.dataFinset hT ∧
        q ≠ T.datum hT i ∧ ¬ (T.datum hT i).Adj q} = 3) ∨
      ((T.dataFinset hT).card = 15 ∧ ∀ i, Set.ncard {q | q ∈ T.dataFinset hT ∧
        q ≠ T.datum hT i ∧ ¬ (T.datum hT i).Adj q} = 6) := by
  have hmem : ∀ i, T.datum hT i ∈ T.dataFinset hT := fun i => (T.mem_dataFinset hT).mpr ⟨i, rfl⟩
  rcases rootSet_classification_four RootFamily.add_self_eq_zero hV (T.dataFinset hT)
    (T.dataFinset_nonempty hT) (T.dataFinset_isSymm hT) (T.dataFinset_isClosed hT)
    (T.dataFinset_isConn hT) with h | ⟨h3, hadj⟩ | ⟨h6, hu⟩ | ⟨h10, hv⟩ | ⟨h12, hv⟩ | ⟨h15, hv⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨h3, fun i j hij => ?_⟩)
    exact (T.datum_adj_iff hT).mp (hadj _ (hmem i) _ (hmem j) hij)
  · exact Or.inr (Or.inr (Or.inl ⟨h6, fun i => hu _ (hmem i)⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h10, fun i => hv _ (hmem i)⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h12, fun i => hv _ (hmem i)⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h15, fun i => hv _ (hmem i)⟩))))

end CFSG.ClassicalInvolution.Balance
