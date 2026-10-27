module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporBFS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash
public import Std.Data.HashSet.Lemmas

public section

namespace CFSG.KC.LQT.PWSnd

open CFSG.QuasithinUnique.Vol2Native.L239

section Closure

variable {X : Type*} [Group X]

@[expose] def Ball (gens : List X) : ℕ → Set X
  | 0 => {1}
  | k + 1 => Ball gens k ∪ {y | ∃ g ∈ gens, ∃ x ∈ Ball gens k, y = g * x}

theorem ball_succ_eq (gens : List X) (k : ℕ) :
    Ball gens (k + 1) = Ball gens k ∪ {y | ∃ g ∈ gens, ∃ x ∈ Ball gens k, y = g * x} := rfl

theorem ball_mono (gens : List X) {k l : ℕ} (h : k ≤ l) : Ball gens k ⊆ Ball gens l := by
  have step : ∀ m : ℕ, Ball gens m ⊆ Ball gens (m + 1) := by
    intro m y hy
    rw [ball_succ_eq]
    exact Or.inl hy
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction j with
  | zero => exact fun y hy => hy
  | succ j ih => exact ih.trans (step _)

theorem one_mem_ball (gens : List X) (k : ℕ) : (1 : X) ∈ Ball gens k := by
  induction k with
  | zero => exact Set.mem_singleton _
  | succ k ih =>
    rw [ball_succ_eq]
    exact Or.inl ih

theorem mul_mem_ball (gens : List X) {g x : X} (hg : g ∈ gens) {k : ℕ} (hx : x ∈ Ball gens k) :
    g * x ∈ Ball gens (k + 1) := by
  rw [ball_succ_eq]
  exact Or.inr ⟨g, hg, x, hx, rfl⟩

theorem ball_subset_closure (gens : List X) (k : ℕ) :
    Ball gens k ⊆ (Subgroup.closure {g | g ∈ gens} : Set X) := by
  induction k with
  | zero =>
    intro y hy
    have hy1 : y = 1 := hy
    subst hy1
    exact SetLike.mem_coe.2 (Subgroup.one_mem _)
  | succ k ih =>
    intro y hy
    rw [ball_succ_eq] at hy
    rcases hy with hy | ⟨g, hg, x, hx, rfl⟩
    · exact ih hy
    · exact SetLike.mem_coe.2 (Subgroup.mul_mem _
        (Subgroup.subset_closure (show g ∈ {g | g ∈ gens} from hg)) (SetLike.mem_coe.1 (ih hx)))

theorem ball_subset_of_closed (gens : List X) (T : Set X) (h1 : (1 : X) ∈ T)
    (hcl : ∀ g ∈ gens, ∀ x ∈ T, g * x ∈ T) (k : ℕ) : Ball gens k ⊆ T := by
  induction k with
  | zero =>
    intro y hy
    have hy1 : y = 1 := hy
    subst hy1
    exact h1
  | succ k ih =>
    intro y hy
    rw [ball_succ_eq] at hy
    rcases hy with hy | ⟨g, hg, x, hx, rfl⟩
    · exact ih hy
    · exact hcl g hg x (ih hx)

theorem closure_subset_of_closed [Finite X] (gens : List X) (T : Set X) (h1 : (1 : X) ∈ T)
    (hcl : ∀ g ∈ gens, ∀ x ∈ T, g * x ∈ T) : (Subgroup.closure {g | g ∈ gens} : Set X) ⊆ T := by
  have key : ∀ a ∈ Subgroup.closure {g | g ∈ gens}, ∀ y ∈ T, a * y ∈ T := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem g hg => exact fun y hy => hcl g hg y hy
    | one => exact fun y hy => by simpa using hy
    | mul a b _ _ ha hb => exact fun y hy => by rw [mul_assoc]; exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      have hpow : ∀ n : ℕ, a ^ n * y ∈ T := by
        intro n
        induction n with
        | zero => simpa using hy
        | succ n ih => rw [pow_succ', mul_assoc]; exact ha _ ih
      have hpos := orderOf_pos a
      have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv', ← pow_succ', Nat.sub_add_cancel hpos,
          pow_orderOf_eq_one]
      rw [hinv]
      exact hpow _
  intro x hx
  simpa using key x hx 1 h1

theorem ball_stable (gens : List X) {k : ℕ} (h : Ball gens (k + 1) ⊆ Ball gens k) (j : ℕ) :
    Ball gens (k + j) ⊆ Ball gens k := by
  induction j with
  | zero =>
    intro y hy
    simpa using hy
  | succ j ih =>
    intro y hy
    have hy' : y ∈ Ball gens (k + j + 1) := hy
    rw [ball_succ_eq] at hy'
    rcases hy' with hy' | ⟨g, hg, x, hx, rfl⟩
    · exact ih hy'
    · exact h (mul_mem_ball gens hg (ih hx))


private def layerH_stepH (nrm : X → X) (enc : X → ℕ) (x : X) (q : List X × Std.HashSet ℕ) (g : X) :
    List X × Std.HashSet ℕ :=
  if q.2.contains (enc (nrm (g * x))) then q
  else (nrm (g * x) :: q.1, q.2.insert (enc (nrm (g * x))))

private abbrev layerH_Inv (nrm : X → X) (enc : X → ℕ) (gens : List X) (seen : Std.HashSet ℕ)
    (frontier : List X) (p : List X × Std.HashSet ℕ) : Prop :=
  p.1.Nodup ∧ (∀ y ∈ p.1, seen.contains (enc y) = false) ∧
    (∀ y ∈ p.1, ∃ g ∈ gens, ∃ x ∈ frontier, y = nrm (g * x)) ∧
    (∀ e, p.2.contains e = true ↔ (seen.contains e = true ∨ ∃ y ∈ p.1, enc y = e))

private theorem layerH_step_spec (nrm : X → X) (enc : X → ℕ) (gens : List X)
    (seen : Std.HashSet ℕ) (frontier : List X) (x g : X) (hg : g ∈ gens) (hx : x ∈ frontier)
    (q : List X × Std.HashSet ℕ) (hq : layerH_Inv nrm enc gens seen frontier q) :
    layerH_Inv nrm enc gens seen frontier (layerH_stepH nrm enc x q g) ∧
    (layerH_stepH nrm enc x q g).2.contains (enc (nrm (g * x))) = true ∧
    ∀ e, q.2.contains e = true → (layerH_stepH nrm enc x q g).2.contains e = true := by
  obtain ⟨hnd, hseen, hgen, hiff⟩ := hq
  unfold layerH_stepH
  split_ifs with h
  · exact ⟨⟨hnd, hseen, hgen, hiff⟩, h, fun e he => he⟩
  · have hnot : ¬ (seen.contains (enc (nrm (g * x))) = true ∨
        ∃ y ∈ q.1, enc y = enc (nrm (g * x))) := by
      intro hc
      exact h ((hiff (enc (nrm (g * x)))).2 hc)
    have hseen' : seen.contains (enc (nrm (g * x))) = false := by
      cases hs : seen.contains (enc (nrm (g * x)))
      · rfl
      · exact absurd (Or.inl hs) hnot
    have hnin : nrm (g * x) ∉ q.1 := fun hm => hnot (Or.inr ⟨nrm (g * x), hm, rfl⟩)
    have hex : ∀ e, (∃ y ∈ nrm (g * x) :: q.1, enc y = e) ↔
        (enc (nrm (g * x)) = e ∨ ∃ y ∈ q.1, enc y = e) := by
      intro e
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases List.mem_cons.1 hy with h2 | h2
        · rw [h2]; exact Or.inl rfl
        · exact Or.inr ⟨y, h2, rfl⟩
      · rintro (h2 | ⟨y, hy, h2⟩)
        · exact ⟨nrm (g * x), List.mem_cons.2 (Or.inl rfl), h2⟩
        · exact ⟨y, List.mem_cons.2 (Or.inr hy), h2⟩
    refine ⟨⟨List.nodup_cons.2 ⟨hnin, hnd⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with h2 | h2
      · rw [h2]; exact hseen'
      · exact hseen y h2
    · intro y hy
      rcases List.mem_cons.1 hy with h2 | h2
      · exact ⟨g, hg, x, hx, h2⟩
      · exact hgen y h2
    · intro e
      try dsimp only
      rw [Std.HashSet.contains_insert, Bool.or_eq_true_iff, beq_iff_eq, hiff e, hex e]
      tauto
    · try dsimp only
      simp [Std.HashSet.contains_insert]
    · intro e he
      try dsimp only
      simp [Std.HashSet.contains_insert, he]

private theorem layerH_inner_spec (nrm : X → X) (enc : X → ℕ) (gens : List X)
    (seen : Std.HashSet ℕ) (frontier : List X) (x : X) (hx : x ∈ frontier) :
    ∀ (gl : List X), (∀ g ∈ gl, g ∈ gens) → ∀ (q : List X × Std.HashSet ℕ),
      layerH_Inv nrm enc gens seen frontier q →
      layerH_Inv nrm enc gens seen frontier (gl.foldl (layerH_stepH nrm enc x) q) ∧
      (∀ g ∈ gl, (gl.foldl (layerH_stepH nrm enc x) q).2.contains (enc (nrm (g * x))) = true) ∧
      ∀ e, q.2.contains e = true → (gl.foldl (layerH_stepH nrm enc x) q).2.contains e = true := by
  intro gl
  induction gl with
  | nil =>
    intro _ q hq
    exact ⟨hq, fun g hg => by simp at hg, fun e he => he⟩
  | cons g gl ih =>
    intro hgl q hq
    obtain ⟨h1, h2, h3⟩ := layerH_step_spec nrm enc gens seen frontier x g
      (hgl g (List.mem_cons.2 (Or.inl rfl))) hx q hq
    obtain ⟨k1, k2, k3⟩ := ih (fun g' hg' => hgl g' (List.mem_cons.2 (Or.inr hg')))
      (layerH_stepH nrm enc x q g) h1
    simp only [List.foldl_cons]
    refine ⟨k1, ?_, fun e he => k3 e (h3 e he)⟩
    intro g' hg'
    rcases List.mem_cons.1 hg' with h4 | h4
    · rw [h4]; exact k3 _ h2
    · exact k2 g' h4

private theorem layerH_outer_spec (nrm : X → X) (enc : X → ℕ) (gens : List X)
    (seen : Std.HashSet ℕ) (frontier : List X) :
    ∀ (fr : List X), (∀ x ∈ fr, x ∈ frontier) → ∀ (q : List X × Std.HashSet ℕ),
      layerH_Inv nrm enc gens seen frontier q →
      layerH_Inv nrm enc gens seen frontier
        (fr.foldl (fun (p : List X × Std.HashSet ℕ) x => gens.foldl (layerH_stepH nrm enc x) p) q) ∧
      (∀ x ∈ fr, ∀ g ∈ gens,
        (fr.foldl (fun (p : List X × Std.HashSet ℕ) x => gens.foldl (layerH_stepH nrm enc x) p)
          q).2.contains (enc (nrm (g * x))) = true) ∧
      ∀ e, q.2.contains e = true →
        (fr.foldl (fun (p : List X × Std.HashSet ℕ) x => gens.foldl (layerH_stepH nrm enc x) p)
          q).2.contains e = true := by
  intro fr
  induction fr with
  | nil =>
    intro _ q hq
    exact ⟨hq, fun x hx => by simp at hx, fun e he => he⟩
  | cons x fr ih =>
    intro hfr q hq
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := layerH_inner_spec nrm enc gens seen frontier x
      (hfr x (List.mem_cons.2 (Or.inl rfl))) gens (fun g hg => hg) q hq
    obtain ⟨k1, k2, k3⟩ := ih (fun x' hx' => hfr x' (List.mem_cons.2 (Or.inr hx')))
      (gens.foldl (layerH_stepH nrm enc x) q) h1
    refine ⟨k1, ?_, fun e he => k3 e (h3 e he)⟩
    intro x' hx' g hg
    rcases List.mem_cons.1 hx' with h4 | h4
    · rw [h4]; exact k3 _ (h2 g hg)
    · exact k2 x' h4 g hg

theorem layerH_spec (nrm : X → X) (hnrm : ∀ x, nrm x = x) (enc : X → ℕ) (gens : List X)
    (seen : Std.HashSet ℕ) (frontier : List X) :
    (layerH nrm enc gens seen frontier).1.Nodup ∧
    (∀ y ∈ (layerH nrm enc gens seen frontier).1, seen.contains (enc y) = false) ∧
    (∀ y ∈ (layerH nrm enc gens seen frontier).1, ∃ g ∈ gens, ∃ x ∈ frontier, y = g * x) ∧
    (∀ e, (layerH nrm enc gens seen frontier).2.contains e = true ↔
      (seen.contains e = true ∨ ∃ y ∈ (layerH nrm enc gens seen frontier).1, enc y = e)) ∧
    (∀ g ∈ gens, ∀ x ∈ frontier,
      (layerH nrm enc gens seen frontier).2.contains (enc (g * x)) = true) := by
  have hlayer : layerH nrm enc gens seen frontier =
      frontier.foldl (fun (p : List X × Std.HashSet ℕ) x => gens.foldl (layerH_stepH nrm enc x) p)
        ([], seen) := rfl
  have h0 : layerH_Inv nrm enc gens seen frontier ([], seen) := by
    refine ⟨List.nodup_nil, fun y hy => by simp at hy, fun y hy => by simp at hy, fun e => ?_⟩
    simp
  obtain ⟨hL, hG, -⟩ := layerH_outer_spec nrm enc gens seen frontier frontier
    (fun x hx => hx) ([], seen) h0
  obtain ⟨k1, k2, k3, k4⟩ := hL
  rw [hlayer]
  refine ⟨k1, k2, fun y hy => ?_, k4, fun g hg x hx => ?_⟩
  · obtain ⟨g', hg', x', hx', h⟩ := k3 y hy
    exact ⟨g', hg', x', hx', h.trans (hnrm (g' * x'))⟩
  · have h := hG x hx g hg
    rw [hnrm] at h
    exact h


@[expose] def CInv (gens : List X) (enc : X → ℕ) (k : ℕ) (all : List X) (seen : Std.HashSet ℕ)
    (frontier : List X) : Prop :=
  all.Nodup ∧ (∀ y ∈ all, y ∈ Ball gens k) ∧ (∀ y ∈ Ball gens k, y ∈ all) ∧
    (∀ e, seen.contains e = true ↔ ∃ y ∈ all, enc y = e) ∧ (∀ x ∈ frontier, x ∈ all) ∧
    (∀ y ∈ Ball gens (k + 1), y ∈ all ∨ ∃ g ∈ gens, ∃ x ∈ frontier, y = g * x)

theorem closureH_spec (nrm : X → X) (hnrm : ∀ x, nrm x = x) (enc : X → ℕ) (gens : List X) :
    ∀ (f k : ℕ) (all : List X) (seen : Std.HashSet ℕ) (frontier : List X),
      CInv gens enc k all seen frontier →
      (∀ x ∈ Ball gens (k + f), ∀ y ∈ Ball gens (k + f), enc x = enc y → x = y) →
      (closureH nrm enc gens f all seen frontier).Nodup ∧
        ∀ y, y ∈ closureH nrm enc gens f all seen frontier ↔ y ∈ Ball gens (k + f) := by
  intro f
  induction f with
  | zero =>
    intro k all seen frontier hI _
    obtain ⟨ha, hb, hc, -⟩ := hI
    have e : closureH nrm enc gens 0 all seen frontier = all := rfl
    rw [e]
    exact ⟨ha, fun y => ⟨fun hy => hb y hy, fun hy => hc y hy⟩⟩
  | succ f ih =>
    intro k all seen frontier hI hinj
    have hI0 := hI
    obtain ⟨hnd, hsub, hsup, hseen, hfr, hnext⟩ := hI
    obtain ⟨hl1, hl2, hl3, hl4, hl5⟩ := layerH_spec nrm hnrm enc gens seen frontier
    have hinj1 : ∀ x ∈ Ball gens (k + 1), ∀ y ∈ Ball gens (k + 1), enc x = enc y → x = y :=
      fun x hx y hy e => hinj x (ball_mono gens (by omega) hx) y (ball_mono gens (by omega) hy) e
    have hr1sub : ∀ y ∈ (layerH nrm enc gens seen frontier).1, y ∈ Ball gens (k + 1) := by
      intro y hy
      obtain ⟨g, hg, x, hx, rfl⟩ := hl3 y hy
      exact mul_mem_ball gens hg (hsub x (hfr x hx))
    have hnotall : ∀ y ∈ (layerH nrm enc gens seen frontier).1, y ∉ all := by
      intro y hy hya
      have h1 := hl2 y hy
      have h2 := (hseen (enc y)).2 ⟨y, hya, rfl⟩
      rw [h1] at h2
      exact absurd h2 (by decide)
    have hcov : ∀ g ∈ gens, ∀ x ∈ frontier,
        g * x ∈ all ++ (layerH nrm enc gens seen frontier).1 := by
      intro g hg x hx
      have hgx : g * x ∈ Ball gens (k + 1) := mul_mem_ball gens hg (hsub x (hfr x hx))
      rcases (hl4 _).1 (hl5 g hg x hx) with h | ⟨y, hy, hey⟩
      · obtain ⟨y, hy, hey⟩ := (hseen _).1 h
        have hyk : y ∈ Ball gens (k + 1) := ball_mono gens (Nat.le_succ k) (hsub y hy)
        rw [← hinj1 y hyk (g * x) hgx hey]
        exact List.mem_append_left _ hy
      · have hyk : y ∈ Ball gens (k + 1) := hr1sub y hy
        rw [← hinj1 y hyk (g * x) hgx hey]
        exact List.mem_append_right _ hy
    have e : closureH nrm enc gens (f + 1) all seen frontier =
        if (layerH nrm enc gens seen frontier).1.isEmpty then all
        else closureH nrm enc gens f (all ++ (layerH nrm enc gens seen frontier).1.reverse)
          (layerH nrm enc gens seen frontier).2 (layerH nrm enc gens seen frontier).1.reverse := rfl
    rw [e]
    split_ifs with hemp
    · have hnil : (layerH nrm enc gens seen frontier).1 = [] := List.isEmpty_iff.1 hemp
      have hB : Ball gens (k + 1) ⊆ Ball gens k := by
        intro y hy
        apply hsub
        rcases hnext y hy with h | ⟨g, hg, x, hx, rfl⟩
        · exact h
        · have := hcov g hg x hx
          rw [hnil, List.append_nil] at this
          exact this
      have hS := ball_stable gens hB (f + 1)
      refine ⟨hnd, fun y => ⟨fun hy => ball_mono gens (by omega) (hsub y hy),
        fun hy => hsup y (hS hy)⟩⟩
    · have hI' : CInv gens enc (k + 1) (all ++ (layerH nrm enc gens seen frontier).1.reverse)
          (layerH nrm enc gens seen frontier).2 (layerH nrm enc gens seen frontier).1.reverse := by
        have hc' : ∀ y ∈ Ball gens (k + 1),
            y ∈ all ++ (layerH nrm enc gens seen frontier).1.reverse := by
          intro y hy
          rcases hnext y hy with h | ⟨g, hg, x, hx, rfl⟩
          · exact List.mem_append_left _ h
          · rcases List.mem_append.1 (hcov g hg x hx) with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_reverse.2 h)
        refine ⟨?_, ?_, hc', ?_, ?_, ?_⟩
        · refine List.nodup_append.2 ⟨hnd, List.nodup_reverse.2 hl1, ?_⟩
          intro a ha b hb hab
          exact hnotall b (List.mem_reverse.1 hb) (hab ▸ ha)
        · intro y hy
          rcases List.mem_append.1 hy with h | h
          · exact ball_mono gens (Nat.le_succ k) (hsub y h)
          · exact hr1sub y (List.mem_reverse.1 h)
        · intro e
          constructor
          · intro h
            rcases (hl4 e).1 h with h | ⟨y, hy, rfl⟩
            · obtain ⟨y, hy, rfl⟩ := (hseen e).1 h
              exact ⟨y, List.mem_append_left _ hy, rfl⟩
            · exact ⟨y, List.mem_append_right _ (List.mem_reverse.2 hy), rfl⟩
          · rintro ⟨y, hy, rfl⟩
            rcases List.mem_append.1 hy with hy | hy
            · exact (hl4 _).2 (Or.inl ((hseen _).2 ⟨y, hy, rfl⟩))
            · exact (hl4 _).2 (Or.inr ⟨y, List.mem_reverse.1 hy, rfl⟩)
        · intro x hx
          exact List.mem_append_right _ hx
        · intro y hy
          rcases hy with hy | ⟨g, hg, x', hx', rfl⟩
          · exact Or.inl (hc' y hy)
          · rcases List.mem_append.1 (hc' x' hx') with h | h
            · exact Or.inl (hc' _ (mul_mem_ball gens hg (hsub x' h)))
            · exact Or.inr ⟨g, hg, x', h, rfl⟩
      have hk : k + 1 + f = k + (f + 1) := by omega
      have key := ih (k + 1) _ _ _ hI' (by rw [hk]; exact hinj)
      rw [hk] at key
      exact key

theorem closureListH_spec (nrm : X → X) (hnrm : ∀ x, nrm x = x) (enc : X → ℕ) (gens : List X)
    (fuel : ℕ)
    (hinj : ∀ x ∈ Ball gens fuel, ∀ y ∈ Ball gens fuel, enc x = enc y → x = y) :
    (closureListH nrm enc gens fuel).Nodup ∧
      ∀ y, y ∈ closureListH nrm enc gens fuel ↔ y ∈ Ball gens fuel := by
  have hI : CInv gens enc 0 [1] ((∅ : Std.HashSet ℕ).insert (enc 1)) [1] := by
    refine ⟨List.nodup_singleton _, ?_, ?_, ?_, fun x hx => hx, ?_⟩
    · intro y hy
      rw [List.mem_singleton.1 hy]
      exact one_mem_ball gens 0
    · intro y hy
      have h1 : y = 1 := hy
      rw [h1]
      exact List.mem_singleton_self _
    · intro e
      rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
      constructor
      · intro h
        exact ⟨1, List.mem_singleton_self _, beq_iff_eq.1 h⟩
      · rintro ⟨y, hy, rfl⟩
        rw [List.mem_singleton.1 hy]
        exact beq_self_eq_true _
    · intro y hy
      rcases hy with hy | ⟨g, hg, x, hx, rfl⟩
      · exact Or.inl (List.mem_singleton.2 hy)
      · have h1 : x = 1 := hx
        exact Or.inr ⟨g, hg, 1, List.mem_singleton_self _, by rw [h1]⟩
  have key := closureH_spec nrm hnrm enc gens fuel 0 [1] _ [1] hI (by simpa using hinj)
  rw [Nat.zero_add] at key
  exact key

end Closure

section Orbit

variable {Γ : Type*} [Group Γ] {Ω : Type*} [MulAction Γ Ω]

@[expose] def OInv (enc : Ω → ℕ) (x₀ : Ω) (Tr : List Ω) (st : BfsState Ω ℕ) : Prop :=
  st.O.toList.Nodup ∧ (∀ e, st.seen.contains e = true ↔ ∃ y ∈ st.O.toList, enc y = e) ∧
    (∀ y ∈ st.O.toList, y ∈ Tr) ∧ x₀ ∈ st.O.toList

@[expose] def LoopInv (gens : List Γ) (enc : Ω → ℕ) (x₀ : Ω) (Tr : List Ω) (i : ℕ)
    (st : BfsState Ω ℕ) : Prop :=
  OInv enc x₀ Tr st ∧ i ≤ st.O.toList.length ∧
    ∀ x ∈ st.O.toList.take i, ∀ g ∈ gens, g • x ∈ st.O.toList

private theorem mem_of_append_eq {α : Type*} {l l' e : List α} {a : α} (h : l' = l ++ e)
    (ha : a ∈ l) : a ∈ l' := by
  rw [h]
  exact List.mem_append_left _ ha

private theorem oinv_push (enc : Ω → ℕ) (x₀ : Ω) (Tr : List Ω) (st : BfsState Ω ℕ)
    (z : Ω) (par lab : Array ℕ) (hI : OInv enc x₀ Tr st) (hz : z ∈ Tr)
    (hzn : ¬ st.seen.contains (enc z) = true) :
    OInv enc x₀ Tr ⟨st.O.push z, par, lab, st.seen.insert (enc z)⟩ := by
  obtain ⟨hnd, hseen, hTr, hx₀⟩ := hI
  unfold OInv
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (st.O.push z).toList.Nodup
    rw [Array.toList_push, List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    apply hzn
    exact (hseen _).2 ⟨a, ha, by rw [hab, hb]⟩
  · intro e
    change (st.seen.insert (enc z)).contains e = true ↔ ∃ y ∈ (st.O.push z).toList, enc y = e
    rw [Array.toList_push, Std.HashSet.contains_insert, Bool.or_eq_true_iff, beq_iff_eq,
      hseen e]
    constructor
    · rintro (h | ⟨y, hy, hye⟩)
      · exact ⟨z, List.mem_append_right _ (List.mem_singleton_self _), h⟩
      · exact ⟨y, List.mem_append_left _ hy, hye⟩
    · rintro ⟨y, hy, hye⟩
      rcases List.mem_append.1 hy with hy | hy
      · exact Or.inr ⟨y, hy, hye⟩
      · rw [List.mem_singleton] at hy
        subst hy
        exact Or.inl hye
  · intro y hy
    change y ∈ (st.O.push z).toList at hy
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hTr y hy
    · exact hz
  · change x₀ ∈ (st.O.push z).toList
    rw [Array.toList_push]
    exact List.mem_append_left _ hx₀

theorem bfs_step_spec (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → ℕ)
    (hinj : Function.Injective enc) (gens : List Γ) (x₀ : Ω) (Tr : List Ω)
    (hcl : ∀ g ∈ gens, ∀ x ∈ Tr, g • x ∈ Tr) (x : Ω) (i j : ℕ) (hj : j < gens.length)
    (st : BfsState Ω ℕ) (hI : OInv enc x₀ Tr st) (hx : x ∈ st.O.toList) :
    let st' : BfsState Ω ℕ :=
      if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
      else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
        st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩
    OInv enc x₀ Tr st' ∧ (∃ extra, st'.O.toList = st.O.toList ++ extra) ∧
      gens.getD j 1 • x ∈ st'.O.toList := by
  obtain ⟨-, hseen, hTr, -⟩ := id hI
  have hgen : gens.getD j 1 ∈ gens := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hzTr : gens.getD j 1 • x ∈ Tr := hcl _ hgen x (hTr x hx)
  simp only [hnrm]
  by_cases hc : st.seen.contains (enc (gens.getD j 1 • x)) = true
  · rw [if_pos hc]
    obtain ⟨y, hy, hyz⟩ := (hseen _).1 hc
    have hyeq : y = gens.getD j 1 • x := hinj hyz
    rw [hyeq] at hy
    exact ⟨id hI, ⟨[], by simp⟩, hy⟩
  · rw [if_neg hc]
    refine ⟨oinv_push enc x₀ Tr st (gens.getD j 1 • x) (st.par.push i) (st.lab.push j)
      (id hI) hzTr hc, ⟨[gens.getD j 1 • x], by simp⟩, ?_⟩
    change gens.getD j 1 • x ∈ (st.O.push (gens.getD j 1 • x)).toList
    rw [Array.toList_push]
    exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem fold_aux (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → ℕ)
    (hinj : Function.Injective enc) (gens : List Γ) (x₀ : Ω) (Tr : List Ω)
    (hcl : ∀ g ∈ gens, ∀ x ∈ Tr, g • x ∈ Tr) (x : Ω) (i : ℕ) (js : List ℕ) :
    (∀ j ∈ js, j < gens.length) → ∀ (st : BfsState Ω ℕ), OInv enc x₀ Tr st →
      x ∈ st.O.toList →
      OInv enc x₀ Tr (js.foldl (fun (st : BfsState Ω ℕ) j =>
        if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
        else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
          st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st) ∧
      (∃ extra, (js.foldl (fun (st : BfsState Ω ℕ) j =>
        if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
        else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
          st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st).O.toList = st.O.toList ++ extra) ∧
      ∀ j ∈ js, gens.getD j 1 • x ∈ (js.foldl (fun (st : BfsState Ω ℕ) j =>
        if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
        else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
          st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st).O.toList := by
  induction js with
  | nil =>
    intro _ st hI _
    exact ⟨hI, ⟨[], by simp⟩, by simp⟩
  | cons j js ih =>
    intro hjs st hI hx
    obtain ⟨h1, ⟨e1, he1⟩, h3⟩ := bfs_step_spec nrm hnrm enc hinj gens x₀ Tr hcl x i j
      (hjs j (by simp)) st hI hx
    obtain ⟨g1, ⟨e2, he2⟩, g3⟩ := ih (fun j' hj' => hjs j' (by simp [hj'])) _ h1
      (mem_of_append_eq he1 hx)
    rw [List.foldl_cons]
    refine ⟨g1, ⟨e1 ++ e2, ?_⟩, ?_⟩
    · exact he2.trans ((congrArg (fun l : List Ω => l ++ e2) he1).trans
        (List.append_assoc _ _ _))
    · intro j' hj'
      rcases List.mem_cons.1 hj' with rfl | hj''
      · exact mem_of_append_eq he2 h3
      · exact g3 j' hj''

theorem bfs_fold_spec (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → ℕ)
    (hinj : Function.Injective enc) (gens : List Γ) (x₀ : Ω) (Tr : List Ω)
    (hcl : ∀ g ∈ gens, ∀ x ∈ Tr, g • x ∈ Tr) (x : Ω) (i : ℕ) (js : List ℕ)
    (hjs : ∀ j ∈ js, j < gens.length) (st : BfsState Ω ℕ) (hI : OInv enc x₀ Tr st)
    (hx : x ∈ st.O.toList) :
    let st' : BfsState Ω ℕ := js.foldl (fun (st : BfsState Ω ℕ) j =>
      if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
      else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
        st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st
    OInv enc x₀ Tr st' ∧ (∃ extra, st'.O.toList = st.O.toList ++ extra) ∧
      ∀ j ∈ js, gens.getD j 1 • x ∈ st'.O.toList := by
  dsimp only
  exact fold_aux nrm hnrm enc hinj gens x₀ Tr hcl x i js hjs st hI hx

private theorem loop_zero (nrm : Ω → Ω) (enc : Ω → ℕ) (gens : List Γ) (i : ℕ)
    (st : BfsState Ω ℕ) : bfsLoop nrm enc gens 0 i st = st := by
  rw [bfsLoop]

private theorem loop_succ_lt (nrm : Ω → Ω) (enc : Ω → ℕ) (gens : List Γ) (f i : ℕ)
    (st : BfsState Ω ℕ) (hi : i < st.O.size) (x : Ω) (hx : st.O[i] = x) :
    bfsLoop nrm enc gens (f + 1) i st = bfsLoop nrm enc gens f (i + 1)
      ((List.range gens.length).foldl (fun (st : BfsState Ω ℕ) j =>
        if st.seen.contains (enc (nrm (gens.getD j 1 • x))) then st
        else ⟨st.O.push (nrm (gens.getD j 1 • x)), st.par.push i, st.lab.push j,
          st.seen.insert (enc (nrm (gens.getD j 1 • x)))⟩) st) := by
  subst hx
  rw [bfsLoop, dif_pos hi]

private theorem loop_succ_not_lt (nrm : Ω → Ω) (enc : Ω → ℕ) (gens : List Γ) (f i : ℕ)
    (st : BfsState Ω ℕ) (hi : ¬ i < st.O.size) : bfsLoop nrm enc gens (f + 1) i st = st := by
  rw [bfsLoop, dif_neg hi]

private theorem loopInv_next (gens : List Γ) (enc : Ω → ℕ) (x₀ : Ω) (Tr : List Ω) (i : ℕ)
    (st st1 : BfsState Ω ℕ) (hi : i < st.O.size)
    (hpr : ∀ x ∈ st.O.toList.take i, ∀ g ∈ gens, g • x ∈ st.O.toList)
    (hI1 : OInv enc x₀ Tr st1) (e : List Ω) (he : st1.O.toList = st.O.toList ++ e)
    (hall : ∀ g ∈ gens, g • st.O[i] ∈ st1.O.toList) :
    LoopInv gens enc x₀ Tr (i + 1) st1 := by
  have hlen : st.O.toList.length = st.O.size := by simp
  have hlt : i < st.O.toList.length := by omega
  have hle : i + 1 ≤ st.O.toList.length := by omega
  unfold LoopInv
  refine ⟨hI1, ?_, ?_⟩
  · rw [he, List.length_append]
    omega
  · intro y hy g hg
    rw [he, List.take_append_of_le_length hle, List.take_succ_eq_append_getElem hlt,
      List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy
    · rw [he]
      exact List.mem_append_left _ (hpr y hy g hg)
    · have hy' : y = st.O[i] := hy
      rw [hy']
      exact hall g hg

theorem bfsLoop_spec (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → ℕ)
    (hinj : Function.Injective enc) (gens : List Γ) (x₀ : Ω) (Tr : List Ω)
    (hcl : ∀ g ∈ gens, ∀ x ∈ Tr, g • x ∈ Tr) :
    ∀ (f i : ℕ) (st : BfsState Ω ℕ), LoopInv gens enc x₀ Tr i st →
      ∃ i', LoopInv gens enc x₀ Tr i' (bfsLoop nrm enc gens f i st) ∧
        (i' = i + f ∨ i' = (bfsLoop nrm enc gens f i st).O.toList.length) := by
  intro f
  induction f with
  | zero =>
    intro i st hL
    refine ⟨i, ?_, Or.inl (by simp)⟩
    rw [loop_zero]
    exact hL
  | succ f ih =>
    intro i st hL
    obtain ⟨hI, hle, hpr⟩ := hL
    by_cases hi : i < st.O.size
    · have hxmem : st.O[i] ∈ st.O.toList := Array.mem_toList_iff.2 (Array.getElem_mem hi)
      obtain ⟨hI1, ⟨e, he⟩, hall⟩ := bfs_fold_spec nrm hnrm enc hinj gens x₀ Tr hcl (st.O[i]) i
        (List.range gens.length) (fun j hj => List.mem_range.1 hj) st hI hxmem
      have hL1 := loopInv_next gens enc x₀ Tr i st _ hi hpr hI1 e he (by
        intro g hg
        obtain ⟨j, hj, hjg⟩ := List.mem_iff_getElem.1 hg
        have hgj : gens.getD j 1 = g := by rw [List.getD_eq_getElem _ _ hj, hjg]
        rw [← hgj]
        exact hall j (List.mem_range.2 hj))
      rw [loop_succ_lt nrm enc gens f i st hi (st.O[i]) rfl]
      obtain ⟨i', hL', hdis⟩ := ih (i + 1) _ hL1
      refine ⟨i', hL', ?_⟩
      rcases hdis with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    · rw [loop_succ_not_lt nrm enc gens f i st hi]
      have hlen : st.O.toList.length = st.O.size := by simp
      refine ⟨i, ?_, Or.inr (by omega)⟩
      unfold LoopInv
      exact ⟨hI, hle, hpr⟩

theorem bfsOrbit_spec (nrm : Ω → Ω) (hnrm : ∀ x, nrm x = x) (enc : Ω → ℕ)
    (hinj : Function.Injective enc) (gens : List Γ) (x₀ : Ω) (fuel : ℕ) (Tr : List Ω)
    (hnd : Tr.Nodup) (h0 : x₀ ∈ Tr) (hcl : ∀ g ∈ gens, ∀ x ∈ Tr, g • x ∈ Tr)
    (hreach : ∀ y ∈ Tr, ∀ S : Set Ω, x₀ ∈ S → (∀ g ∈ gens, ∀ x ∈ S, g • x ∈ S) → y ∈ S)
    (hf : Tr.length ≤ fuel) :
    ((bfsOrbit nrm enc gens x₀ fuel).1).Perm Tr := by
  have hI0 : LoopInv gens enc x₀ Tr 0
      (⟨#[x₀], #[0], #[0], (∅ : Std.HashSet ℕ).insert (enc x₀)⟩ : BfsState Ω ℕ) := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp
    · intro e
      show (Std.HashSet.contains ((∅ : Std.HashSet ℕ).insert (enc x₀)) e = true) ↔
        ∃ y ∈ [x₀], enc y = e
      rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
      constructor
      · intro h
        exact ⟨x₀, List.mem_singleton_self _, beq_iff_eq.1 h⟩
      · rintro ⟨y, hy, rfl⟩
        rw [List.mem_singleton.1 hy]
        exact beq_self_eq_true _
    · intro y hy
      simp at hy
      rw [hy]
      exact h0
    · simp
    · simp
    · intro x hx
      simp at hx
  obtain ⟨i', hI', hcase⟩ := bfsLoop_spec nrm hnrm enc hinj gens x₀ Tr hcl fuel 0 _ hI0
  have hbf : (bfsOrbit nrm enc gens x₀ fuel).1 =
      (bfsLoop nrm enc gens fuel 0
        (⟨#[x₀], #[0], #[0], (∅ : Std.HashSet ℕ).insert (enc x₀)⟩ : BfsState Ω ℕ)).O.toList := rfl
  rw [hbf]
  generalize (bfsLoop nrm enc gens fuel 0
    (⟨#[x₀], #[0], #[0], (∅ : Std.HashSet ℕ).insert (enc x₀)⟩ : BfsState Ω ℕ)) = st' at hI' hcase ⊢
  obtain ⟨⟨hOnd, -, hOTr, hx0⟩, hle, hproc⟩ := hI'
  rcases hcase with hcase | hcase
  · exact (List.subperm_of_subset hOnd hOTr).perm_of_length_le (by omega)
  · have hclO : ∀ g ∈ gens, ∀ x ∈ st'.O.toList, g • x ∈ st'.O.toList := by
      intro g hg x hx
      refine hproc x ?_ g hg
      rw [hcase, List.take_length]
      exact hx
    exact (List.perm_ext_iff_of_nodup hOnd hnd).2 fun a => ⟨fun ha => hOTr a ha,
      fun ha => hreach a ha _ hx0 hclO⟩

end Orbit

end CFSG.KC.LQT.PWSnd

end
