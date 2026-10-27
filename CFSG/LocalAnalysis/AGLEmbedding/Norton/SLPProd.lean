module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.SLPDecode

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.YGroups CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.MON5_7

inductive ProdStep where
  | gen (i : ℕ)
  | prod (l : List ℕ)
  | inv (l : List ℕ)
  deriving Inhabited

@[expose] def prodWord (gens : Array (List Native.Gen)) (steps : Array (ProdStep × List Native.Gen))
    (k : ℕ) : List Native.Gen :=
  match steps[k]!.1 with
  | .gen i => gens[i]!
  | _ => steps[k]!.2

@[expose] def prodConcat (gens : Array (List Native.Gen))
    (steps : Array (ProdStep × List Native.Gen)) (l : List ℕ) : List Native.Gen :=
  l.flatMap (prodWord gens steps)

@[expose] def prodStepOK (gens : Array (List Native.Gen))
    (steps : Array (ProdStep × List Native.Gen)) (k : ℕ) : Bool :=
  match steps[k]!.1 with
  | .gen i => decide (i < gens.size)
  | .prod l => l.all (fun i => decide (i < k)) && agree steps[k]!.2 (prodConcat gens steps l)
  | .inv l => l.all (fun i => decide (i < k)) &&
      agree (steps[k]!.2 ++ prodConcat gens steps l) []

@[expose] def prodStepsOK (gens : Array (List Native.Gen))
    (steps : Array (ProdStep × List Native.Gen)) (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all (prodStepOK gens steps)

theorem prodStepOK_of_prodStepsOK {gens : Array (List Native.Gen)}
    {steps : Array (ProdStep × List Native.Gen)} {lo hi k : ℕ}
    (h : prodStepsOK gens steps lo hi = true) (hlo : lo ≤ k) (hhi : k < hi) :
    prodStepOK gens steps k = true :=
  List.all_eq_true.1 h k (List.mem_range'_1.2 ⟨hlo, by omega⟩)

theorem prodStepsOK_append {gens : Array (List Native.Gen)}
    {steps : Array (ProdStep × List Native.Gen)} {lo mid hi : ℕ}
    (h₁ : prodStepsOK gens steps lo mid = true) (h₂ : prodStepsOK gens steps mid hi = true) :
    prodStepsOK gens steps lo hi = true := by
  unfold prodStepsOK at *
  rw [List.all_eq_true] at *
  intro k hk
  rw [List.mem_range'_1] at hk
  by_cases hkm : k < mid
  · exact h₁ k (List.mem_range'_1.2 ⟨hk.1, by omega⟩)
  · exact h₂ k (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem gw_flatMap_mem {H : Subgroup Gmat} {f : ℕ → List Native.Gen} :
    ∀ l : List ℕ, (∀ i ∈ l, gw (f i) ∈ H) → gw (l.flatMap f) ∈ H
  | [], _ => by
      rw [List.flatMap_nil, gw_nil]
      exact H.one_mem
  | i :: l, h => by
      rw [List.flatMap_cons, gw_append]
      exact H.mul_mem (gw_flatMap_mem l fun j hj => h j (List.mem_cons_of_mem _ hj))
        (h i List.mem_cons_self)

theorem mem_closure_of_prodStepOK
    {gens : Array (List Native.Gen)} {steps : Array (ProdStep × List Native.Gen)}
    (h : ∀ k < steps.size, prodStepOK gens steps k = true) :
    ∀ k < steps.size, gw (prodWord gens steps k) ∈
      Subgroup.closure (Set.range fun i : Fin gens.size => gw gens[i]) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hs := h k hk
    unfold prodStepOK at hs
    unfold prodWord
    rcases hstep : steps[k]!.1 with i | l | l
    · rw [hstep] at hs
      have hi : i < gens.size := of_decide_eq_true hs
      refine Subgroup.subset_closure ⟨⟨i, hi⟩, ?_⟩
      show gw gens[i] = gw gens[i]!
      rw [getElem!_pos gens i hi]
    · rw [hstep] at hs
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
      obtain ⟨hl, hag⟩ := hs
      rw [agree_sound hag]
      exact gw_flatMap_mem l fun i hi => ih i (hl i hi) (by have := hl i hi; omega)
    · rw [hstep] at hs
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
      obtain ⟨hl, hag⟩ := hs
      have e := agree_sound hag
      rw [gw_append, gw_nil] at e
      rw [eq_inv_of_mul_eq_one_right e]
      exact inv_mem (gw_flatMap_mem l fun i hi => ih i (hl i hi) (by have := hl i hi; omega))

@[expose] def splitBar : List String → List ℕ × List String
  | [] => ([], [])
  | "|" :: w => ([], w)
  | t :: rest => ((splitBar rest).1.cons (tokNat t), (splitBar rest).2)

@[expose] def decodeProdLine (acc : Array (Array ℕ) × Array (ProdStep × List Native.Gen))
    (line : String) : Array (Array ℕ) × Array (ProdStep × List Native.Gen) :=
  match tokens line with
  | "P" :: rest => (acc.1.push (rest.map tokNat).toArray, acc.2)
  | "E" :: i :: _ => (acc.1, acc.2.push (.gen (tokNat i), []))
  | "M" :: rest => (acc.1, acc.2.push (.prod (splitBar rest).1,
      decodeLetters acc.1 (splitBar rest).2))
  | "I" :: rest => (acc.1, acc.2.push (.inv (splitBar rest).1,
      decodeLetters acc.1 (splitBar rest).2))
  | _ => acc

@[expose] def decodeProdSteps (s : String) : Array (ProdStep × List Native.Gen) :=
  ((s.splitOn "\n").foldl decodeProdLine (#[], #[])).2

@[expose] def prodStepOKC (c : Native.Ctx) (va vb vw : Native.DVec)
    (gens : Array (List Native.Gen)) (steps : Array (ProdStep × List Native.Gen)) (k : ℕ) : Bool :=
  match steps[k]!.1 with
  | .gen i => decide (i < gens.size)
  | .prod l => l.all (fun i => decide (i < k)) &&
      agreeC c va vb vw steps[k]!.2 (prodConcat gens steps l)
  | .inv l => l.all (fun i => decide (i < k)) &&
      agreeC c va vb vw (steps[k]!.2 ++ prodConcat gens steps l) []

theorem prodStepOKC_eq (gens : Array (List Native.Gen))
    (steps : Array (ProdStep × List Native.Gen)) (k : ℕ) :
    prodStepOKC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) gens steps k =
      prodStepOK gens steps k := by
  unfold prodStepOKC prodStepOK
  rcases steps[k]!.1 with i | l | l <;> simp only [agreeC_eq]

@[expose] def prodCheck (gens : Array (List Native.Gen))
    (steps : Array (ProdStep × List Native.Gen)) (lo hi : ℕ) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  (List.range' lo (hi - lo)).all (prodStepOKC c va vb vw gens steps)

theorem prodStepsOK_of_prodCheck {gens : Array (List Native.Gen)}
    {steps : Array (ProdStep × List Native.Gen)} {lo hi : ℕ}
    (h : prodCheck gens steps lo hi = true) : prodStepsOK gens steps lo hi = true := by
  have e : prodCheck gens steps lo hi = prodStepsOK gens steps lo hi := by
    unfold prodCheck prodStepsOK
    exact congrArg (List.range' lo (hi - lo)).all (funext (prodStepOKC_eq gens steps))
  rw [← e]
  exact h

@[expose] def prodTargetsCheck (gens : Array (List Native.Gen))
    (steps : Array (ProdStep × List Native.Gen)) (n : ℕ) (idx : List ℕ) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  decide (steps.size = n) && (List.range 11).all fun j =>
    decide (idx[j]! < n) && agreeC c va vb vw (prodWord gens steps idx[j]!) (L j)

theorem of_prodTargetsCheck {gens : Array (List Native.Gen)}
    {steps : Array (ProdStep × List Native.Gen)} {n : ℕ} {idx : List ℕ}
    (h : prodTargetsCheck gens steps n idx = true) :
    steps.size = n ∧ ∀ j < 11, idx[j]! < n ∧ agree (prodWord gens steps idx[j]!) (L j) = true := by
  unfold prodTargetsCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨h.1, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 j hj
  exact ⟨h1, by rw [← agreeC_eq]; exact h2⟩

theorem closure_eq_top_of_prod
    {gens : Array (List Native.Gen)} {steps : Array (ProdStep × List Native.Gen)} {n : ℕ}
    {idx : List ℕ} (hs : prodStepsOK gens steps 0 n = true)
    (ht : prodTargetsCheck gens steps n idx = true) :
    Subgroup.closure (Set.range fun i : Fin gens.size => gw gens[i]) = ⊤ := by
  obtain ⟨hn, hidx⟩ := of_prodTargetsCheck ht
  have hall : ∀ k < steps.size, prodStepOK gens steps k = true := fun k hk =>
    prodStepOK_of_prodStepsOK hs (Nat.zero_le k) (hn ▸ hk)
  rw [eq_top_iff, ← closure_range_gGen_eq_top, Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  obtain ⟨hlt, hag⟩ := hidx (wIdx g) (wIdx_lt g)
  have hmem := mem_closure_of_prodStepOK hall idx[wIdx g]! (hn ▸ hlt)
  rw [agree_sound hag] at hmem
  exact hmem

end CFSG.AGLEmbedding.Norton
