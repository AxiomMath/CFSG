module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.GmatGen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.YGroups CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.MON5_7

@[expose] def tokNat (s : String) : ℕ := s.toNat?.getD 0

@[expose] def decodeLetters (perms : Array (Array ℕ)) : List String → List Native.Gen
  | "r" :: s :: a :: d :: rest =>
      .rho (tokNat s != 0, tokNat a, tokNat d) :: decodeLetters perms rest
  | "p" :: k :: rest => .perm perms[tokNat k]! :: decodeLetters perms rest
  | "x" :: rest => .xi :: decodeLetters perms rest
  | "t" :: rest => .tau :: decodeLetters perms rest
  | "g" :: a :: rest => .sign (tokNat a) :: decodeLetters perms rest
  | _ => []

@[expose] def tokens (line : String) : List String :=
  (line.splitOn " ").filter (· ≠ "")

@[expose] def decodeLine (acc : Array (Array ℕ) × Array (SLPStep × List Native.Gen))
    (line : String) : Array (Array ℕ) × Array (SLPStep × List Native.Gen) :=
  match tokens line with
  | "P" :: rest => (acc.1.push (rest.map tokNat).toArray, acc.2)
  | "E" :: i :: _ => (acc.1, acc.2.push (.gen (tokNat i), []))
  | "M" :: i :: j :: w => (acc.1, acc.2.push (.mul (tokNat i) (tokNat j), decodeLetters acc.1 w))
  | "I" :: i :: w => (acc.1, acc.2.push (.inv (tokNat i), decodeLetters acc.1 w))
  | _ => acc

@[expose] def decodeSteps (s : String) : Array (SLPStep × List Native.Gen) :=
  ((s.splitOn "\n").foldl decodeLine (#[], #[])).2

@[expose] def agreeC (c : Native.Ctx) (va vb vw : Native.DVec) (w₁ w₂ : List Native.Gen) : Bool :=
  w₁.all (fun g => g.validB) && w₂.all (fun g => g.validB) &&
    (Native.evalWordC c w₁ va).eqv (Native.evalWordC c w₂ va) &&
    (Native.evalWordC c w₁ vb).eqv (Native.evalWordC c w₂ vb) &&
    (Native.evalWordC c w₁ vw).eqv (Native.evalWordC c w₂ vw)

theorem agreeC_eq (w₁ w₂ : List Native.Gen) :
    agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) w₁ w₂ = agree w₁ w₂ := rfl

@[expose] def stepOKC (c : Native.Ctx) (va vb vw : Native.DVec) (gens : Array (List Native.Gen))
    (steps : Array (SLPStep × List Native.Gen)) (k : ℕ) : Bool :=
  match steps[k]!.1 with
  | .gen i => decide (i < gens.size)
  | .mul i j => decide (i < k) && decide (j < k) &&
      agreeC c va vb vw steps[k]!.2 (entryWord gens steps j ++ entryWord gens steps i)
  | .inv i => decide (i < k) && agreeC c va vb vw (steps[k]!.2 ++ entryWord gens steps i) []

theorem stepOKC_eq (gens : Array (List Native.Gen)) (steps : Array (SLPStep × List Native.Gen))
    (k : ℕ) : stepOKC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) gens steps k =
      stepOK gens steps k := by
  unfold stepOKC stepOK
  rcases steps[k]!.1 with i | ⟨i, j⟩ | i <;> simp only [agreeC_eq]

@[expose] def slpCheck (gens : Array (List Native.Gen)) (steps : Array (SLPStep × List Native.Gen))
    (lo hi : ℕ) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  (List.range' lo (hi - lo)).all (stepOKC c va vb vw gens steps)

theorem stepsOK_of_slpCheck {gens : Array (List Native.Gen)}
    {steps : Array (SLPStep × List Native.Gen)} {lo hi : ℕ} (h : slpCheck gens steps lo hi = true) :
    stepsOK gens steps lo hi = true := by
  have e : slpCheck gens steps lo hi = stepsOK gens steps lo hi := by
    unfold slpCheck stepsOK
    exact congrArg (List.range' lo (hi - lo)).all (funext (stepOKC_eq gens steps))
  rw [← e]
  exact h

theorem stepsOK_append {gens : Array (List Native.Gen)} {steps : Array (SLPStep × List Native.Gen)}
    {lo mid hi : ℕ} (h₁ : stepsOK gens steps lo mid = true)
    (h₂ : stepsOK gens steps mid hi = true) : stepsOK gens steps lo hi = true := by
  unfold stepsOK at *
  rw [List.all_eq_true] at *
  intro k hk
  rw [List.mem_range'_1] at hk
  by_cases hkm : k < mid
  · exact h₁ k (List.mem_range'_1.2 ⟨hk.1, by omega⟩)
  · exact h₂ k (List.mem_range'_1.2 ⟨by omega, by omega⟩)

@[expose] def targetsCheck (gens : Array (List Native.Gen))
    (steps : Array (SLPStep × List Native.Gen)) (n : ℕ) (idx : List ℕ) : Bool :=
  let c := Native.mkCtx ()
  let va := aV ()
  let vb := bV ()
  let vw := wV ()
  decide (steps.size = n) && (List.range 11).all fun j =>
    decide (idx[j]! < n) && agreeC c va vb vw (entryWord gens steps idx[j]!) (L j)

theorem of_targetsCheck {gens : Array (List Native.Gen)}
    {steps : Array (SLPStep × List Native.Gen)} {n : ℕ} {idx : List ℕ}
    (h : targetsCheck gens steps n idx = true) :
    steps.size = n ∧ ∀ j < 11, idx[j]! < n ∧ agree (entryWord gens steps idx[j]!) (L j) = true := by
  unfold targetsCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨h.1, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 j hj
  exact ⟨h1, by rw [← agreeC_eq]; exact h2⟩

theorem closure_eq_top_of_slp
    {gens : Array (List Native.Gen)} {steps : Array (SLPStep × List Native.Gen)} {n : ℕ}
    {idx : List ℕ} (hs : stepsOK gens steps 0 n = true) (ht : targetsCheck gens steps n idx = true) :
    Subgroup.closure (Set.range fun i : Fin gens.size => gw gens[i]) = ⊤ := by
  obtain ⟨hn, hidx⟩ := of_targetsCheck ht
  have hall : ∀ k < steps.size, stepOK gens steps k = true := fun k hk =>
    stepOK_of_stepsOK hs (Nat.zero_le k) (hn ▸ hk)
  rw [eq_top_iff, ← closure_range_gGen_eq_top, Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  obtain ⟨hlt, hag⟩ := hidx (wIdx g) (wIdx_lt g)
  have hmem := mem_closure_of_stepOK hall idx[wIdx g]! (hn ▸ hlt)
  rw [agree_sound hag] at hmem
  exact hmem

theorem closure_eq_top_of_mem {Γ : Set Gmat} {gens : Array (List Native.Gen)}
    (h : Subgroup.closure (Set.range fun i : Fin gens.size => gw gens[i]) = ⊤)
    (hΓ : ∀ i : Fin gens.size, gw gens[i] ∈ Γ) : Subgroup.closure Γ = ⊤ := by
  rw [eq_top_iff, ← h]
  exact Subgroup.closure_mono (by rintro _ ⟨i, rfl⟩; exact hΓ i)

end CFSG.AGLEmbedding.Norton
