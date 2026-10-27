module

public import CFSG.CGT.Harada80.OmegaCodes
public import CFSG.CGT.Harada80.OmegaEightData

public section

namespace CFSG.CGT.Harada80.OmegaEight

open CFSG.CGT.Harada80
open CFSG.Quasithin.SteinbergCB.G2Two
open CFSG.Quasithin.SteinbergCB.I16

@[expose] def wordOf (s : String) : List (Fin 2) := s.toList.map fun c => if c = '1' then 1 else 0

@[expose] def words : List (List (Fin 2)) := wordStrings.map wordOf

@[expose] def sChain (i : ℕ) : List ℕ :=
  xyCodes.getD (2 * i) [] ++ xyCodes.getD (2 * i + 1) [] ++ (xyCodes.getD (2 * i) []).reverse ++
    (xyCodes.getD (2 * i + 1) []).reverse

@[expose] def nsCheck : Bool :=
  (List.range 256).all fun c =>
    decide (CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0) == nsCodes.contains c

@[expose] def genCheck : Bool :=
  (List.range 2).all fun i => (List.range 256).all fun x =>
    mApp (sCols.getD i []) x == reflChain 3 (sChain i) x

@[expose] def relCheck : Bool :=
  rels.all fun r => wordCols 8 sCols r == (List.range 8).map (2 ^ ·)

@[expose] def wordCheck : Bool :=
  nsCodes.length == words.length &&
    (nsCodes.zip words).all fun p =>
      let c := wordCols 8 sCols p.2
      (List.range 256).all fun x => mApp c x == reflCode 3 p.1 (reflCode 3 v0Code x)

@[expose] def foxCheck : Bool :=
  (List.range 256).all fun v₀ => (List.range 256).all fun v₁ =>
    !(rels.all fun r => foxCode sCols [v₀, v₁] r == 0) ||
      (List.range 256).any fun x =>
        v₀ == (mApp (sCols.getD 0 []) x ^^^ x) && v₁ == (mApp (sCols.getD 1 []) x ^^^ x)

theorem nsCheck_spec (h : nsCheck = true) {c : ℕ} (hc : c < 2 ^ 8) :
    CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0 ↔ c ∈ nsCodes := by
  have hc' : c < 256 := by
    norm_num at hc ⊢
    exact hc
  have h' := (List.all_eq_true.1 h) c (List.mem_range.2 hc')
  have h'' : decide (CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0) =
      nsCodes.contains c := by
    simpa using h'
  simpa [decide_eq_true_eq, List.contains_iff_mem] using (Bool.eq_iff_iff.mp h'')

theorem genCheck_spec (h : genCheck = true) (i : Fin 2) {x : ℕ} (hx : x < 2 ^ 8) :
    mApp (sCols.getD i []) x = reflChain 3 (sChain i) x := by
  have hx' : x < 256 := by
    norm_num at hx ⊢
    exact hx
  have hi := (List.all_eq_true.1 h) i (List.mem_range.2 i.isLt)
  have h' := (List.all_eq_true.1 hi) x (List.mem_range.2 hx')
  simpa using h'

theorem relCheck_spec (h : relCheck = true) {r : List (Fin 2)} (hr : r ∈ rels) :
    wordCols 8 sCols r = (List.range 8).map (2 ^ ·) := by
  have h' := (List.all_eq_true.1 h) r hr
  simpa using h'

theorem wordCheck_spec (h : wordCheck = true) {u : ℕ} (hu : u ∈ nsCodes) :
    ∃ w : List (Fin 2), ∀ x < 2 ^ 8,
      mApp (wordCols 8 sCols w) x = reflCode 3 u (reflCode 3 v0Code x) := by
  simp only [wordCheck, Bool.and_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  rw [beq_iff_eq] at hlen
  have hall' := List.all_eq_true.1 hall
  let i := nsCodes.idxOf u
  have hi : i < nsCodes.length := List.idxOf_lt_length_of_mem hu
  have hiw : i < words.length := by
    rw [← hlen]
    exact hi
  have hui : nsCodes[i]'hi = u := by
    have h1 := List.getElem?_idxOf (l := nsCodes) hu
    exact (List.getElem_eq_iff hi).2 h1
  let w := words[i]'hiw
  refine ⟨w, ?_⟩
  have hzip : (u, w) ∈ nsCodes.zip words := by
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · rw [List.length_zip, ← hlen, min_self]
      exact hi
    · rw [List.getElem_zip]
      simp [w, hui]
  have hxall := hall' (u, w) hzip
  intro x hx
  have hx' : x < 256 := by
    norm_num at hx ⊢
    exact hx
  have h' := (List.all_eq_true.1 hxall) x (List.mem_range.2 hx')
  simpa using h'

theorem foxCheck_spec (h : foxCheck = true) :
    ∀ v₀ < 2 ^ 8, ∀ v₁ < 2 ^ 8, (∀ r ∈ rels, foxCode sCols [v₀, v₁] r = 0) →
      ∃ x < 2 ^ 8, ∃ ε < 2, v₀ = mApp (sCols.getD 0 []) x ^^^ x ^^^ ε * [0, 0].getD 0 0 ∧
        v₁ = mApp (sCols.getD 1 []) x ^^^ x ^^^ ε * [0, 0].getD 1 0 := by
  intro v₀ hv₀ v₁ hv₁ hfox
  have hv₀' : v₀ < 256 := by
    norm_num at hv₀ ⊢
    exact hv₀
  have hv₁' : v₁ < 256 := by
    norm_num at hv₁ ⊢
    exact hv₁
  have hrel : (rels.all fun r => foxCode sCols [v₀, v₁] r == 0) = true := by
    apply List.all_eq_true.2
    intro r hr
    rw [hfox r hr]
    exact beq_self_eq_true 0
  have hany : (List.range 256).any (fun x =>
      v₀ == (mApp (sCols.getD 0 []) x ^^^ x) &&
        v₁ == (mApp (sCols.getD 1 []) x ^^^ x)) = true := by
    have h1 := (List.all_eq_true.1 h) v₀ (List.mem_range.2 hv₀')
    have h2 := (List.all_eq_true.1 h1) v₁ (List.mem_range.2 hv₁')
    simpa [hrel] using h2
  obtain ⟨x, hxmem, hxprop⟩ := List.any_eq_true.1 hany
  have hx : x < 2 ^ 8 := by
    have := List.mem_range.1 hxmem
    norm_num at this ⊢
    exact this
  simp only [Bool.and_eq_true, beq_iff_eq] at hxprop
  obtain ⟨h0, h1⟩ := hxprop
  refine ⟨x, hx, 0, by norm_num, ?_, ?_⟩
  · simpa using h0
  · simpa using h1

theorem sCols_lt : ∀ i : Fin 2, ∀ c ∈ sCols.getD i [], c < 2 ^ 8 := by
  decide

theorem sChain_mem (i : Fin 2) : ∀ c ∈ sChain i, c ∈ nsCodes := by
  fin_cases i <;> decide

theorem v0Code_mem : v0Code ∈ nsCodes := by
  decide

end CFSG.CGT.Harada80.OmegaEight
