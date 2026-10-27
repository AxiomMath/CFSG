module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem elemW_nil : elemW [] = 1 := by
  simp only [elemW, TwoHS.wordVal, List.map_nil, List.prod_nil]

theorem elemW_flatten_replicate (e : ℕ) (w : List ℕ) :
    elemW (List.replicate e w).flatten = elemW w ^ e := by
  induction e with
  | zero => simp [elemW_nil]
  | succ e ih => rw [List.replicate_succ, List.flatten_cons, elemW_append, ih, pow_succ']

theorem elemW_getD_mem (gs : List (List ℕ)) (i : ℕ) :
    elemW (gs.getD i []) ∈ closure (elemW '' {w | w ∈ gs}) := by
  by_cases h : i < gs.length
  · rw [List.getD_eq_getElem _ _ h]
    exact subset_closure ⟨_, List.getElem_mem h, rfl⟩
  · rw [List.getD_eq_default _ _ (by omega), elemW_nil]
    exact one_mem _

theorem elemW_specWord_mem (gs : List (List ℕ)) (spec : List (ℕ × ℕ)) :
    elemW (specWord gs spec) ∈ closure (elemW '' {w | w ∈ gs}) := by
  induction spec with
  | nil => simp [specWord, elemW_nil]
  | cons p ps ih =>
    have e : specWord gs (p :: ps) =
        (List.replicate p.2 (gs.getD (p.1 - 1) [])).flatten ++ specWord gs ps := by
      simp [specWord, List.flatMap_cons]
    rw [e, elemW_append, elemW_flatten_replicate]
    exact mul_mem (pow_mem (elemW_getD_mem gs (p.1 - 1)) _) ih

theorem closure_specWords_le (gs : List (List ℕ)) (specs : List (List (ℕ × ℕ))) :
    closure (elemW '' {w | w ∈ specs.map (specWord gs)}) ≤ closure (elemW '' {w | w ∈ gs}) := by
  rw [closure_le]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨spec, -, rfl⟩ := List.mem_map.1 hw
  exact elemW_specWord_mem gs spec

variable {L Z Q : Array Table} {S A B : Set (Equiv.Perm (Fin 1408))}

theorem centInOK_iff (hg : gensOK = true) (ws : List (List ℕ)) (hw : ws.all wordOK = true)
    {M : Array Table} {T : Set (Equiv.Perm (Fin 1408))} (hL : IsEnumSet 1408 L S)
    (hM : IsEnumSet 1408 M T) :
    centInOK L (ws.map tabW) M = true ↔
      ∀ g ∈ S, (∀ w ∈ ws, g * elemW w = elemW w * g) → g ∈ T := by
  refine hL.forall_iff _ (fun g => (∀ w ∈ ws, g * elemW w = elemW w * g) → g ∈ T) ?_
  intro x g hx
  have hcomm : (ws.map tabW).all (fun t => commTT 1408 x t) = true ↔
      ∀ w ∈ ws, g * elemW w = elemW w * g := by
    rw [List.all_eq_true]
    constructor
    · intro h w hwm
      exact (commTT_iff hx (rep_elemW_of_gensOK hg (List.all_eq_true.1 hw w hwm))).1
        (h _ (List.mem_map_of_mem hwm))
    · intro h t ht
      obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 ht
      exact (commTT_iff hx (rep_elemW_of_gensOK hg (List.all_eq_true.1 hw w hwm))).2 (h w hwm)
  have hmem := hM.memT_iff hx
  simp only [centInOK, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h hc
    rcases h with h | h
    · exact absurd (hcomm.2 hc) (by simp [h])
    · exact hmem.1 h
  · intro H
    by_cases hc : (ws.map tabW).all (fun t => commTT 1408 x t) = true
    · exact Or.inr (hmem.2 (H (hcomm.1 hc)))
    · exact Or.inl (by simpa using hc)

theorem centInPairOK_iff (hg : gensOK = true) (ws : List (List ℕ)) (hw : ws.all wordOK = true)
    {tc : Table} {c : Equiv.Perm (Fin 1408)} (hc : Rep 1408 tc c) (hL : IsEnumSet 1408 L S) :
    centInPairOK L (ws.map tabW) (idT 1408) tc = true ↔
      ∀ g ∈ S, (∀ w ∈ ws, g * elemW w = elemW w * g) → g = 1 ∨ g = c := by
  refine hL.forall_iff _ (fun g => (∀ w ∈ ws, g * elemW w = elemW w * g) → g = 1 ∨ g = c) ?_
  intro x g hx
  have hcomm : (ws.map tabW).all (fun t => commTT 1408 x t) = true ↔
      ∀ w ∈ ws, g * elemW w = elemW w * g := by
    rw [List.all_eq_true]
    constructor
    · intro h w hwm
      exact (commTT_iff hx (rep_elemW_of_gensOK hg (List.all_eq_true.1 hw w hwm))).1
        (h _ (List.mem_map_of_mem hwm))
    · intro h t ht
      obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 ht
      exact (commTT_iff hx (rep_elemW_of_gensOK hg (List.all_eq_true.1 hw w hwm))).2 (h w hwm)
  have h1 := tblEq_iff_eq hx (Rep.idT (by norm_num : 1408 < 2 ^ 32))
  have h2 := tblEq_iff_eq hx hc
  simp only [centInPairOK, Bool.or_eq_true, Bool.not_eq_true', h1, h2]
  constructor
  · intro h hcm
    rcases h with (h | h) | h
    · exact absurd (hcomm.2 hcm) (by simp [h])
    · exact Or.inl h
    · exact Or.inr h
  · intro H
    by_cases hcm : (ws.map tabW).all (fun t => commTT 1408 x t) = true
    · rcases H (hcomm.1 hcm) with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · exact Or.inl (Or.inl (by simpa using hcm))

theorem commListsOK_iff (hg : gensOK = true) (ws vs : List (List ℕ)) (hw : ws.all wordOK = true)
    (hv : vs.all wordOK = true) :
    commListsOK (ws.map tabW) (vs.map tabW) = true ↔
      ∀ w ∈ ws, ∀ v ∈ vs, elemW w * elemW v = elemW v * elemW w := by
  simp only [commListsOK, List.all_eq_true, List.mem_map]
  constructor
  · intro h w hwm v hvm
    exact (commTT_iff (rep_elemW_of_gensOK hg (List.all_eq_true.1 hw w hwm))
      (rep_elemW_of_gensOK hg (List.all_eq_true.1 hv v hvm))).1
      (h _ ⟨w, hwm, rfl⟩ _ ⟨v, hvm, rfl⟩)
  · rintro h _ ⟨w, hwm, rfl⟩ _ ⟨v, hvm, rfl⟩
    exact (commTT_iff (rep_elemW_of_gensOK hg (List.all_eq_true.1 hw w hwm))
      (rep_elemW_of_gensOK hg (List.all_eq_true.1 hv v hvm))).2 (h w hwm v hvm)

theorem prodCoverOK_iff (hL : IsEnumSet 1408 L S) (hZ : IsEnumSet 1408 Z A)
    (hQ : IsEnumSet 1408 Q B) :
    prodCoverOK L Z Q = true ↔ ∀ g ∈ S, ∃ z ∈ A, ∃ q ∈ B, z * q = g := by
  refine hL.forall_iff _ (fun g => ∃ z ∈ A, ∃ q ∈ B, z * q = g) ?_
  intro x g hx
  refine hZ.exists_iff (fun z => Q.any fun q => tblEq 1408 (compT 1408 z q) x)
    (fun z' => ∃ q ∈ B, z' * q = g) ?_
  intro z z' hz
  exact hQ.exists_iff (fun q => tblEq 1408 (compT 1408 z q) x) (fun q' => z' * q' = g)
    (fun q q' hq => tblEq_iff_eq (Rep.compT hz hq) hx)

theorem commInOK_iff {tc : Table} {c : Equiv.Perm (Fin 1408)} (hc : Rep 1408 tc c)
    (hL : IsEnumSet 1408 L S) :
    commInOK L tc = true ↔ ∀ s ∈ S, ∀ t ∈ S, s * t = t * s ∨ s * t = c * (t * s) := by
  refine hL.forall_iff _ (fun s => ∀ t ∈ S, s * t = t * s ∨ s * t = c * (t * s)) ?_
  intro x s hx
  refine hL.forall_iff _ (fun t => s * t = t * s ∨ s * t = c * (t * s)) ?_
  intro y t hy
  simp only [Bool.or_eq_true]
  rw [tblEq_iff_eq (Rep.compT hx hy) (Rep.compT hy hx),
    tblEq_iff_eq (Rep.compT hx hy) (Rep.compT hc (Rep.compT hy hx))]

theorem sqInPairOK_iff {tc : Table} {c : Equiv.Perm (Fin 1408)} (hc : Rep 1408 tc c)
    (hL : IsEnumSet 1408 L S) :
    sqInPairOK L (idT 1408) tc = true ↔ ∀ s ∈ S, s * s = 1 ∨ s * s = c := by
  refine hL.forall_iff _ (fun s => s * s = 1 ∨ s * s = c) ?_
  intro x s hx
  simp only [Bool.or_eq_true]
  rw [tblEq_iff_eq (Rep.compT hx hx) (Rep.idT (by norm_num : 1408 < 2 ^ 32)),
    tblEq_iff_eq (Rep.compT hx hx) hc]

end CFSG.EvenSporadicStandard.HNRecog
