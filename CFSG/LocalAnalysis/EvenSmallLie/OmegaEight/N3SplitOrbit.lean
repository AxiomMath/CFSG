module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitNative
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitConj

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def bigFix (k : ℕ) : Bool := decide (8 ≤ (kerBasis k).length) && fixLB k (kerBasis k)

theorem card_fixM_of_bigFix {k : ℕ} (h : bigFix k = true) :
    2 ^ 8 ≤ Nat.card (fixM (toMatK k)) := by
  simp only [bigFix, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (Nat.pow_le_pow_right (by norm_num) h.1).trans (fixLB_sound h.2)

@[expose] def findK (A : Array ℕ) (y : ℕ) : Option ℕ :=
  match bsearchAux A y 64 0 A.size with
  | some p => if p < A.size ∧ A.getD p 0 = y then some p else none
  | none => none

theorem findK_spec {A : Array ℕ} {y p : ℕ} (h : findK A y = some p) :
    p < A.size ∧ A.getD p 0 = y := by
  unfold findK at h
  split at h
  · split_ifs at h with h1
    · cases h
      exact h1
  · cases h

@[expose] def visitK (A : Array ℕ) (x : ℕ) (st : Array Bool × List ℕ) (g : ℕ × ℕ) :
    Array Bool × List ℕ :=
  match findK A (mulK (mulK g.1 x) g.2) with
  | some p => if st.1.getD p true then st
      else (st.1.setIfInBounds p true, mulK (mulK g.1 x) g.2 :: st.2)
  | none => st

@[expose] def visitAll (A : Array ℕ) (gs : Array (ℕ × ℕ)) (x : ℕ) (st : Array Bool × List ℕ) :
    Array Bool × List ℕ :=
  (List.range gs.size).foldl (fun st j => visitK A x st (genK gs j)) st

@[expose] def orbLoop (A : Array ℕ) (gs : Array (ℕ × ℕ)) : ℕ → Array Bool × List ℕ → Array Bool
  | 0, st => st.1
  | _ + 1, (vis, []) => vis
  | n + 1, (vis, x :: xs) => orbLoop A gs n (visitAll A gs x (vis, xs))

@[expose] def orbStart (A : Array ℕ) (gs : Array (ℕ × ℕ)) (vis : Array Bool) (r : ℕ) :
    Array Bool :=
  match findK A r with
  | some p => orbLoop A gs (A.size + 1) (vis.setIfInBounds p true, [r])
  | none => vis

@[expose] def orbAll (A : Array ℕ) (gs : Array (ℕ × ℕ)) (reps : List ℕ) : Array Bool :=
  reps.foldl (orbStart A gs) (Array.replicate A.size false)

section Orbits

variable {A : Array ℕ} {gs : Array (ℕ × ℕ)} (P : ℕ → Prop)

@[expose] def MarkInv (A : Array ℕ) (vis : Array Bool) : Prop :=
  ∀ q, vis.getD q false = true → P (A.getD q 0)

theorem getD_setIfInBounds_true {vis : Array Bool} {p q : ℕ}
    (h : (vis.setIfInBounds p true).getD q false = true) : q = p ∨ vis.getD q false = true := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at h
  by_cases hpq : p = q
  · exact Or.inl hpq.symm
  · simp only [hpq, ↓reduceIte] at h
    rw [← Array.getD_eq_getD_getElem?] at h
    exact Or.inr h

theorem markInv_set {vis : Array Bool} (hv : MarkInv P A vis) {p : ℕ} (hp : P (A.getD p 0)) :
    MarkInv P A (vis.setIfInBounds p true) := by
  intro q hq
  rcases getD_setIfInBounds_true hq with rfl | hq
  · exact hp
  · exact hv q hq

variable {P}

theorem visitK_inv (hP : ∀ x, P x → ∀ j, P (mulK (mulK (genK gs j).1 x) (genK gs j).2))
    {x : ℕ} (hx : P x) (j : ℕ) {st : Array Bool × List ℕ}
    (hst : MarkInv P A st.1 ∧ ∀ y ∈ st.2, P y) :
    MarkInv P A (visitK A x st (genK gs j)).1 ∧ ∀ y ∈ (visitK A x st (genK gs j)).2, P y := by
  have hy := hP x hx j
  unfold visitK
  split
  · rename_i p hp
    have hpA := (findK_spec hp).2
    split_ifs
    · exact hst
    · refine ⟨markInv_set P hst.1 (by rw [hpA]; exact hy), ?_⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hy
      · exact hst.2 z hz
  · exact hst

theorem visitAll_inv (hP : ∀ x, P x → ∀ j, P (mulK (mulK (genK gs j).1 x) (genK gs j).2))
    {x : ℕ} (hx : P x) :
    ∀ (js : List ℕ) (st : Array Bool × List ℕ), (MarkInv P A st.1 ∧ ∀ y ∈ st.2, P y) →
      MarkInv P A (js.foldl (fun st j => visitK A x st (genK gs j)) st).1 ∧
        ∀ y ∈ (js.foldl (fun st j => visitK A x st (genK gs j)) st).2, P y
  | [], _, hst => hst
  | j :: js, _, hst => visitAll_inv hP hx js _ (visitK_inv hP hx j hst)

theorem orbLoop_inv (hP : ∀ x, P x → ∀ j, P (mulK (mulK (genK gs j).1 x) (genK gs j).2)) :
    ∀ (n : ℕ) (st : Array Bool × List ℕ), (MarkInv P A st.1 ∧ ∀ y ∈ st.2, P y) →
      MarkInv P A (orbLoop A gs n st)
  | 0, st, hst => hst.1
  | _ + 1, (vis, []), hst => hst.1
  | n + 1, (vis, x :: xs), hst => by
    refine orbLoop_inv hP n _ (visitAll_inv hP (hst.2 x List.mem_cons_self) _ (vis, xs)
      ⟨hst.1, fun y hy => hst.2 y (List.mem_cons_of_mem _ hy)⟩)

theorem orbAll_inv (hP : ∀ x, P x → ∀ j, P (mulK (mulK (genK gs j).1 x) (genK gs j).2))
    {reps : List ℕ} (hr : ∀ r ∈ reps, ∀ p < A.size, A.getD p 0 = r → P r) :
    MarkInv P A (orbAll A gs reps) := by
  have key : ∀ (rs : List ℕ) (vis : Array Bool), (∀ r ∈ rs, ∀ p < A.size, A.getD p 0 = r → P r) →
      MarkInv P A vis → MarkInv P A (rs.foldl (orbStart A gs) vis) := by
    intro rs
    induction rs with
    | nil => exact fun vis _ hv => hv
    | cons r rs ih =>
      intro vis hrs hv
      refine ih _ (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr')) ?_
      unfold orbStart
      split
      · rename_i p hp
        obtain ⟨hpA, hpr⟩ := findK_spec hp
        have hPr := hrs r List.mem_cons_self p hpA hpr
        refine orbLoop_inv hP _ _ ⟨markInv_set P hv (by rw [hpr]; exact hPr), ?_⟩
        intro y hy
        rw [List.mem_singleton] at hy
        rw [hy]
        exact hPr
      · exact hv
  refine key reps _ hr fun q hq => ?_
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hq
  split_ifs at hq <;> simp at hq

end Orbits

@[expose] def classCert (E : Enum) (gs : Array (ℕ × ℕ)) (reps good : List ℕ) : Bool :=
  let vis := orbAll E.keys gs reps
  ((List.range E.keys.size).all fun i =>
    mulK (E.keys.getD i 0) (E.keys.getD i 0) != idK || E.keys.getD i 0 == idK ||
      vis.getD i false || bigFix (E.keys.getD i 0)) &&
    reps.all fun r => memK E.keys r && (!(candB E r) || good.contains r)

variable {gs : Array (ℕ × ℕ)} {E : Enum}

@[expose] def IsConjKey (gs : Array (ℕ × ℕ)) (reps : List ℕ) (k : ℕ) : Prop :=
  ∃ r ∈ reps, ∃ X : GL12, Rep k X ∧ ∃ y ∈ grpOf gs, ∀ rG : GL12, Rep r rG → X = y * rG * y⁻¹

theorem isConjKey_conj (hg : gensOK gs = true) {reps : List ℕ} {x : ℕ}
    (hx : IsConjKey gs reps x) (j : ℕ) :
    IsConjKey gs reps (mulK (mulK (genK gs j).1 x) (genK gs j).2) := by
  obtain ⟨r, hr, X, hX, y, hy, hXy⟩ := hx
  refine ⟨r, hr, genG gs j * X * (genG gs j)⁻¹,
    ((rep_genG hg j).mul hX).mul (rep_genG_inv hg j), genG gs j * y,
    mul_mem (genG_mem hg j) hy, fun rG hrG => ?_⟩
  rw [hXy rG hrG]
  group

theorem cand_of_classCert (hE : enumOK gs E = true) {reps good : List ℕ}
    (h : classCert E gs reps good = true) {s : GL12} (hs : s ∈ grpOf gs)
    (hc : IsCand (grpOf gs) s) :
    ∃ r ∈ good, ∃ rG : GL12, Rep r rG ∧ rG ∈ grpOf gs ∧ ∃ y ∈ grpOf gs, s = y * rG * y⁻¹ := by
  have hg := (Enum.of_enumOK hE).1
  simp only [classCert, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true', List.contains_iff_mem] at h
  obtain ⟨h1, h2⟩ := h
  have hstep : ∀ x, IsConjKey gs reps x → ∀ j,
      IsConjKey gs reps (mulK (mulK (genK gs j).1 x) (genK gs j).2) :=
    fun x hx j => isConjKey_conj hg hx j
  have hstart : ∀ r ∈ reps, ∀ p < E.keys.size, E.keys.getD p 0 = r → IsConjKey gs reps r := by
    intro r hr p hp hpr
    obtain ⟨X, -, hrX⟩ := Enum.exists_mem hE p hp
    rw [hpr] at hrX
    refine ⟨r, hr, X, hrX, 1, one_mem _, fun rG hrG => ?_⟩
    rw [hrX.unique hrG]
    group
  have hinv : MarkInv (IsConjKey gs reps) E.keys (orbAll E.keys gs reps) :=
    orbAll_inv (P := IsConjKey gs reps) (A := E.keys) (gs := gs) hstep hstart
  obtain ⟨i, hi, hri⟩ := Enum.exists_key hE hs
  obtain ⟨hs2, hs1, hfix, -⟩ := id hc
  rcases h1 i hi with ((h3 | h3) | h3) | h3
  · exact absurd ((hri.mul hri).key_unique (by rw [hs2]; exact rep_one) (mulK_lt _ _) idK_lt) h3
  · rw [h3] at hri
    exact absurd (hri.unique rep_one) hs1
  · obtain ⟨r, hr, X, hX, y, hy, hXy⟩ := hinv i h3
    have hXs : X = s := hX.unique hri
    obtain ⟨hmem, hgood⟩ := h2 r hr
    obtain ⟨rG, hrGS, hrG⟩ := Enum.rep_of_memK hE hmem
    have hsy : s = y * rG * y⁻¹ := hXs ▸ hXy rG hrG
    have hcr : IsCand (grpOf gs) rG := by
      have := (isCand_conj (S := grpOf gs) (le_normalizer (inv_mem hy)) (s := s)).2 hc
      rwa [hsy, show y⁻¹ * (y * rG * y⁻¹) * y⁻¹⁻¹ = rG by group] at this
    have hcb := candB_of_isCand hE hrG hcr
    rcases hgood with hgood | hgood
    · exact absurd hcb (by rw [hgood]; decide)
    · exact ⟨r, hgood, rG, hrG, hrGS, y, hy, hsy⟩
  · have := card_fixM_of_bigFix h3
    rw [hri] at this
    exact absurd (this.trans hfix) (by norm_num)

theorem conj_mem_of_relIndex_two {M S : Subgroup GL12} (hMS : M ≤ S) (h : M.relIndex S = 2)
    {y m : GL12} (hy : y ∈ S) (hm : m ∈ M) : y * m * y⁻¹ ∈ M := by
  have hn := Subgroup.normal_of_index_eq_two (H := M.subgroupOf S) h
  have := hn.conj_mem ⟨m, hMS hm⟩ (by rwa [mem_subgroupOf]) ⟨y, hy⟩
  rwa [mem_subgroupOf] at this

theorem not_isCand_of_classCert (hE : enumOK gs E = true) {reps good : List ℕ}
    (h : classCert E gs reps good = true) {ms : Array (ℕ × ℕ)} {EM : Enum}
    (hEM : enumOK ms EM = true) (hsz : EM.keys.size < 2 ^ 64) (hMS : grpOf ms ≤ grpOf gs)
    (hidx : (grpOf ms).relIndex (grpOf gs) = 2)
    (hgood : (good.all fun r => !(memK EM.keys r) && decide (r < 2 ^ 144)) = true) :
    ∀ s ∈ grpOf ms, ¬ IsCand (grpOf gs) s := by
  intro s hs hc
  obtain ⟨r, hr, rG, hrG, -, y, hy, hsy⟩ := cand_of_classCert hE h (hMS hs) hc
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hgood
  have hrM : rG ∈ grpOf ms := by
    have := conj_mem_of_relIndex_two hMS hidx (inv_mem hy) hs
    rwa [hsy, show y⁻¹ * (y * rG * y⁻¹) * y⁻¹⁻¹ = rG by group] at this
  have := Enum.memK_of_mem' hEM hsz hrM hrG (hgood r hr).2
  rw [(hgood r hr).1] at this
  exact Bool.false_ne_true this

end CFSG.EvenSmallLie.OmegaEight.N3Split
