module

public import CFSG.CGT.M24R.L2FD

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

@[expose] def Adm8 (u : Fin 3 → N8) : Prop :=
  (∀ w, wv d8 w ∈ T8 → wv u w ∈ B8) ∧ (∀ w, wv d8 w ∈ B8 → wv u w ∈ T8) ∧
    (∀ w, wv d8 w ≠ 1 → wv u w ≠ 1) ∧ ∀ l r, wv d8 l = wv d8 r → wv u l = wv u r

theorem wv_conj (e : N8) (u : Fin 3 → N8) (w : List (Fin 3)) :
    wv (fun k => e * u k * e⁻¹) w = e * wv u w * e⁻¹ := by
  induction w with
  | nil => simp [wv_nil]
  | cons k w ih => rw [wv_cons, wv_cons, ih]; group

theorem Adm8.conj (hT : T8.Normal) {u : Fin 3 → N8} (h : Adm8 u) {e : N8} (he : e ∈ D8) :
    Adm8 fun k => e * u k * e⁻¹ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun l r hlr => ?_⟩
  · rw [wv_conj]
    exact (Subgroup.mem_normalizer_iff.1 he _).1 (h1 w hw)
  · rw [wv_conj]
    exact hT.conj_mem _ (h2 w hw) e
  · rw [wv_conj]
    intro h
    exact h3 w hw (by simpa using h)
  · rw [wv_conj, wv_conj, h4 l r hlr]

theorem le_foldl_max (w : List (Fin 3)) :
    ∀ m : ℕ, m ≤ w.foldl (fun m k => max m k.val) m ∧
      ∀ k ∈ w, k.val ≤ w.foldl (fun m k => max m k.val) m := by
  induction w with
  | nil => intro m; simp
  | cons k w ih =>
    intro m
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (max m k.val)
    refine ⟨(le_max_left _ _).trans h1, fun k' hk' => ?_⟩
    rcases List.mem_cons.1 hk' with rfl | hk'
    · exact (le_max_right _ _).trans h1
    · exact h2 k' hk'

theorem le_maxL {w : List (Fin 3)} {k : Fin 3} (hk : k ∈ w) : k.val ≤ maxL w :=
  (le_foldl_max w 0).2 k hk

theorem fcAll_getD {j : ℕ} (hj : j < 3) : (fcAll (mkCtx ())).getD j default =
    { wA := ((dBFSq ()).2.toList.map Prod.snd).filter fun w =>
        maxL w == j && (mkCtx ()).isTt (evT dT w)
      wB := ((dBFSq ()).2.toList.map Prod.snd).filter fun w => maxL w == j && isBt (evT dT w)
      wN := ((dBFSq ()).2.toList.map Prod.snd).filter fun w =>
        maxL w == j && !(evT dT w == idT 16)
      wP := ((dBFSq ()).2.toList.flatMap fun xw => (List.finRange 3).map fun k =>
        (xw.2 ++ [k], (((dBFSq ()).1)[codeOf (compT 16 xw.1 (dT k))]!).getD [])).filter
          fun p => max (maxL p.1) (maxL p.2) == j && evT dT p.1 == evT dT p.2 } := by
  simp [fcAll, List.getD_eq_getElem?_getD, hj]

section FC

variable (hcard : Nat.card N8 = 322560)
include hcard

theorem goodC_of_adm {j : ℕ} (hj : j < 3) {u : Fin 3 → N8} (hu : Adm8 u) {a : Fin 3 → Table}
    (ha : ∀ k : Fin 3, k.val ≤ j → IsTab (a k) (u k)) :
    (mkCtx ()).goodC ((fcAll (mkCtx ())).getD j default) a = true := by
  have hev : ∀ w : List (Fin 3), maxL w = j → IsTab (evT a w) (wv u w) := fun w hw =>
    evT_isTab w fun k hk => ha k (hw ▸ le_maxL hk)
  have hd : ∀ w : List (Fin 3), IsTab (evT dT w) (wv d8 w) := fun w =>
    evT_isTab w fun k _ => isTab_dT k
  rw [fcAll_getD hj]
  simp only [Ctx8.goodC, Bool.and_eq_true, List.all_eq_true, List.mem_filter, beq_iff_eq,
    Bool.not_eq_true', and_imp]
  refine ⟨⟨⟨fun w _ hw h => ?_, fun w _ hw h => ?_⟩, fun w _ hw h => ?_⟩, fun p _ hp h => ?_⟩
  · exact (isBt_iff hcard (hev w hw) (evT_size _ _)).2
      (hu.1 w ((isTt_iff hcard (hd w) (evT_size _ _)).1 h))
  · exact (isTt_iff hcard (hev w hw) (evT_size _ _)).2
      (hu.2.1 w ((isBt_iff hcard (hd w) (evT_size _ _)).1 h))
  · rw [Bool.eq_false_iff]
    intro h'
    refine hu.2.2.1 w (fun h1 => ?_) (((hev w hw).beq_iff hcard IsTab.one (evT_size _ _)
      idT_size).1 h')
    rw [((hd w).beq_iff hcard IsTab.one (evT_size _ _) idT_size).2 h1] at h
    exact absurd h (by decide)
  · have hl : maxL p.1 ≤ j := hp ▸ le_max_left _ _
    have hr : maxL p.2 ≤ j := hp ▸ le_max_right _ _
    have hev' : ∀ w : List (Fin 3), maxL w ≤ j → IsTab (evT a w) (wv u w) := fun w hw =>
      evT_isTab w fun k hk => ha k ((le_maxL hk).trans hw)
    exact ((hev' _ hl).eq_iff hcard (hev' _ hr) (evT_size _ _) (evT_size _ _)).2
      (hu.2.2.2 _ _ ((hd _).eq_of_eq hcard (h ▸ hd _)))

omit hcard in
theorem fcTree_succ (cx : Ctx8) (dl : List ℕ) (cs : List FCConds) (thc : List ℕ) (fuel : ℕ)
    (P : List ℕ) : cx.fcTree dl cs thc (fuel + 1) P =
      ((cx.mkReps (dl.filter fun e => P.all fun p => commT (cx.tab e) (cx.tab p))
          (if (dl.filter fun v => cx.goodC (cs.getD P.length default) (cx.asg (P ++ [v]))).contains
              (thc.getD P.length 0) then thc.getD P.length 0 ::
              dl.filter fun v => cx.goodC (cs.getD P.length default) (cx.asg (P ++ [v]))
            else dl.filter fun v => cx.goodC (cs.getD P.length default) (cx.asg (P ++ [v])))).all
          (fun r => decide (r < 1048576)) &&
        (dl.filter fun v => cx.goodC (cs.getD P.length default) (cx.asg (P ++ [v]))).all
          (fun v => (cx.mkReps (dl.filter fun e => P.all fun p => commT (cx.tab e) (cx.tab p))
            (if (dl.filter fun v => cx.goodC (cs.getD P.length default)
                (cx.asg (P ++ [v]))).contains (thc.getD P.length 0) then thc.getD P.length 0 ::
                dl.filter fun v => cx.goodC (cs.getD P.length default) (cx.asg (P ++ [v]))
              else dl.filter fun v => cx.goodC (cs.getD P.length default)
                (cx.asg (P ++ [v])))).any fun r =>
            (dl.filter fun e => P.all fun p => commT (cx.tab e) (cx.tab p)).any fun e =>
              cx.conjEq e v r) &&
        (cx.mkReps (dl.filter fun e => P.all fun p => commT (cx.tab e) (cx.tab p))
          (if (dl.filter fun v => cx.goodC (cs.getD P.length default) (cx.asg (P ++ [v]))).contains
              (thc.getD P.length 0) then thc.getD P.length 0 ::
              dl.filter fun v => cx.goodC (cs.getD P.length default) (cx.asg (P ++ [v]))
            else dl.filter fun v => cx.goodC (cs.getD P.length default) (cx.asg (P ++ [v])))).all
          fun r => cx.fcTree dl cs thc fuel (P ++ [r])) := rfl

end FC

end CFSG.CGT.M24R
