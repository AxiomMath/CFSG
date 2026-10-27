module

public import Certificates.Data.CFSGNative.J1.Prim
public import Mathlib.Data.Finset.Card
import CFSG.Certificates.Kernel.SporSch.LyMatLemmas
import CFSG.Certificates.Kernel.Spor.TBfsSound

public section

namespace CFSG.KS.DS

open CFSG.Sporadic.J1.Native CFSG.KS.SporSch.LyM

abbrev DSt := Array Bool × Array (Nat × Nat)

@[expose] def wStep (lab : Array Nat) (j : Nat) (im : Array Nat) (s : DSt) (w : Nat) : DSt :=
  if s.1[lab[w]!]! = true then
    if (!s.1[lab[im[w]!]!]!) = true then (s.1.set! lab[im[w]!]! true, s.2.push (j, w)) else s
  else s

@[expose] def jStep (n : Nat) (lab : Array Nat) (imgs : Array (Array Nat)) (s : DSt) (j : Nat) :
    DSt :=
  if s.1[j]! = true then (List.range n).foldl (wStep lab j imgs[j]!) s else s

@[expose] def round (n k : Nat) (lab : Array Nat) (imgs : Array (Array Nat)) (s : DSt) : DSt :=
  (List.range k).foldl (jStep n lab imgs) s

@[expose] def initD (k l0 i : Nat) : Array Bool := ((Array.replicate k false).set! l0 true).set! i true

theorem ite_pure_yieldD {β : Type} (q : Prop) [Decidable q] (a b : β) :
    (if q then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if q then a else b)) := by
  split <;> rfl

theorem derSearch_fold (n k l0 i : Nat) (lab : Array Nat) (imgs : Array (Array Nat)) :
    derSearch n k l0 i lab imgs =
      ((List.range (k + 1)).foldl (fun s _ => round n k lab imgs s) (initD k l0 i, #[])).2.toList := by
  unfold derSearch
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yieldD,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  have h1 : ∀ a b : Nat, [a:b].size = b - a := fun a b => by simp [Std.Legacy.Range.size]
  simp only [h1, Nat.sub_zero, ← List.range_eq_range']
  rfl

variable {n k l0 i : Nat} {lab : Array Nat} {imgs : Array (Array Nat)}

abbrev LeD (D D' : Array Bool) : Prop := ∀ l : Nat, D[l]! = true → D'[l]! = true

theorem LeD.refl (D : Array Bool) : LeD D D := fun _ h => h

theorem LeD.trans {D D' D'' : Array Bool} (h1 : LeD D D') (h2 : LeD D' D'') : LeD D D'' :=
  fun l h => h2 l (h1 l h)

theorem set_get (D : Array Bool) (a l : Nat) (ha : a < D.size) :
    (D.set! a true)[l]! = if l = a then true else D[l]! := by
  by_cases hl : l < D.size
  · rw [get_setR D a true hl]
  · rw [getElem!_neg _ l (by rw [size_setR]; exact hl), getElem!_neg D l hl]
    have : l ≠ a := by omega
    simp [this]

theorem le_set (D : Array Bool) (a : Nat) (ha : a < D.size) : LeD D (D.set! a true) := by
  intro l h
  rw [set_get D a l ha]
  split <;> simp_all

structure Good (n k l0 i : Nat) (lab : Array Nat) (imgs : Array (Array Nat)) (s : DSt) : Prop where
  size : s.1.size = k
  replay : derRun n k l0 i lab imgs s.2.toList = s.1

theorem wStep_good (hlab : ∀ w < n, lab[w]! < k) (himg : ∀ j < k, ∀ w < n, (imgs[j]!)[w]! < n)
    {j : Nat} (hj : j < k) {s : DSt} (hG : Good n k l0 i lab imgs s) (hsj : s.1[j]! = true)
    {w : Nat} (hw : w < n) :
    Good n k l0 i lab imgs (wStep lab j imgs[j]! s w) ∧ LeD s.1 (wStep lab j imgs[j]! s w).1 ∧
      (s.1[lab[w]!]! = true → (wStep lab j imgs[j]! s w).1[lab[(imgs[j]!)[w]!]!]! = true) := by
  have hl := hlab _ (himg j hj w hw)
  unfold wStep
  by_cases h1 : s.1[lab[w]!]! = true
  · rw [ite_eq_left h1]
    by_cases h2 : (!s.1[lab[(imgs[j]!)[w]!]!]!) = true
    · rw [ite_eq_left h2]
      refine ⟨⟨by rw [size_setR, hG.size], ?_⟩, le_set _ _ (by rw [hG.size]; exact hl),
        fun _ => by rw [set_get _ _ _ (by rw [hG.size]; exact hl), ite_eq_left rfl]⟩
      unfold derRun
      rw [Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change derStep n k lab imgs (derRun n k l0 i lab imgs s.2.toList) (j, w) = _
      rw [hG.replay]
      unfold derStep
      simp [hj, hw, hsj, h1]
    · rw [ite_eq_right h2]
      simp only [Bool.not_eq_true', Bool.not_eq_false] at h2
      exact ⟨hG, LeD.refl _, fun _ => by simpa using h2⟩
  · rw [ite_eq_right h1]
    exact ⟨hG, LeD.refl _, fun h => absurd h h1⟩

theorem wFold_good (hlab : ∀ w < n, lab[w]! < k) (himg : ∀ j < k, ∀ w < n, (imgs[j]!)[w]! < n)
    {j : Nat} (hj : j < k) {s : DSt} (hG : Good n k l0 i lab imgs s) (hsj : s.1[j]! = true) :
    ∀ m ≤ n, Good n k l0 i lab imgs ((List.range m).foldl (wStep lab j imgs[j]!) s) ∧
      LeD s.1 ((List.range m).foldl (wStep lab j imgs[j]!) s).1 ∧
      ∀ w < m, s.1[lab[w]!]! = true →
        ((List.range m).foldl (wStep lab j imgs[j]!) s).1[lab[(imgs[j]!)[w]!]!]! = true := by
  intro m
  induction m with
  | zero => intro _; exact ⟨hG, LeD.refl _, fun w hw => absurd hw (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨g1, g2, g3⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2, h3⟩ := wStep_good hlab himg hj g1 (g2 j hsj) (w := m) (by omega)
    refine ⟨h1, g2.trans h2, fun w hw hsw => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hw | rfl
    · exact h2 _ (g3 w hw hsw)
    · exact h3 (g2 _ hsw)

theorem round_good (hlab : ∀ w < n, lab[w]! < k) (himg : ∀ j < k, ∀ w < n, (imgs[j]!)[w]! < n)
    {s : DSt} (hG : Good n k l0 i lab imgs s) :
    ∀ m ≤ k, Good n k l0 i lab imgs ((List.range m).foldl (jStep n lab imgs) s) ∧
      LeD s.1 ((List.range m).foldl (jStep n lab imgs) s).1 ∧
      ∀ j < m, s.1[j]! = true → ∀ w < n, s.1[lab[w]!]! = true →
        ((List.range m).foldl (jStep n lab imgs) s).1[lab[(imgs[j]!)[w]!]!]! = true := by
  intro m
  induction m with
  | zero => intro _; exact ⟨hG, LeD.refl _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨g1, g2, g3⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range m).foldl (jStep n lab imgs) s = t at g1 g2 g3
    unfold jStep
    by_cases ht : t.1[m]! = true
    · rw [ite_eq_left ht]
      obtain ⟨h1, h2, h3⟩ := wFold_good hlab himg (by omega) g1 ht n (Nat.le_refl _)
      refine ⟨h1, g2.trans h2, fun j hj hsj w hw hsw => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h2 _ (g3 j hj hsj w hw hsw)
      · exact h3 w hw (g2 _ hsw)
    · rw [ite_eq_right ht]
      refine ⟨g1, g2, fun j hj hsj w hw hsw => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact g3 j hj hsj w hw hsw
      · exact absurd (g2 _ hsj) ht

abbrev ClosedD (n k : Nat) (lab : Array Nat) (imgs : Array (Array Nat)) (D : Array Bool) :
    Prop :=
  ∀ j < k, D[j]! = true → ∀ w < n, D[lab[w]!]! = true → D[lab[(imgs[j]!)[w]!]!]! = true

@[expose] noncomputable def cntD (k : Nat) (D : Array Bool) : Nat :=
  ((Finset.range k).filter fun l => D[l]! = true).card

theorem cnt_le (k : Nat) (D : Array Bool) : cntD k D ≤ k := by
  unfold cntD
  exact le_trans (Finset.card_filter_le _ _) (by simp)

theorem cnt_lt {k : Nat} {D D' : Array Bool} (h : LeD D D') {l : Nat} (hl : l < k)
    (h1 : D'[l]! = true) (h2 : D[l]! ≠ true) : cntD k D < cntD k D' := by
  unfold cntD
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => h2 ?_⟩
  · simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, h x hx.2⟩
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_range.2 hl, h1⟩)
    exact (Finset.mem_filter.1 this).2

theorem closed_fix {t : DSt} (hcl : ClosedD n k lab imgs t.1) :
    ∀ l : Nat, (round n k lab imgs t).1[l]! = true → t.1[l]! = true := by
  have key : ∀ m ≤ k, ((List.range m).foldl (jStep n lab imgs) t).1 = t.1 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have e := ih (by omega)
      generalize hu : (List.range m).foldl (jStep n lab imgs) t = u at e
      unfold jStep
      rw [e]
      split
      · next hum =>
        have hw : ∀ m' ≤ n, ((List.range m').foldl (wStep lab m imgs[m]!) u).1 = t.1 := by
          intro m'
          induction m' with
          | zero => intro _; exact e
          | succ m' ih' =>
            intro hm'
            rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
            have e' := ih' (by omega)
            generalize (List.range m').foldl (wStep lab m imgs[m]!) u = v at e'
            unfold wStep
            rw [e']
            split
            · next hv =>
              have := hcl m (by omega) hum m' (by omega) hv
              rw [ite_eq_right (by simp [this])]
              exact e'
            · exact e'
        exact hw n (Nat.le_refl _)
      · exact e
  intro l h
  have := key k (Nat.le_refl _)
  unfold round at h
  rw [this] at h
  exact h

theorem rounds_closed (hlab : ∀ w < n, lab[w]! < k) (himg : ∀ j < k, ∀ w < n, (imgs[j]!)[w]! < n)
    {s : DSt} (hG : Good n k l0 i lab imgs s) (h0 : 1 ≤ cntD k s.1) :
    ∀ m, Good n k l0 i lab imgs ((List.range m).foldl (fun s _ => round n k lab imgs s) s) ∧
      LeD s.1 ((List.range m).foldl (fun s _ => round n k lab imgs s) s).1 ∧
      (ClosedD n k lab imgs ((List.range m).foldl (fun s _ => round n k lab imgs s) s).1 ∨
        m + 1 ≤ cntD k ((List.range m).foldl (fun s _ => round n k lab imgs s) s).1) := by
  intro m
  induction m with
  | zero => exact ⟨hG, LeD.refl _, Or.inr h0⟩
  | succ m ih =>
    obtain ⟨g1, g2, g3⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range m).foldl (fun s _ => round n k lab imgs s) s = t at g1 g2 g3
    obtain ⟨r1, r2, r3⟩ := round_good hlab himg g1 k (Nat.le_refl _)
    change Good n k l0 i lab imgs (round n k lab imgs t) at r1
    change LeD t.1 (round n k lab imgs t).1 at r2
    change ∀ j < k, t.1[j]! = true → ∀ w < n, t.1[lab[w]!]! = true →
      (round n k lab imgs t).1[lab[(imgs[j]!)[w]!]!]! = true at r3
    refine ⟨r1, g2.trans r2, ?_⟩
    by_cases hc : LeD (round n k lab imgs t).1 t.1
    ·
      left
      have hct : ClosedD n k lab imgs t.1 := fun j hj hsj w hw hsw => hc _ (r3 j hj hsj w hw hsw)
      intro j hj hsj w hw hsw
      exact r2 _ (hct j hj (hc _ hsj) w hw (hc _ hsw))
    · right
      unfold LeD at hc
      simp only [not_forall] at hc
      obtain ⟨l, hl1, hl2⟩ := hc
      have hlk : l < k := by
        by_contra hge
        rw [getElem!_neg _ l (by rw [r1.size]; omega)] at hl1
        exact absurd hl1 (by decide)
      have hlt := cnt_lt r2 hlk hl1 hl2
      rcases g3 with hcl | hge
      · exact absurd (closed_fix hcl l hl1) hl2
      · omega

theorem derSearch_ok (hlab : ∀ w < n, lab[w]! < k) (himg : ∀ j < k, ∀ w < n, (imgs[j]!)[w]! < n)
    (hl0 : l0 < k) (hi : i < k)
    (hall : ∀ S : Nat → Prop, S l0 → S i →
      (∀ j < k, ∀ w < n, S j → S lab[w]! → S lab[(imgs[j]!)[w]!]!) → ∀ l < k, S l) :
    derOK n k l0 i lab imgs (derSearch n k l0 i lab imgs) = true := by
  have hsz : (initD k l0 i).size = k := by simp [initD]
  have hin0 : (initD k l0 i)[l0]! = true ∧ (initD k l0 i)[i]! = true := by
    unfold initD
    refine ⟨?_, by rw [set_get _ _ _ (by rw [size_setR]; simpa using hi), ite_eq_left rfl]⟩
    rw [set_get _ _ _ (by rw [size_setR]; simpa using hi)]
    split
    · rfl
    · rw [set_get _ _ _ (by simpa using hl0), ite_eq_left rfl]
  have hG : Good n k l0 i lab imgs (initD k l0 i, #[]) := ⟨hsz, rfl⟩
  have h1 : 1 ≤ cntD k (initD k l0 i) := by
    unfold cntD
    exact Finset.card_pos.2 ⟨l0, Finset.mem_filter.2 ⟨Finset.mem_range.2 hl0, hin0.1⟩⟩
  obtain ⟨g1, g2, g3⟩ := rounds_closed hlab himg hG h1 (k + 1)
  rw [derSearch_fold]
  generalize (List.range (k + 1)).foldl (fun s _ => round n k lab imgs s) (initD k l0 i, #[]) = s
    at g1 g2 g3 ⊢
  have hcl : ClosedD n k lab imgs s.1 := by
    rcases g3 with h | h
    · exact h
    · have := cnt_le k s.1
      omega
  have hallk := hall (fun l => s.1[l]! = true) (g2 _ hin0.1) (g2 _ hin0.2)
    (fun j hj w hw hsj hsw => hcl j hj hsj w hw hsw)
  unfold derOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  have e := g1.replay
  change derRun n k l0 i lab imgs s.2.toList = s.1 at e
  rw [e]
  exact ⟨g1.size, CFSG.KS.TBfs.allIn_iff.2 hallk⟩

end CFSG.KS.DS

end
