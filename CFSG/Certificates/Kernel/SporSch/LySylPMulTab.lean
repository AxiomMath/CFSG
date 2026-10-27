module

public import CFSG.Certificates.Kernel.SporSch.LySylDefs
import CFSG.Certificates.Kernel.SporSch.LyLoop
import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.LyCheckSylow

public section

namespace CFSG.KS.SporSch.LySyl

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.SporSch.LyM CFSG.Sporadic.LySchreier.Native
open CFSG.KS.SporSch.LyLoop

private theorem row_spec {MT W PL : Nat → Nat} {n i : Nat} (h : rowOK MT W PL n i = true) :
    (i = 0 → ∀ j < n, tmK MT i j = j) ∧
      (i ≠ 0 → ∀ j < n, tmK MT i j = lamK W (labK PL i) (tmK MT (parK PL i) j)) := by
  unfold rowOK at h
  simp only [strictB_eqB] at h
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  · subst hi
    have h3 : allN n (fun j => Nat.beq (b8 (MT 0) j) j) = true := h2
    exact fun j hj => Nat.eq_of_beq_eq_true (allN_spec h3 j hj)
  · have hb : Nat.beq i 0 = false := by
      cases i with
      | zero => exact absurd rfl hi
      | succ _ => rfl
    rw [hb] at h2
    have h3 : allN n (fun j => Nat.beq (b8 (MT i) j)
        (lamK W (labK PL i) (b8 (MT (parK PL i)) j))) = true := h2
    exact fun j hj => Nat.eq_of_beq_eq_true (allN_spec h3 j hj)

private theorem pl_spec {W PL : Nat → Nat} {n j : Nat} (h : plOK W PL n j = true) :
    (j ≠ 0 → parK PL j < j ∧ labK PL j < 6) ∧ ∀ k < 6, lamK W k j < n := by
  unfold plOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun hj => ?_, fun k hk => ?_⟩
  · have hb : Nat.beq j 0 = false := by
      cases j with
      | zero => exact absurd rfl hj
      | succ _ => rfl
    rw [hb] at h1
    obtain ⟨a, h1'⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨b, -⟩ := (bAnd_iff _ _).1 h1'
    exact ⟨Eq.mp Nat.blt_eq a, Eq.mp Nat.blt_eq b⟩
  · have h3 := allN_spec h2 k hk
    rw [strictB_eqB] at h3
    exact Eq.mp Nat.blt_eq ((bAnd_iff _ _).1 h3).1

private theorem tm_lt {n : Nat} {MT W PL : Nat → Nat}
    (hpl : ∀ j < n, plOK W PL n j = true) (hrow : ∀ i < n, rowOK MT W PL n i = true) :
    ∀ i < n, ∀ j < n, tmK MT i j < n := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi j hj
    by_cases h0 : i = 0
    · rw [(row_spec (hrow i hi)).1 h0 j hj]
      exact hj
    · rw [(row_spec (hrow i hi)).2 h0 j hj]
      obtain ⟨hp, hl⟩ := (pl_spec (hpl i hi)).1 h0
      have hx := ih _ hp (by omega) j hj
      exact (pl_spec (hpl _ hx)).2 _ hl

private theorem forIn_one_spec {β : Type} (R : Nat → β → Prop) (n : Nat) (hn : 1 ≤ n) (init : β)
    (f : Nat → β → Id (ForInStep β)) (h0 : R 1 init)
    (hf : ∀ j b, 1 ≤ j → j < n → R j b → ∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') :
    R n (forIn (m := Id) [1:n] init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have e : ([1:n] : Std.Legacy.Range).size = n - 1 := by simp [Std.Legacy.Range.size]
  rw [e]
  have := forIn_list_spec (fun j b => 1 ≤ j ∧ R j b) n f
    (fun j b hj hb => by
      obtain ⟨b', h1, h2⟩ := hf j b hb.1 hj hb.2
      exact ⟨b', h1, by omega, h2⟩) (n - 1) 1 init (by omega) ⟨le_rfl, h0⟩
  have e2 : 1 + (n - 1) = n := by omega
  rw [e2] at this
  exact this.2

private theorem allIn_of {lo hi : Nat} {p : Nat → Bool} (h : ∀ i, lo ≤ i → i < hi → p i = true) :
    CFSG.Sporadic.Th.Native.allIn lo hi p = true := by
  unfold CFSG.Sporadic.Th.Native.allIn
  have key : ∀ m, m ≤ hi - lo → Nat.all m (fun k _ => p (lo + k)) = true := by
    intro m
    induction m with
    | zero => intro; simp
    | succ m ih =>
      intro hm
      rw [Nat.all_succ, Bool.and_eq_true]
      exact ⟨ih (by omega), h _ (by omega) (by omega)⟩
  exact key _ le_rfl

private theorem tbl_get {MT : Nat → Nat} {n i j : Nat} (hi : i < n) (hj : j < n) :
    ((TBL MT n)[i]!)[j]! = tmK MT i j := by
  unfold TBL
  rw [ofFn_getP (fun i => Array.ofFn (n := n) fun j => tmK MT i j.val) hi,
    ofFn_getP (fun j => tmK MT i j) hj]

theorem _root_.CFSG.KS.SporSch.LySylP.MulTab.mulTab_sound {n : Nat} {MT W PL : Nat → Nat} (hn0 : 0 < n) (hn : n ≤ 256)
    (hpl : ∀ j < n, plOK W PL n j = true) (hrow : ∀ i < n, rowOK MT W PL n i = true) :
    mulTabOf n (Array.ofFn (n := n) fun i => parK PL i.val) (Array.ofFn (n := n) fun i => labK PL i.val)
        (Array.ofFn (n := 6) fun k => Array.ofFn (n := n) fun h => lamK W k.val h.val) = TBL MT n ∧
      mulTabOK (TBL MT n) n (Array.ofFn (n := n) fun i => parK PL i.val)
        (Array.ofFn (n := n) fun i => labK PL i.val)
        (Array.ofFn (n := 6) fun k => Array.ofFn (n := n) fun h => lamK W k.val h.val) = true := by
  have hlt := tm_lt hpl hrow
  have hlam : ∀ l < 6, ∀ x < n,
      ((Array.ofFn (n := 6) fun k => Array.ofFn (n := n) fun h => lamK W k.val h.val)[l]!)[x]! =
        lamK W l x := by
    intro l hl x hx
    rw [ofFn_getP (fun k => Array.ofFn (n := n) fun h => lamK W k h.val) hl,
      ofFn_getP (fun h => lamK W l h) hx]
  have hpar : ∀ j < n, (Array.ofFn (n := n) fun i => parK PL i.val)[j]! = parK PL j :=
    fun j hj => ofFn_getP (fun i => parK PL i) hj
  have hlab : ∀ j < n, (Array.ofFn (n := n) fun i => labK PL i.val)[j]! = labK PL j :=
    fun j hj => ofFn_getP (fun i => labK PL i) hj
  have hrowj : ∀ j < n, j ≠ 0 → ∀ x < n, tmK MT j x =
      ((Array.ofFn (n := 6) fun k => Array.ofFn (n := n) fun h => lamK W k.val h.val)[
        (Array.ofFn (n := n) fun i => labK PL i.val)[j]!]!)[tmK MT (parK PL j) x]! := by
    intro j hj h0 x hx
    obtain ⟨hp, hl⟩ := (pl_spec (hpl j hj)).1 h0
    rw [hlab j hj, hlam _ hl _ (hlt _ (by omega) x hx)]
    exact (row_spec (hrow j hj)).2 h0 x hx
  let Rf : Nat → Array Nat := fun i => Array.ofFn (n := n) fun x => tmK MT i x.val
  have hT : TBL MT n = Array.ofFn (n := n) fun i => Rf i.val := rfl
  refine ⟨?_, ?_⟩
  · have hex : ∃ T, mulTabOf n (Array.ofFn (n := n) fun i => parK PL i.val)
        (Array.ofFn (n := n) fun i => labK PL i.val)
        (Array.ofFn (n := 6) fun k => Array.ofFn (n := n) fun h => lamK W k.val h.val) = T ∧
        T = Array.ofFn (n := n) fun i => Rf i.val := by
      unfold mulTabOf
      refine ⟨_, rfl, forIn_one_spec (fun j T => T = Array.ofFn (n := j) fun i => Rf i.val) n hn0
        _ _ ?_ ?_⟩
      ·
        apply Array.ext
        · simp
        · intro i h1 h2
          have hi : i = 0 := by simp at h2; omega
          subst hi
          simp only [List.getElem_toArray, List.getElem_cons_zero, Array.getElem_ofFn]
          apply Array.ext
          · simp [Rf]
          · intro x hx1 hx2
            simp only [Array.getElem_ofFn, Rf]
            simp at hx1
            exact ((row_spec (hrow 0 hn0)).1 rfl x hx1).symm
      · intro j b hj1 hj hb
        refine ⟨_, rfl, ?_⟩
        subst hb
        rw [← ofFn_push Rf j]
        congr 1
        obtain ⟨hp, -⟩ := (pl_spec (hpl j hj)).1 (by omega)
        rw [hpar j hj, ofFn_getP Rf hp]
        apply Array.ext
        · simp [Rf]
        · intro x hx1 hx2
          have hx : x < n := by simpa [Rf] using hx1
          simp only [Array.getElem_map, Array.getElem_ofFn, Rf]
          exact (hrowj j hj (by omega) x hx).symm
    obtain ⟨T, h1, h2⟩ := hex
    rw [h1, h2, hT]
  · unfold mulTabOK
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp [TBL]
    · intro i hi
      simp only [TBL, Array.size_ofFn] at hi
      simp only [TBL, Array.getElem_ofFn, Array.size_ofFn, Array.all_eq_true, decide_eq_true_eq,
        true_and]
      intro x hx
      exact hlt i hi x hx
    · refine allIn_of fun j _ hj => ?_
      rw [tbl_get hn0 hj, beq_iff_eq]
      exact (row_spec (hrow 0 hn0)).1 rfl j hj
    · refine allIn_of fun i hi1 hi => allIn_of fun x _ hx => ?_
      obtain ⟨hp, -⟩ := (pl_spec (hpl i hi)).1 (by omega)
      rw [tbl_get hi hx, hpar i hi, tbl_get (by omega) hx, beq_iff_eq]
      exact hrowj i hi (by omega) x hx

end CFSG.KS.SporSch.LySyl

end
