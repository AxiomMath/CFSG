module

public import Certificates.Data.Kernel.Spor.PEnum
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.Certificates.Kernel.Spor.BfsReplay
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawSiftK
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.Schreier
import Std.Tactic.BVDecide.Normalize.BitVec

namespace CFSG.KS.PEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.PSL3Four.Native CFSG.KS.BfsReplay
  CFSG.Monster.B.Co2.Native

public section

@[expose] noncomputable def penumRec (n w cnt : Nat) (T PL : Nat → Nat) : Enum :=
  ⟨Array.ofFn (n := cnt) fun i => unpack n w (T i.val),
    Array.ofFn (n := cnt) fun i => parOf PL i.val, Array.ofFn (n := cnt) fun i => labOf PL i.val⟩

@[expose] def GensOK (n w k : Nat) (G : Nat → Nat) (gens : Array Tab) : Prop :=
  gens.size = k ∧ ∀ j < k, gens[j]! = unpack n w (G j) ∧ canonK n w (mask w) (n * w) (G j) = true

theorem penumRec_eq (n w cnt : Nat) (T PL : Nat → Nat) :
    penumRec n w cnt T PL = ⟨Array.ofFn (n := cnt) fun i => unpack n w (T i.val),
      Array.ofFn (n := cnt) fun i => parOf PL i.val,
      Array.ofFn (n := cnt) fun i => labOf PL i.val⟩ :=
  rfl

theorem found_indexOf_iff (A : Array Tab) (x : Tab) :
    found (indexOf A) A x = true ↔ ∃ i < A.size, A[i]! = x := by
  have key : (∀ y, (∃ i < A.size, A[i]! = y) →
      (indexOf A).getD y A.size < A.size ∧ A[(indexOf A).getD y A.size]! = y) ∧
      ∀ y, (∀ i < A.size, A[i]! ≠ y) → (indexOf A).getD y A.size = A.size := by
    unfold indexOf
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one]
    have := forIn_range'_yield A.size 0 (Std.HashMap.emptyWithCapacity A.size)
      (fun k m => pure (ForInStep.yield (m.insert A[k]! k)))
      (fun j (m : Std.HashMap Tab Nat) => (∀ y, (∃ i < j, A[i]! = y) →
        m.getD y A.size < j ∧ A[m.getD y A.size]! = y) ∧
        ∀ y, (∀ i < j, A[i]! ≠ y) → m.getD y A.size = A.size)
      (fun j hj m hP => ⟨_, rfl, fun y hy => ?_, fun y hy => ?_⟩)
      ⟨fun y ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero _),
        fun y _ => Std.HashMap.getD_emptyWithCapacity⟩
    · exact ⟨fun y hy => this.1 y hy, this.2⟩
    · rw [Nat.zero_add, Std.HashMap.getD_insert]
      by_cases e : A[j]! = y
      · rw [ite_eq_left (beq_iff_eq.2 e)]
        exact ⟨by omega, e⟩
      · rw [ite_eq_right (by simpa using e)]
        obtain ⟨i, hi, hiy⟩ := hy
        have hij : i < j := by
          rcases Nat.lt_or_ge i j with a | a
          · exact a
          · exact absurd (by rw [show j = i by omega]; exact hiy) e
        obtain ⟨h1, h2⟩ := hP.1 y ⟨i, hij, hiy⟩
        exact ⟨by omega, h2⟩
    · rw [Nat.zero_add, Std.HashMap.getD_insert, ite_eq_right (by simpa using hy j (by omega))]
      exact hP.2 y fun i hi => hy i (by omega)
  unfold found posOf
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨_, h.1, h.2⟩
  · intro h
    obtain ⟨h1, h2⟩ := key.1 x h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨h1, h2⟩

end

theorem lexLtK_iff' {a b c d : Nat} : lexLtK a b c d = true ↔ LexLt a b c d := by
  unfold lexLtK LexLt
  rw [CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.blt_dec,
    CFSG.KS.Raw.Orb.beq_dec, CFSG.KS.Raw.Orb.blt_dec]
  by_cases h : a < c
  · simp [h]
  · simp [h]

theorem penumPt_spec {n w m nw k cnt i : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumPtK n w m nw conj G GI k cnt T PL POS SRT SRI i = true) :
    canonK n w m nw (T i) = true ∧
    (i ≠ 0 → parOf PL i < i ∧ labOf PL i < k ∧
      T i = stepK n w m conj G GI (labOf PL i) (T (parOf PL i)) ∧
      (i + 1 < cnt → LexLt (parOf PL i) (labOf PL i) (parOf PL (i + 1)) (labOf PL (i + 1)))) ∧
    (∀ j < k, r32 POS (i * k + j) < cnt ∧
      T (r32 POS (i * k + j)) = stepK n w m conj G GI j (T i) ∧
      (r32 POS (i * k + j) = 0 ∨
        ¬ LexLt i j (parOf PL (r32 POS (i * k + j))) (labOf PL (r32 POS (i * k + j))))) ∧
    (r32 SRT i < cnt ∧ r32 SRI (r32 SRT i) = i ∧
      (i + 1 < cnt → T (r32 SRT i) < T (r32 SRT (i + 1)))) := by
  unfold penumPtK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hc, ht, hpos, hs⟩ := h
  refine ⟨hc, fun hi => ?_, fun j hj => ?_, ?_⟩
  · have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [e] at ht
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, Bool.and_eq_true,
      Nat.blt_eq] at ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    refine ⟨h1, h2, Nat.eq_of_beq_eq_true h3, fun hc => ?_⟩
    have hc' : Nat.succ i < cnt := hc
    simp only [hc', ↓reduceIte] at h4
    exact lexLtK_iff'.1 h4
  · have hq := allN_spec hpos j hj
    simp only [CFSG.KS.Raw.Orb.strictB_eq, Nat.mul_eq, Nat.add_eq, Bool.and_eq_true,
      Nat.blt_eq] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨h1, Nat.eq_of_beq_eq_true h2, ?_⟩
    by_cases h0 : r32 POS (i * k + j) = 0
    · exact Or.inl h0
    · right
      have e : Nat.beq (r32 POS (i * k + j)) 0 = false :=
        Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      rw [e] at h3
      intro hl
      rw [← lexLtK_iff'] at hl
      rw [hl] at h3
      exact absurd h3 (by decide)
  · rw [CFSG.KS.Raw.Orb.strictB_eq] at hs
    simp only [CFSG.KS.Raw.Orb.bIf_eq, Bool.and_eq_true, Nat.blt_eq] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨h1, Nat.eq_of_beq_eq_true h2, fun hc => ?_⟩
    have hc' : Nat.succ i < cnt := hc
    simp only [hc', ↓reduceIte] at h3
    exact Nat.blt_eq.mp h3

theorem inj_of_sort {cnt : Nat} {T S SI : Nat → Nat}
    (hS : ∀ i < cnt, S i < cnt ∧ SI (S i) = i ∧ (i + 1 < cnt → T (S i) < T (S (i + 1)))) :
    ∀ a < cnt, ∀ b < cnt, T a = T b → a = b := by
  have hmono : ∀ i j, i < j → j < cnt → T (S i) < T (S j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) ((hS j (by omega)).2.2 hj)
      · subst h
        exact (hS i (by omega)).2.2 hj
  have hsurj : ∀ a < cnt, ∃ i < cnt, S i = a := by
    classical
    have himg : (Finset.range cnt).image S = Finset.range cnt := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_range.2 (hS i (Finset.mem_range.1 hi)).1
      · rw [Finset.card_image_of_injOn]
        intro i hi j hj e
        have h1 := (hS i (Finset.mem_range.1 hi)).2.1
        have h2 := (hS j (Finset.mem_range.1 hj)).2.1
        rw [← h1, ← h2]
        exact congrArg SI e
    intro a ha
    have : a ∈ (Finset.range cnt).image S := by rw [himg]; exact Finset.mem_range.2 ha
    obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
    exact ⟨i, Finset.mem_range.1 hi, e⟩
  intro a ha b hb e
  obtain ⟨i, hi, rfl⟩ := hsurj a ha
  obtain ⟨j, hj, rfl⟩ := hsurj b hb
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd e (Nat.ne_of_lt (hmono i j h hj))
  · rw [h]
  · exact absurd e.symm (Nat.ne_of_lt (hmono j i h hi))

theorem unpack_inj {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (h : unpack n w p = unpack n w q) : p = q := by
  obtain ⟨-, hw, hp1, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hq1, -⟩ := CFSG.KS.PF.canon_facts hq
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp1 hq1 fun i hi => ?_
  rw [← CFSG.KS.Raw.Orb.unpack_get hi, ← CFSG.KS.Raw.Orb.unpack_get hi, h]

theorem replay_of {n w k cnt cap : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
    {step : Nat → Tab → Tab} {root : Tab} {R : Nat}
    (hstep : ∀ j < k, ∀ t, canonK n w (mask w) (n * w) t = true →
      step j (unpack n w t) = unpack n w (stepK n w (mask w) conj G GI j t))
    (hroot : root = unpack n w R)
    (hh : penumHdK R cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) conj G GI k cnt T PL POS SRT SRI i = true) :
    Replay step k root cnt (fun i => unpack n w (T i)) (parOf PL) (labOf PL)
      (fun h j => r32 POS (h * k + j)) ∧ cnt ≤ cap := by
  unfold penumHdK at hh
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hh
  obtain ⟨hc0, hcap, hT0, hPL0⟩ := hh
  have sp := fun i (hi : i < cnt) => penumPt_spec (hp i hi)
  have hinjT : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b :=
    inj_of_sort (T := T) (S := r32 SRT) (SI := r32 SRI) fun i hi => (sp i hi).2.2.2
  refine ⟨⟨hc0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hcap⟩
  · rw [Nat.eq_of_beq_eq_true hT0, hroot]
  · unfold parOf
    rw [Nat.eq_of_beq_eq_true hPL0]
    rfl
  · unfold labOf
    rw [Nat.eq_of_beq_eq_true hPL0]
    rfl
  · intro a ha b hb e
    exact hinjT a ha b hb (unpack_inj (sp a ha).1 (sp b hb).1 e)
  · intro i hi0 hi
    obtain ⟨h1, h2, h3, -⟩ := (sp i hi).2.1 (by omega)
    refine ⟨h1, h2, ?_⟩
    rw [hstep _ h2 _ (sp _ (by omega)).1, ← h3]
  · intro i hi0 hi
    exact ((sp i (by omega)).2.1 (by omega)).2.2.2 hi
  · intro h hh j hj
    obtain ⟨h1, h2, h3⟩ := (sp h hh).2.2.1 j hj
    refine ⟨h1, ?_, h3⟩
    rw [hstep _ hj _ (sp h hh).1, h2]

theorem idTab_unpack {n w : Nat} (hn : szOK n w = true) : idTab n = unpack n w (pidn n w) := by
  obtain ⟨h1, h2⟩ := CFSG.KS.Raw.Orb.szOK_facts hn
  apply Array.ext
  · simp [idTab, unpack]
  · intro i hi _
    have hi' : i < n := by simpa [idTab] using hi
    rw [← getElem!_pos _ i hi,
      ← getElem!_pos (unpack n w (pidn n w)) i (by simpa [unpack] using hi'),
      CFSG.KS.Raw.Orb.unpack_get hi', CFSG.KS.PF.pg_pidn h1 h2 hi', getElem!_pos _ i hi]
    simp [idTab]

theorem comp_unpack {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    comp n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

public section

theorem penumK_left_sound {n w k cnt cap : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    {gens : Array Tab} (hn : szOK n w = true) (hg : GensOK n w k G gens)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) false G GI k cnt T PL POS SRT SRI i = true) :
    enumBFS n gens cap = penumRec n w cnt T PL ∧ enumOK n gens (penumRec n w cnt T PL) = true := by
  obtain ⟨hk, hgj⟩ := hg
  have hstep : ∀ j < k, ∀ t, canonK n w (mask w) (n * w) t = true →
      leftStep n gens j (unpack n w t) =
        unpack n w (stepK n w (mask w) false G GI j t) := by
    intro j hj t ht
    unfold leftStep
    rw [(hgj j hj).1]
    exact comp_unpack (hgj j hj).2 ht
  obtain ⟨R, hcap⟩ := replay_of (step := leftStep n gens) (root := idTab n) hstep
    (idTab_unpack hn) hh hp
  rw [← hk] at R
  have := enumBFS_replay R hcap
  rw [penumRec_eq]
  exact this

theorem penumK_conj_sound {n w k cnt cap X : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    {gens ginv : Array Tab} {x : Tab} (_hn : szOK n w = true) (hg : GensOK n w k G gens)
    (hgi : GensOK n w k GI ginv) (hx : x = unpack n w X)
    (hh : penumHdK X cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true) :
    orbitBFS n gens ginv x cap = penumRec n w cnt T PL ∧
      treeOK (conjStep n gens ginv) gens.size x (penumRec n w cnt T PL) = true := by
  obtain ⟨hk, hgj⟩ := hg
  obtain ⟨-, hgij⟩ := hgi
  have hstep : ∀ j < k, ∀ t, canonK n w (mask w) (n * w) t = true →
      conjStep n gens ginv j (unpack n w t) =
        unpack n w (stepK n w (mask w) true G GI j t) := by
    intro j hj t ht
    unfold conjStep conjTab
    rw [(hgj j hj).1, (hgij j hj).1, comp_unpack (hgj j hj).2 ht]
    exact comp_unpack (CFSG.KC.BfsPin.canonK_pcomp (hgj j hj).2 ht) (hgij j hj).2
  obtain ⟨R, hcap⟩ := replay_of (step := conjStep n gens ginv) (root := x) hstep hx hh hp
  rw [← hk] at R
  have := bfs_replay R hcap
  unfold orbitBFS
  rw [penumRec_eq]
  exact this

theorem penum_found_sound {n w k cnt q X : Nat} {conj : Bool}
    {G GI T PL POS SRT SRI : Nat → Nat}
    (_hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) conj G GI k cnt T PL POS SRT SRI i = true)
    (hq : q < cnt) (hX : T q = X) :
    found (indexOf (penumRec n w cnt T PL).tabs) (penumRec n w cnt T PL).tabs (unpack n w X) =
      true := by
  rw [found_indexOf_iff]
  refine ⟨q, by simpa [penumRec] using hq, ?_⟩
  rw [getElem!_pos _ q (by simpa [penumRec] using hq)]
  simp [penumRec, hX]

theorem found_penumRec_iff {n w k cnt X : Nat} {conj : Bool}
    {G GI T PL POS SRT SRI : Nat → Nat}
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) conj G GI k cnt T PL POS SRT SRI i = true)
    (hX : canonK n w (mask w) (n * w) X = true) :
    found (indexOf (penumRec n w cnt T PL).tabs) (penumRec n w cnt T PL).tabs (unpack n w X) =
      true ↔ ∃ i < cnt, T i = X := by
  rw [found_indexOf_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    have hi' : i < cnt := by simpa [penumRec] using hi
    refine ⟨i, hi', unpack_inj (penumPt_spec (hp i hi')).1 hX ?_⟩
    rw [← e, getElem!_pos _ i hi]
    simp [penumRec]
  · rintro ⟨i, hi, e⟩
    refine ⟨i, by simpa [penumRec] using hi, ?_⟩
    rw [getElem!_pos _ i (by simpa [penumRec] using hi)]
    simp [penumRec, e]

end

end CFSG.KS.PEnum
