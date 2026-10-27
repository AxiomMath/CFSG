module

public import Certificates.Data.Kernel.Spor.MulH
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.HBfsReplay
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import Mathlib.Data.Finset.Card
public import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Monster.B.Co2.Native CFSG.KS.BfsReplay

@[expose] def tabT (a : Array Nat) : Table := a.map UInt32.ofNat

@[expose] noncomputable def hRec (n w cnt : Nat) (T PL : Nat → Nat) :
    Array Table × Array Nat × Array Nat :=
  (Array.ofFn (n := cnt) fun i => tabT (unpack n w (T i.val)),
    Array.ofFn (n := cnt) fun i => parOf PL i.val, Array.ofFn (n := cnt) fun i => labOf PL i.val)

@[expose] def TabsOK (n w k : Nat) (G : Nat → Nat) (gens : Array Table) : Prop :=
  gens.size = k ∧ ∀ j < k, gens[j]! = tabT (unpack n w (G j)) ∧
    canonK n w (mask w) (n * w) (G j) = true

theorem strictB_eq'' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem findPt_spec {cnt i : Nat} {T Q POS : Nat → Nat} (h : findPtK cnt T Q POS i = true) :
    r32 POS i < cnt ∧ T (r32 POS i) = Q i := by
  unfold findPtK at h
  rw [strictB_eq''] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem slK_spec {cnt lo len : Nat} {P : Nat → Bool} (h : slK cnt P lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt → P i = true := by
  intro i h1 h2 h3
  have h' := allN_spec h (i - lo) (by omega)
  rw [strictB_eq''] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, Eq.mpr Nat.blt_eq h3] at h'
  exact h'

theorem tabT_get (a : Array Nat) (i : Nat) : (tabT a)[i]! = UInt32.ofNat a[i]! := by
  unfold tabT
  by_cases h : i < a.size
  · rw [getElem!_pos _ i (by simpa using h), getElem!_pos _ i h, Array.getElem_map]
  · rw [getElem!_neg _ i (by simpa using h), getElem!_neg _ i h]
    rfl

theorem ap_tabT (a : Array Nat) {i : Nat} (h : a[i]! < 2 ^ 32) : ap (tabT a) i = a[i]! := by
  unfold ap
  rw [tabT_get, UInt32.toNat_ofNat', Nat.mod_eq_of_lt h]

theorem unpack_lt {n w X i : Nat} (hX : canonK n w (mask w) (n * w) X = true) :
    (unpack n w X)[i]! < 2 ^ 32 := by
  unfold canonK at hX
  obtain ⟨hs, h2⟩ := (bAnd_iff _ _).1 hX
  obtain ⟨_, h3⟩ := (bAnd_iff _ _).1 h2
  have hn : n < 16777216 := by
    unfold szOK at hs
    exact Nat.le_of_ble_eq_true ((bAnd_iff _ _).1 hs).1
  by_cases hi : i < n
  · rw [getElem!_pos _ i (by simp [unpack, hi])]
    simp only [unpack, Array.getElem_ofFn]
    have := Nat.le_of_ble_eq_true (allN_spec h3 i hi)
    omega
  · rw [getElem!_neg _ i (by simp [unpack, hi])]
    exact Nat.two_pow_pos 32

theorem allLt_iff' (n : Nat) (p : Nat → Bool) : allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i.val i.isLt

theorem tblEq_unpack {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    tblEq n (tabT (unpack n w p)) (tabT (unpack n w q)) = Nat.beq p q := by
  rw [← eqA_unpack hp hq]
  unfold tblEq eqA
  rw [Bool.eq_iff_iff, CFSG.KS.TW.allIn_iff, allLt_iff']
  refine forall_congr' fun i => imp_congr_right fun _ => ?_
  rw [ap_tabT _ (unpack_lt hp), ap_tabT _ (unpack_lt hq)]

theorem compT_tabT {n : Nat} (a b : Array Nat) (hb : ∀ i < n, b[i]! < 2 ^ 32) :
    compT n (tabT a) (tabT b) = tabT (compA n a b) := by
  unfold compT compA
  apply Array.ext (by simp [tabT])
  intro i h1 _
  have hi : i < n := by simpa using h1
  simp only [Array.getElem_ofFn, tabT, Array.getElem_map]
  rw [← tabT, ← tabT, tabT_get, tabT_get, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (hb i hi)]

theorem idT_tabT (n : Nat) : idT n = tabT (idA n) := by
  unfold idT idA tabT
  apply Array.ext (by simp)
  intro i h1 _
  simp

theorem memT_of {n w cnt q : Nat} {T PL : Nat → Nat} {x : Table} (hq : q < cnt)
    (hx : tblEq n x (tabT (unpack n w (T q))) = true) :
    memT n (hRec n w cnt T PL).1 x = true := by
  unfold memT
  rw [Array.any_eq_true]
  exact ⟨q, by simpa [hRec] using hq, by simpa [hRec] using hx⟩

theorem lexLtK_iffH {a b c d : Nat} : lexLtK a b c d = true ↔ LexLt a b c d := by
  unfold lexLtK LexLt
  rw [CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.blt_dec,
    CFSG.KS.Raw.Orb.beq_dec, CFSG.KS.Raw.Orb.blt_dec]
  by_cases h : a < c
  · simp [h]
  · simp [h]

theorem penumPt_specH {n w m nw k cnt i : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
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
    exact lexLtK_iffH.1 h4
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
      rw [← lexLtK_iffH] at hl
      rw [hl] at h3
      exact absurd h3 (by decide)
  · rw [CFSG.KS.Raw.Orb.strictB_eq] at hs
    simp only [CFSG.KS.Raw.Orb.bIf_eq, Bool.and_eq_true, Nat.blt_eq] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    refine ⟨h1, Nat.eq_of_beq_eq_true h2, fun hc => ?_⟩
    have hc' : Nat.succ i < cnt := hc
    simp only [hc', ↓reduceIte] at h3
    exact Nat.blt_eq.mp h3

theorem inj_of_sortH {cnt : Nat} {T S SI : Nat → Nat}
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

theorem unpack_injH {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) (h : unpack n w p = unpack n w q) : p = q := by
  obtain ⟨-, hw, hp1, -⟩ := CFSG.KS.PF.canon_facts hp
  obtain ⟨-, -, hq1, -⟩ := CFSG.KS.PF.canon_facts hq
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hp1 hq1 fun i hi => ?_
  rw [← CFSG.KS.Raw.Orb.unpack_get hi, ← CFSG.KS.Raw.Orb.unpack_get hi, h]

theorem replay_ofH {n w k cnt cap : Nat} {conj : Bool} {G GI T PL POS SRT SRI : Nat → Nat}
    {step : Nat → CFSG.PSL3Four.Native.Tab → CFSG.PSL3Four.Native.Tab}
    {root : CFSG.PSL3Four.Native.Tab} {R : Nat}
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
  have sp := fun i (hi : i < cnt) => penumPt_specH (hp i hi)
  have hinjT : ∀ a < cnt, ∀ b < cnt, T a = T b → a = b :=
    inj_of_sortH (T := T) (S := r32 SRT) (SI := r32 SRI) fun i hi => (sp i hi).2.2.2
  refine ⟨⟨hc0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hcap⟩
  · rw [Nat.eq_of_beq_eq_true hT0, hroot]
  · unfold parOf
    rw [Nat.eq_of_beq_eq_true hPL0]
    rfl
  · unfold labOf
    rw [Nat.eq_of_beq_eq_true hPL0]
    rfl
  · intro a ha b hb e
    exact hinjT a ha b hb (unpack_injH (sp a ha).1 (sp b hb).1 e)
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

theorem hkGo_succ (w m X rem i h : Nat) :
    hkGo w m X (rem + 1) i h = hkGo w m X rem (i + 1) (hkStep h (pg w m X i)) :=
  CFSG.KS.PF.strictN_eqP (hkStep h (pg w m X i)) (fun h' => hkGo w m X rem (i + 1) h')

theorem hkGo_last (w m X : Nat) : ∀ rem i h,
    hkGo w m X (rem + 1) i h = hkStep (hkGo w m X rem i h) (pg w m X (i + rem))
  | 0, i, h => by rw [hkGo_succ]; rfl
  | rem + 1, i, h => by
    rw [hkGo_succ, hkGo_last w m X rem (i + 1), hkGo_succ, Nat.add_right_comm, Nat.add_assoc]

theorem hkey_tabT {n w X : Nat} (hX : canonK n w (mask w) (n * w) X = true) :
    (hkey n (tabT (unpack n w X))).toNat = hkeyK n w (mask w) X := by
  have step : ∀ i < n, ∀ a : UInt64,
      ((a ^^^ ((tabT (unpack n w X))[i]!).toUInt64) * 1099511628211).toNat =
        hkStep a.toNat (pg w (mask w) X i) := by
    intro i hi a
    rw [UInt64.toNat_mul, UInt64.toNat_xor, UInt32.toNat_toUInt64, tabT_get, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (unpack_lt hX), CFSG.KS.Raw.Orb.unpack_get hi]
    rfl
  have key : ∀ r ≤ n, (Nat.fold r (fun i _ h => (h ^^^ ((tabT (unpack n w X))[i]!).toUInt64) *
      1099511628211) (14695981039346656037 : UInt64)).toNat =
      hkGo w (mask w) X r 0 14695981039346656037 := by
    intro r
    induction r with
    | zero =>
      intro _
      rw [Nat.fold_zero]
      rfl
    | succ r ih =>
      intro hr
      rw [Nat.fold_succ, step r (by omega), ih (by omega), hkGo_last, Nat.zero_add]
  exact key n (Nat.le_refl n)

theorem strictInc_of_pairwiseH :
    ∀ {l : List Nat}, l.Pairwise (· < ·) → strictlyIncreasing l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self,
      strictInc_of_pairwiseH h.of_cons⟩

theorem hkeysDistinct_ofFn {n cnt : Nat} {U : Nat → Table}
    (hU : ∀ a < cnt, ∀ b < cnt, (hkey n (U a)).toNat = (hkey n (U b)).toNat → a = b) :
    hkeysDistinct n (Array.ofFn (n := cnt) fun i => U i.val).toList = true := by
  unfold hkeysDistinct
  apply strictInc_of_pairwiseH
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    ((Array.ofFn (n := cnt) fun i => U i.val).toList.map fun T => (hkey n T).toNat)
  have hd : ((Array.ofFn (n := cnt) fun i => U i.val).toList.map
      fun T => (hkey n T).toNat).Pairwise (· ≠ ·) := by
    rw [Array.toList_ofFn, List.map_ofFn, List.pairwise_ofFn]
    intro i j hij e
    exact absurd (hU i i.isLt j j.isLt e) (Nat.ne_of_lt hij)
  have hd' := (List.mergeSort_perm _ (fun a b : Nat => decide (a ≤ b))).pairwise_iff
    (R := (· ≠ ·)) (fun h => Ne.symm h) |>.2 hd
  refine (hs.and hd').imp fun ⟨h1, h2⟩ => ?_
  simp only [decide_eq_true_eq] at h1
  omega

theorem hkeyK_inj {n w cnt : Nat} {T HS HSI : Nat → Nat}
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true) :
    ∀ a < cnt, ∀ b < cnt, hkeyK n w (mask w) (T a) = hkeyK n w (mask w) (T b) → a = b := by
  refine inj_of_sortH (T := fun i => hkeyK n w (mask w) (T i)) (S := r32 HS) (SI := r32 HSI)
    fun i hi => ?_
  have h := hs i hi
  unfold hsortPtK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h3
  refine ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2, fun hc => ?_⟩
  simp only [Nat.blt_eq.mpr hc, ↓reduceIte] at h3
  exact Nat.blt_eq.mp h3

theorem allInH_of {lo hi : Nat} {p : Nat → Bool} (h : ∀ i, lo ≤ i → i < hi → p i = true) :
    allIn lo hi p = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro i _
  exact h _ (Nat.le_add_right _ _) (by have := i.isLt; omega)

theorem tblEqH_self (n : Nat) (S : Table) : tblEq n S S = true := by
  unfold tblEq
  rw [CFSG.KS.TW.allIn_iff]
  intro i _
  exact beq_self_eq_true _

theorem ofFnH_get {β : Type} [Inhabited β] {cnt i : Nat} (f : Nat → β) (hi : i < cnt) :
    (Array.ofFn (n := cnt) fun j => f j.val)[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem mulTree_of {n cnt : Nat} {gens : Array Table} {key : Table → UInt64} {U : Nat → Table}
    {par lab : Nat → Nat} {pos : Nat → Nat → Nat}
    (R : CFSG.KS.HBfs.HReplay key (fun j y => compT n y gens[j]!) gens.size (idT n) cnt U par lab
      pos) :
    mulTreeOK n gens (Array.ofFn (n := cnt) fun i => U i.val)
      (Array.ofFn (n := cnt) fun i => par i.val) (Array.ofFn (n := cnt) fun i => lab i.val) =
        true := by
  unfold mulTreeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.size_ofFn]
  refine ⟨⟨R.pos_cnt, ?_⟩, allInH_of fun i h1 h2 => ?_⟩
  · rw [ofFnH_get _ R.pos_cnt, R.root_eq]
    exact tblEqH_self n _
  · obtain ⟨a1, a2, a3⟩ := R.tree i (by omega) h2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [ofFnH_get _ h2, ofFnH_get _ h2, ofFnH_get _ h2, ofFnH_get _ (by omega), ← a3]
    exact ⟨⟨a1, a2⟩, tblEqH_self n _⟩

theorem conjTree_of {n cnt : Nat} {gens ginv : Array Table} {x : Table} {key : Table → UInt64}
    {U : Nat → Table} {par lab : Nat → Nat} {pos : Nat → Nat → Nat}
    (R : CFSG.KS.HBfs.HReplay key (fun j y => conjT n gens[j]! ginv[j]! y) gens.size x cnt U par
      lab pos) :
    conjTreeOK n gens ginv x (Array.ofFn (n := cnt) fun i => U i.val)
      (Array.ofFn (n := cnt) fun i => par i.val) (Array.ofFn (n := cnt) fun i => lab i.val) =
        true := by
  unfold conjTreeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.size_ofFn]
  refine ⟨⟨R.pos_cnt, ?_⟩, allInH_of fun i h1 h2 => ?_⟩
  · rw [ofFnH_get _ R.pos_cnt, R.root_eq]
    exact tblEqH_self n _
  · obtain ⟨a1, a2, a3⟩ := R.tree i (by omega) h2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [ofFnH_get _ h2, ofFnH_get _ h2, ofFnH_get _ h2, ofFnH_get _ (by omega), ← a3]
    exact ⟨⟨a1, a2⟩, tblEqH_self n _⟩

theorem compA_idA_unpack {n w t : Nat} (ht : canonK n w (mask w) (n * w) t = true) :
    compA n (idA n) (unpack n w t) = unpack n w t := by
  unfold canonK at ht
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 ht
  obtain ⟨_, h3⟩ := (bAnd_iff _ _).1 h2
  apply Array.ext (by simp [compA, unpack])
  intro i _ h2
  have hi : i < n := by simpa [unpack] using h2
  have hlt := Nat.le_of_ble_eq_true (allN_spec h3 i hi)
  simp only [compA, Array.getElem_ofFn]
  rw [← getElem!_pos (unpack n w t) i h2, CFSG.KS.Raw.Orb.unpack_get hi,
    getElem!_pos (idA n) _ (by simp [idA]; omega)]
  simp [idA]

theorem hreplay_of {n w k cnt cap R : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    {step : Nat → CFSG.PSL3Four.Native.Tab → CFSG.PSL3Four.Native.Tab}
    {stepα : Nat → Table → Table} {root : CFSG.PSL3Four.Native.Tab}
    (hstep : ∀ j < k, ∀ t, canonK n w (mask w) (n * w) t = true →
      step j (unpack n w t) = unpack n w (stepK n w (mask w) true G GI j t))
    (hf : ∀ j < k, ∀ t, canonK n w (mask w) (n * w) t = true →
      tabT (step j (unpack n w t)) = stepα j (tabT (unpack n w t)))
    (hroot : root = unpack n w R) (hh : penumHdK R cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true) :
    CFSG.KS.HBfs.HReplay (hkey n) stepα k (tabT root) cnt (fun i => tabT (unpack n w (T i)))
      (parOf PL) (labOf PL) (fun h j => r32 POS (h * k + j)) ∧ cnt ≤ cap := by
  obtain ⟨Rp, hcap⟩ := replay_ofH hstep hroot hh hp
  have hc : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true := fun i hi =>
    (penumPt_specH (hp i hi)).1
  refine ⟨CFSG.KS.HBfs.HReplay.of_replay Rp tabT (fun i hi j hj => hf j hj _ (hc i hi))
    fun a ha b hb e => hkeyK_inj hs a ha b hb ?_, hcap⟩
  rw [← hkey_tabT (hc a ha), ← hkey_tabT (hc b hb), e]

theorem mulH_sound {n w k cnt cap : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    {gens : Array Table} (hn : szOK n w = true) (hG : ∀ j < k, G j = pidn n w)
    (hg : TabsOK n w k GI gens) (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true) :
    mulClosureH n gens cap = hRec n w cnt T PL ∧
      mulTreeOK n gens (hRec n w cnt T PL).1 (hRec n w cnt T PL).2.1 (hRec n w cnt T PL).2.2 =
        true ∧
      hkeysDistinct n (hRec n w cnt T PL).1.toList = true := by
  obtain ⟨hk, hgj⟩ := hg
  have hid := (CFSG.KC.BfsPin.PP.id hn).1
  obtain ⟨R, hcap⟩ := hreplay_of (k := k) (step := fun j a => compA n a (unpack n w (GI j)))
    (stepα := fun j y => compT n y gens[j]!) (root := idA n)
    (fun j hj t ht => by
      change _ = unpack n w (pcomp n w (mask w) (pcomp n w (mask w) (G j) t) (GI j))
      rw [hG j hj, ← CFSG.KC.BfsPin.compA_unpack (CFSG.KC.BfsPin.canonK_pcomp hid ht)
        (hgj j hj).2, ← CFSG.KC.BfsPin.compA_unpack hid ht, ← CFSG.KC.BfsPin.idA_eq hn,
        compA_idA_unpack ht])
    (fun j hj t _ => by
      rw [(hgj j hj).1, compT_tabT _ _ fun x _ => unpack_lt (hgj j hj).2])
    (CFSG.KC.BfsPin.idA_eq hn) hh hp hs
  have e1 : mulClosureH n gens cap =
      CFSG.KS.HBfs.hbfs (hkey n) (fun l y => compT n y gens[l]!) gens.size (idT n) cap := rfl
  rw [hk, idT_tabT n] at e1
  unfold hRec
  refine ⟨e1.trans (CFSG.KS.HBfs.hbfs_replay R hcap), ?_, ?_⟩
  · subst hk
    rw [← idT_tabT n] at R
    have hm := mulTree_of R
    change mulTreeOK n gens (Array.ofFn (n := cnt) fun i => tabT (unpack n w (T i.val)))
      (Array.ofFn (n := cnt) fun i => parOf PL i.val)
      (Array.ofFn (n := cnt) fun i => labOf PL i.val) = true
    exact hm
  · exact hkeysDistinct_ofFn fun a ha b hb e => R.kinj a ha b hb (UInt64.toNat_inj.1 e)

theorem conjH_sound {n w k cnt cap X : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    {gens ginv : Array Table} {x : Table} (_hn : szOK n w = true) (hg : TabsOK n w k G gens)
    (hgi : TabsOK n w k GI ginv) (hx : x = tabT (unpack n w X))
    (hh : penumHdK X cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true) :
    conjClosureH n gens ginv x cap = hRec n w cnt T PL ∧
      conjTreeOK n gens ginv x (hRec n w cnt T PL).1 (hRec n w cnt T PL).2.1
        (hRec n w cnt T PL).2.2 = true ∧
      hkeysDistinct n (hRec n w cnt T PL).1.toList = true := by
  subst hx
  obtain ⟨hk, hgj⟩ := hg
  obtain ⟨-, hgij⟩ := hgi
  obtain ⟨R, hcap⟩ := hreplay_of (k := k)
    (step := fun j a => compA n (compA n (unpack n w (G j)) a) (unpack n w (GI j)))
    (stepα := fun j y => conjT n gens[j]! ginv[j]! y) (root := unpack n w X)
    (fun j hj t ht => by
      change _ = unpack n w (pcomp n w (mask w) (pcomp n w (mask w) (G j) t) (GI j))
      rw [CFSG.KC.BfsPin.compA_unpack (hgj j hj).2 ht]
      exact CFSG.KC.BfsPin.compA_unpack (CFSG.KC.BfsPin.canonK_pcomp (hgj j hj).2 ht)
        (hgij j hj).2)
    (fun j hj t ht => by
      unfold conjT
      rw [(hgj j hj).1, (hgij j hj).1, compT_tabT _ _ fun x _ => unpack_lt ht,
        compT_tabT _ _ fun x _ => unpack_lt (hgij j hj).2])
    rfl hh hp hs
  have e1 : conjClosureH n gens ginv (tabT (unpack n w X)) cap =
      CFSG.KS.HBfs.hbfs (hkey n) (fun l y => conjT n gens[l]! ginv[l]! y) gens.size
        (tabT (unpack n w X)) cap := rfl
  rw [hk] at e1
  unfold hRec
  refine ⟨e1.trans (CFSG.KS.HBfs.hbfs_replay R hcap), ?_, ?_⟩
  · subst hk
    have hm := conjTree_of R
    change conjTreeOK n gens ginv (tabT (unpack n w X))
      (Array.ofFn (n := cnt) fun i => tabT (unpack n w (T i.val)))
      (Array.ofFn (n := cnt) fun i => parOf PL i.val)
      (Array.ofFn (n := cnt) fun i => labOf PL i.val) = true
    exact hm
  · exact hkeysDistinct_ofFn fun a ha b hb e => R.kinj a ha b hb (UInt64.toNat_inj.1 e)

end CFSG.KS.MulH

end
