module

public import Certificates.Data.Kernel.Spor.PChain
public import CFSG.Certificates.Kernel.Spor.TBfsSound
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.PointChainCard

public section

namespace CFSG.KS.PC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.Perm.Native CFSG.Sporadic.Th.Native

@[expose] noncomputable def permOfT (n : Nat) (t : Table) : Equiv.Perm (Fin n) := by
  classical
  exact if h : (∀ x < n, ap t x < n) ∧ Function.Injective (fun x : Fin n => ap t x.val) then
    Equiv.ofBijective (fun x : Fin n => ⟨ap t x.val, h.1 x.val x.isLt⟩)
      ((Finite.injective_iff_bijective).1 fun a b e => h.2 (by simpa using e))
  else 1

structure ChainHyp (n NL m : Nat) (letters : Array Table) (base Q qb : Array Nat)
    (L : Nat → Nat → Nat) (B : Nat → Nat) (QL : List Nat) (QB CNT : Nat → Nat)
    (PTS POS PAR LAB TI : Nat → Nat → Nat) : Prop where
  letters : letters.size = NL ∧ ∀ l < NL, ∀ x < n, ap letters[l]! x = L l x
  inv : NL % 2 = 0 ∧ invK L n NL = true
  base : base.size = m ∧ ∀ i < m, base[i]! = B i ∧ B i < n
  chk : Q.toList = QL ∧ (∀ t < QL.length, QL.getD t 0 < n) ∧ qb.size = m ∧
    ∀ i < m, qb[i]! = QB i ∧ QB i < QL.length ∧ QL.getD (QB i) 0 = B i
  tree : ∀ i < m, tbfsHdK n (B i) (CNT i) (PTS i) (POS i) (PAR i) (LAB i) = true ∧
    ∀ k < CNT i, tbfsPtK n (CNT i) (lvK L B NL i).length L (lvAt L B NL i) (PTS i) (POS i)
      (PAR i) (LAB i) (TI i) k = true

theorem getElem!_eq_getD (a : Array Nat) (i : Nat) : a[i]! = a.toList.getD i 0 := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [getElem!_neg a i h, List.getD_eq_default _ _ (by simpa using h)]
    rfl

theorem parAll_of {n chunks : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    parAll n chunks p = true := by
  unfold parAll
  rw [List.all_eq_true]
  intro t ht
  simp only [List.mem_map, List.mem_range] at ht
  obtain ⟨j, -, rfl⟩ := ht
  change allStep j (chunks + 1) n p = true
  unfold allStep
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨k, hk⟩ _
  apply h
  have h1 : (k + 1) * (chunks + 1) ≤ n + (chunks + 1) - 1 - j :=
    (Nat.le_div_iff_mul_le (by omega)).1 hk
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm] at h1
  generalize (chunks + 1) * k = t at h1 ⊢
  omega

theorem mapK_eq (f : Nat → Nat) (q : List Nat) : mapK f q = q.map f := by
  induction q with
  | nil => rfl
  | cons x q ih =>
    change f x :: mapK f q = _
    rw [ih]
    rfl

theorem listEqK_iff (a b : List Nat) : listEqK a b = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [listEqK]
  | cons x a ih =>
    cases b with
    | nil => simp [listEqK]
    | cons y b =>
      change Bool.rec (motive := fun _ => Bool) false (listEqK a b) (Nat.beq x y) = true ↔ _
      rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, ih, Nat.beq_eq, List.cons.injEq]

theorem map_self {l : List Nat} {f : Nat → Nat} (h : l.map f = l) : ∀ x ∈ l, f x = x := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.map_cons, List.cons.injEq] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

theorem prod_range_map (m : Nat) (f : Nat → Nat) :
    ((List.range m).map f).prod = ∏ i ∈ Finset.range m, f i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
    simp

theorem xor_one_even (j : Nat) : Nat.xor (2 * j) 1 = 2 * j + 1 := by
  change (2 * j) ^^^ 1 = 2 * j + 1
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, show (2 * j + 1) / 2 = j by omega]
    simp

theorem xor_one_odd (j : Nat) : Nat.xor (2 * j + 1) 1 = 2 * j := by
  change (2 * j + 1) ^^^ 1 = 2 * j
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, show (2 * j + 1) / 2 = j by omega]
    simp

theorem xor_one (l : Nat) : Nat.xor l 1 = invL l := by
  unfold invL
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · rw [xor_one_even, ite_eq_left (by omega)]
  · rw [xor_one_odd, ite_eq_right (by omega)]
    omega

theorem pair_inv {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n)
    (hgf : ∀ x < n, g (f x) = x) : ∀ y < n, f (g y) = y := by
  intro y hy
  have hinj : Function.Injective (fun x : Fin n => (⟨f x, hf x x.2⟩ : Fin n)) := by
    intro a b e
    apply Fin.ext
    have := congrArg (fun z : Fin n => g z.val) e
    simpa [hgf a a.2, hgf b b.2] using this
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨y, hy⟩
  have hx' : f x = y := congrArg Fin.val hx
  rw [← hx', hgf x x.2]

section

variable {L : Nat → Nat → Nat} {B : Nat → Nat} {NL : Nat}

theorem mem_lvK {l i : Nat} : l ∈ lvK L B NL i ↔ l < NL ∧ ∀ j < i, L l (B j) = B j := by
  unfold lvK
  rw [List.mem_filter, List.mem_range, Raw.Orb.allN_iff]
  simp [Nat.beq_eq]

theorem lvAt_mem {i t : Nat} (ht : t < (lvK L B NL i).length) : lvAt L B NL i t ∈ lvK L B NL i := by
  unfold lvAt
  rw [List.getD_eq_getElem _ _ ht]
  exact List.getElem_mem ht

theorem exists_lvAt {i l : Nat} (hl : l ∈ lvK L B NL i) :
    ∃ t < (lvK L B NL i).length, lvAt L B NL i t = l := by
  obtain ⟨t, ht, e⟩ := List.getElem_of_mem hl
  exact ⟨t, ht, by unfold lvAt; rw [List.getD_eq_getElem _ _ ht, e]⟩

end

section

variable {n NL m : Nat} {letters : Array Table} {base Q qb : Array Nat}
  {L : Nat → Nat → Nat} {B : Nat → Nat} {QL : List Nat} {QB CNT : Nat → Nat}
  {PTS POS PAR LAB TI : Nat → Nat → Nat}

@[expose] noncomputable def trK (n : Nat) (CNT : Nat → Nat) (PTS POS PAR LAB : Nat → Nat → Nat)
    (i : Nat) : Tree :=
  tbfsRec n (CNT i) (PTS i) (POS i) (PAR i) (LAB i)

theorem invK_spec (hk : invK L n NL = true) {j : Nat} (hj : j < NL / 2) {x : Nat} (hx : x < n) :
    L (2 * j) x < n ∧ L (2 * j + 1) x < n ∧ L (2 * j + 1) (L (2 * j) x) = x := by
  unfold invK at hk
  have := Raw.Orb.allN_iff.1 (Raw.Orb.allN_iff.1 hk j hj) x hx
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  exact this

theorem letter_facts (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {l : Nat} (hl : l < NL) :
    invL l < NL ∧ invL (invL l) = l ∧ (∀ x < n, L l x < n) ∧ ∀ x < n, L (invL l) (L l x) = x := by
  have hNL := H.inv.1
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · have hj : j < NL / 2 := by omega
    have e : invL (2 * j) = 2 * j + 1 := by unfold invL; rw [ite_eq_left (by omega)]
    have e' : invL (2 * j + 1) = 2 * j := by unfold invL; rw [ite_eq_right (by omega)]; omega
    rw [e, e']
    exact ⟨by omega, rfl, fun x hx => (invK_spec H.inv.2 hj hx).1,
      fun x hx => (invK_spec H.inv.2 hj hx).2.2⟩
  · have hj : j < NL / 2 := by omega
    have e : invL (2 * j + 1) = 2 * j := by unfold invL; rw [ite_eq_right (by omega)]; omega
    have e' : invL (2 * j) = 2 * j + 1 := by unfold invL; rw [ite_eq_left (by omega)]
    rw [e, e']
    exact ⟨by omega, rfl, fun x hx => (invK_spec H.inv.2 hj hx).2.1,
      pair_inv (fun x hx => (invK_spec H.inv.2 hj hx).1)
        (fun x hx => (invK_spec H.inv.2 hj hx).2.2)⟩

theorem ap_letter (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {l x : Nat} (hl : l < NL) (hx : x < n) : ap letters[l]! x = L l x :=
  H.letters.2 l hl x hx

theorem Q_lt (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI) :
    ∀ x ∈ Q, x < n := by
  intro x hx
  rw [← Array.mem_toList_iff, H.chk.1] at hx
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
  have := H.chk.2.1 t ht
  rwa [List.getD_eq_getElem _ _ ht] at this

theorem QL_lt (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI) :
    ∀ x ∈ QL, x < n := by
  intro x hx
  rw [← H.chk.1, Array.mem_toList_iff] at hx
  exact Q_lt H x hx

theorem rep_of (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {i : Nat} (hi : i < m) :
    Rep n (B i) (CNT i) (lvK L B NL i).length L (lvAt L B NL i) (PTS i) (POS i) (PAR i) (LAB i)
      (TI i) :=
  ⟨hd_spec (H.tree i hi).1, fun k hk => pt_spec ((H.tree i hi).2 k hk)⟩

theorem lab_mem (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {i k : Nat} (hi : i < m) (hk : k < CNT i) (h0 : 0 < k) :
    r32 (LAB i) k ∈ lvK L B NL i := by
  obtain ⟨-, a2, a3, -, -⟩ := ((rep_of H hi).pt k hk).tree h0
  rw [a3]
  exact lvAt_mem a2

theorem levelLetters_eq (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI) :
    ∀ i ≤ m, levelLetters letters base i = (lvK L B NL i).toArray
  | 0, _ => by
    rw [levelLetters, lvK, List.filter_eq_self.2 fun l _ =>
      Raw.Orb.allN_iff.2 fun j hj => absurd hj (Nat.not_lt_zero _), H.letters.1, List.toArray_range]
  | i + 1, hi => by
    rw [levelLetters, levelLetters_eq H i (by omega), List.filter_toArray]
    congr 1
    unfold lvK
    rw [List.filter_filter]
    apply List.filter_congr
    intro l hl
    rw [List.mem_range] at hl
    obtain ⟨hb, hB⟩ := H.base.2 i (by omega)
    rw [Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq, Raw.Orb.allN_iff, Raw.Orb.allN_iff, hb,
      ap_letter H hl hB]
    simp only [Nat.beq_eq]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h2 j hj
      · exact h1
    · intro h
      exact ⟨h i (by omega), fun j hj => h j (by omega)⟩

theorem tree_eq (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {i : Nat} (hi : i < m) :
    treeBFS n (B i) letters (lvK L B NL i).toArray = trK n CNT PTS POS PAR LAB i ∧
      treeOK n (B i) (trK n CNT PTS POS PAR LAB i) letters (lvK L B NL i).toArray = true := by
  refine tbfsK_sound (r := (lvK L B NL i).length) (L := L) (LV := lvAt L B NL i)
    ⟨by simp, fun t ht => ⟨?_, ?_, fun x hx => ?_⟩⟩ (H.tree i hi).1 (H.tree i hi).2
  · rw [getElem!_eq_getD, List.toList_toArray]
    rfl
  · rw [H.letters.1]
    exact (mem_lvK.1 (lvAt_mem ht)).1
  · exact ap_letter H (mem_lvK.1 (lvAt_mem ht)).1 hx

theorem chainTrees_eq (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI) :
    chainTrees n letters base = Array.ofFn (n := m) fun i => trK n CNT PTS POS PAR LAB i.val := by
  unfold chainTrees
  apply Array.ext
  · simp [H.base.1]
  · intro i h1 h2
    have hi : i < m := by simpa using h2
    rw [Array.getElem_ofFn, Array.getElem_ofFn, (H.base.2 i hi).1,
      levelLetters_eq H i hi.le, (tree_eq H hi).1]

@[expose] def actN (g : Equiv.Perm (Fin n)) (x : Nat) : Nat :=
  if hx : x < n then (g ⟨x, hx⟩ : Nat) else x

theorem actN_of_lt (g : Equiv.Perm (Fin n)) {x : Nat} (hx : x < n) : actN g x = g ⟨x, hx⟩ := by
  unfold actN
  rw [dite_eq_left hx]

theorem actN_lt (g : Equiv.Perm (Fin n)) {x : Nat} (hx : x < n) : actN g x < n := by
  rw [actN_of_lt g hx]
  exact (g ⟨x, hx⟩).isLt

theorem actN_fin (g : Equiv.Perm (Fin n)) (x : Fin n) : actN g x = g x := actN_of_lt g x.isLt

theorem actN_mul (g h : Equiv.Perm (Fin n)) (x : Nat) : actN (g * h) x = actN g (actN h x) := by
  by_cases hx : x < n
  · rw [actN_of_lt _ hx, actN_of_lt _ hx, actN_of_lt _ (h ⟨x, hx⟩).isLt]
    rfl
  · unfold actN
    rw [dite_eq_right hx, dite_eq_right hx, dite_eq_right hx]

theorem actN_one (x : Nat) : actN (1 : Equiv.Perm (Fin n)) x = x := by
  unfold actN
  split <;> rfl

theorem map_actN_one (q : Array Nat) : q.map (actN (1 : Equiv.Perm (Fin n))) = q := by
  have : actN (1 : Equiv.Perm (Fin n)) = id := funext actN_one
  rw [this, Array.map_id]

@[expose] noncomputable def sig (n : Nat) (letters : Array Table) (l : Nat) : Equiv.Perm (Fin n) :=
  permOfT n letters[l]!

theorem permOfT_val {t : Table} (hr : ∀ x < n, ap t x < n)
    (hinj : ∀ x < n, ∀ y < n, ap t x = ap t y → x = y) (x : Fin n) :
    (permOfT n t x : Nat) = ap t x := by
  unfold permOfT
  rw [dite_eq_left ⟨hr, fun a b e => Fin.ext (hinj a a.2 b b.2 e)⟩]
  rfl

theorem sig_val (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {l : Nat} (hl : l < NL) (x : Fin n) : (sig n letters l x : Nat) = L l x := by
  obtain ⟨-, -, hr, hinv⟩ := letter_facts H hl
  unfold sig
  rw [permOfT_val (fun x hx => by rw [ap_letter H hl hx]; exact hr x hx)
    (fun x hx y hy e => by
      rw [ap_letter H hl hx, ap_letter H hl hy] at e
      rw [← hinv x hx, ← hinv y hy, e]), ap_letter H hl x.isLt]

theorem actN_sig (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {l x : Nat} (hl : l < NL) (hx : x < n) : actN (sig n letters l) x = L l x := by
  rw [actN_of_lt _ hx, sig_val H hl]

theorem actN_sig_inv (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {l x : Nat} (hl : l < NL) (hx : x < n) : actN (sig n letters l)⁻¹ x = L (invL l) x := by
  obtain ⟨hi, hii, -, -⟩ := letter_facts H hl
  obtain ⟨-, -, hr', hinv'⟩ := letter_facts H hi
  rw [hii] at hinv'
  have hy : L (invL l) x < n := hr' x hx
  have e : (sig n letters l)⁻¹ ⟨x, hx⟩ = ⟨L (invL l) x, hy⟩ := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    apply Fin.ext
    rw [sig_val H hl]
    exact (hinv' x hx).symm
  rw [actN_of_lt _ hx, e]

theorem sig_mem (l : Fin NL) :
    sig n letters l.val ∈ Subgroup.closure (Set.range fun l : Fin NL => permOfT n letters[l.val]!) :=
  Subgroup.subset_closure ⟨l, rfl⟩

@[expose] noncomputable def tw (σ : Nat → Equiv.Perm (Fin n)) (PAR LAB : Nat → Nat) :
    Nat → Equiv.Perm (Fin n)
  | k => if _h : 0 < k ∧ r32 PAR k < k then σ (r32 LAB k) * tw σ PAR LAB (r32 PAR k) else 1
termination_by k => k
decreasing_by exact _h.2

theorem tw_eq (σ : Nat → Equiv.Perm (Fin n)) (PAR LAB : Nat → Nat) (k : Nat) :
    tw σ PAR LAB k =
      if 0 < k ∧ r32 PAR k < k then σ (r32 LAB k) * tw σ PAR LAB (r32 PAR k) else 1 := by
  rw [tw]
  split <;> simp_all

noncomputable abbrev twL (n : Nat) (letters : Array Table) (PAR LAB : Nat → Nat → Nat)
    (i : Nat) : Nat → Equiv.Perm (Fin n) :=
  tw (sig n letters) (PAR i) (LAB i)

theorem bnd_map {q : Array Nat} {f : Nat → Nat} (hq : ∀ x ∈ q, x < n) (hf : ∀ x < n, f x < n) :
    ∀ x ∈ q.map f, x < n := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Array.mem_map.1 hx
  exact hf y (hq y hy)

theorem walk_eq (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {i : Nat} (hi : i < m) : ∀ k < CNT i, ∀ q : Array Nat, (∀ x ∈ q, x < n) →
      walk (trK n CNT PTS POS PAR LAB i) letters k q = q.map (actN (twL n letters PAR LAB i k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk q hq
    have hpar : ap (trK n CNT PTS POS PAR LAB i).par k = r32 (PAR i) k := ap_ofFn hk
    have hlab : ap (trK n CNT PTS POS PAR LAB i).lab k = r32 (LAB i) k := ap_ofFn hk
    rw [walk, hpar, hlab, twL, tw_eq]
    by_cases hc : 0 < k ∧ r32 (PAR i) k < k
    · rw [dite_eq_left hc, ite_eq_left hc, CFSG.KS.TW.apT_map, ih _ hc.2 (by omega) q hq, Array.map_map]
      apply Array.map_eq_map_iff.2
      intro x hx
      have hl := (mem_lvK.1 (lab_mem H hi hk hc.1)).1
      simp only [Function.comp_apply, actN_mul]
      rw [ap_letter H hl (actN_lt _ (hq x hx)), actN_sig H hl (actN_lt _ (hq x hx))]
    · rw [dite_eq_right hc, ite_eq_right hc, map_actN_one]

theorem walkInv_eq (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {i : Nat} (hi : i < m) : ∀ k < CNT i, ∀ q : Array Nat, (∀ x ∈ q, x < n) →
      walkInv (trK n CNT PTS POS PAR LAB i) letters k q =
        q.map (actN (twL n letters PAR LAB i k)⁻¹) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk q hq
    have hpar : ap (trK n CNT PTS POS PAR LAB i).par k = r32 (PAR i) k := ap_ofFn hk
    have hlab : ap (trK n CNT PTS POS PAR LAB i).lab k = r32 (LAB i) k := ap_ofFn hk
    rw [walkInv, hpar, hlab, twL, tw_eq]
    by_cases hc : 0 < k ∧ r32 (PAR i) k < k
    · have hl := (mem_lvK.1 (lab_mem H hi hk hc.1)).1
      obtain ⟨hil, -, -, -⟩ := letter_facts H hl
      obtain ⟨-, -, hr, -⟩ := letter_facts H hil
      rw [dite_eq_left hc, ite_eq_left hc, CFSG.KS.TW.apT_map,
        ih _ hc.2 (by omega) _ (bnd_map hq fun x hx => by rw [ap_letter H hil hx]; exact hr x hx),
        Array.map_map]
      apply Array.map_eq_map_iff.2
      intro x hx
      simp only [Function.comp_apply, mul_inv_rev, actN_mul]
      rw [ap_letter H hil (hq x hx), actN_sig_inv H hl (hq x hx)]
    · rw [dite_eq_right hc, ite_eq_right hc, inv_one, map_actN_one]

theorem walkF_succ (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (f k : Nat) (q : List Nat) :
    walkF L PAR LAB (f + 1) k q = if (0 < k ∧ r32 PAR k < k) then
      mapK (L (r32 LAB k)) (walkF L PAR LAB f (r32 PAR k) q) else q := by
  change Bool.rec (motive := fun _ => List Nat) q (mapK (L (r32 LAB k)) (walkF L PAR LAB f (r32 PAR k) q))
    (Bool.rec (motive := fun _ => Bool) false (Nat.blt (r32 PAR k) k) (Nat.blt 0 k)) = _
  rw [Raw.Orb.bAnd_eq]
  by_cases hc : 0 < k ∧ r32 PAR k < k
  · rw [ite_eq_left hc, show (Nat.blt 0 k && Nat.blt (r32 PAR k) k) = true by simp [Nat.blt_eq, hc]]
  · rw [ite_eq_right hc, show (Nat.blt 0 k && Nat.blt (r32 PAR k) k) = false from
      Bool.eq_false_iff.2 fun h => hc (by simpa [Nat.blt_eq] using h)]

theorem walkInvF_succ (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (f k : Nat) (q : List Nat) :
    walkInvF L PAR LAB (f + 1) k q = if (0 < k ∧ r32 PAR k < k) then
      walkInvF L PAR LAB f (r32 PAR k) (mapK (L (Nat.xor (r32 LAB k) 1)) q) else q := by
  change Bool.rec (motive := fun _ => List Nat) q
    (walkInvF L PAR LAB f (r32 PAR k) (mapK (L (Nat.xor (r32 LAB k) 1)) q))
    (Bool.rec (motive := fun _ => Bool) false (Nat.blt (r32 PAR k) k) (Nat.blt 0 k)) = _
  rw [Raw.Orb.bAnd_eq]
  by_cases hc : 0 < k ∧ r32 PAR k < k
  · rw [ite_eq_left hc, show (Nat.blt 0 k && Nat.blt (r32 PAR k) k) = true by simp [Nat.blt_eq, hc]]
  · rw [ite_eq_right hc, show (Nat.blt 0 k && Nat.blt (r32 PAR k) k) = false from
      Bool.eq_false_iff.2 fun h => hc (by simpa [Nat.blt_eq] using h)]

theorem walkF_eq (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {i : Nat} (hi : i < m) : ∀ f k, k < CNT i → k ≤ f → ∀ q : List Nat, (∀ x ∈ q, x < n) →
      walkF L (PAR i) (LAB i) f k q = q.map (actN (twL n letters PAR LAB i k)) := by
  intro f
  induction f with
  | zero =>
    intro k _ hkf q _
    have : k = 0 := by omega
    subst this
    rw [twL, tw_eq, ite_eq_right (by omega)]
    have : actN (1 : Equiv.Perm (Fin n)) = id := funext actN_one
    rw [this, List.map_id]
    rfl
  | succ f ih =>
    intro k hk hkf q hq
    rw [walkF_succ, twL, tw_eq]
    by_cases hc : 0 < k ∧ r32 (PAR i) k < k
    · rw [ite_eq_left hc, ite_eq_left hc, mapK_eq, ih _ (by omega) (by omega) q hq, List.map_map]
      apply List.map_congr_left
      intro x hx
      have hl := (mem_lvK.1 (lab_mem H hi hk hc.1)).1
      simp only [Function.comp_apply, actN_mul]
      rw [actN_sig H hl (actN_lt _ (hq x hx))]
    · rw [ite_eq_right hc, ite_eq_right hc]
      have : actN (1 : Equiv.Perm (Fin n)) = id := funext actN_one
      rw [this, List.map_id]

theorem walkInvF_eq (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {i : Nat} (hi : i < m) : ∀ f k, k < CNT i → k ≤ f → ∀ q : List Nat, (∀ x ∈ q, x < n) →
      walkInvF L (PAR i) (LAB i) f k q = q.map (actN (twL n letters PAR LAB i k)⁻¹) := by
  intro f
  induction f with
  | zero =>
    intro k _ hkf q _
    have : k = 0 := by omega
    subst this
    rw [twL, tw_eq, ite_eq_right (by omega), inv_one]
    have : actN (1 : Equiv.Perm (Fin n)) = id := funext actN_one
    rw [this, List.map_id]
    rfl
  | succ f ih =>
    intro k hk hkf q hq
    rw [walkInvF_succ, twL, tw_eq]
    by_cases hc : 0 < k ∧ r32 (PAR i) k < k
    · have hl := (mem_lvK.1 (lab_mem H hi hk hc.1)).1
      obtain ⟨hil, -, -, -⟩ := letter_facts H hl
      obtain ⟨-, -, hr, -⟩ := letter_facts H hil
      rw [ite_eq_left hc, ite_eq_left hc, mapK_eq, xor_one,
        ih _ (by omega) (by omega) _ (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          exact hr y (hq y hy)), List.map_map]
      apply List.map_congr_left
      intro x hx
      simp only [Function.comp_apply, mul_inv_rev, actN_mul]
      rw [actN_sig_inv H hl (hq x hx)]
    · rw [ite_eq_right hc, ite_eq_right hc, inv_one]
      have : actN (1 : Equiv.Perm (Fin n)) = id := funext actN_one
      rw [this, List.map_id]

theorem lab_lt (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {l : Nat} (hl : l < NL) : ∀ x < n, L l x < n := (letter_facts H hl).2.2.1

theorem tupleEq_iff_toList {a b : Array Nat} : tupleEq a b = true ↔ a.toList = b.toList := by
  rw [CFSG.KS.TW.tupleEq_iff]
  constructor
  · rintro ⟨hs, he⟩
    congr 1
    apply Array.ext hs
    intro t h1 h2
    rw [← getElem!_pos a t h1, ← getElem!_pos b t h2, he t h2]
  · intro e
    rw [Array.ext' e]
    exact ⟨rfl, fun _ _ => rfl⟩

noncomputable abbrev trees (n m : Nat) (CNT : Nat → Nat)
    (PTS POS PAR LAB : Nat → Nat → Nat) : Array Tree :=
  Array.ofFn (n := m) fun i => trK n CNT PTS POS PAR LAB i.val

theorem trees_get {i : Nat} (hi : i < m) :
    (trees n m CNT PTS POS PAR LAB)[i]! = trK n CNT PTS POS PAR LAB i := by
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem pos_ap {i y : Nat} (hy : y < n) : ap (trK n CNT PTS POS PAR LAB i).pos y = r32 (POS i) y :=
  ap_ofFn hy

theorem pts_ap {i k : Nat} (hk : k < CNT i) :
    ap (trK n CNT PTS POS PAR LAB i).pts k = r32 (PTS i) k :=
  ap_ofFn hk

theorem pts_size (i : Nat) : (trK n CNT PTS POS PAR LAB i).pts.size = CNT i := by
  unfold trK tbfsRec
  rw [Array.size_ofFn]

theorem sift_eq (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI) :
    ∀ d l, l + d = m → ∀ img : Array Nat, (∀ x ∈ img, x < n) →
      Perm.Native.sift (trees n m CNT PTS POS PAR LAB) letters qb Q l img =
        siftF L POS PAR LAB CNT QB QL d l img.toList
  | 0, l, hl, img, _ => by
    rw [Perm.Native.sift, dite_eq_right (by simp; omega)]
    change tupleEq img Q = listEqK img.toList QL
    rw [Bool.eq_iff_iff, tupleEq_iff_toList, listEqK_iff, H.chk.1]
  | d + 1, l, hl, img, himg => by
    have hlm : l < m := by omega
    rw [Perm.Native.sift, dite_eq_left (by simp; omega)]
    simp only [Array.getElem_ofFn]
    change _ = strictB (r32 (POS l) (img.toList.getD (QB l) 0)) fun k =>
      Bool.rec (motive := fun _ => Bool) false
        (siftF L POS PAR LAB CNT QB QL d (l + 1) (walkInvK L (PAR l) (LAB l) k img.toList))
        (Nat.blt k (CNT l))
    rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, (H.chk.2.2.2 l hlm).1, ← getElem!_eq_getD]
    have hy : img[QB l]! < n := by
      by_cases h : QB l < img.size
      · rw [getElem!_pos img _ h]
        exact himg _ (Array.getElem_mem h)
      · rw [getElem!_neg img _ h]
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) (H.base.2 l hlm).2
    rw [pos_ap hy, pts_size]
    by_cases hk : r32 (POS l) img[QB l]! < CNT l
    · rw [walkInv_eq H hlm _ hk img himg, sift_eq H d (l + 1) (by omega) _ (bnd_map himg fun x hx => actN_lt _ hx)]
      unfold walkInvK
      rw [walkInvF_eq H hlm _ _ hk (Nat.le_refl _) _ fun x hx => himg x (Array.mem_toList_iff.1 hx),
        Array.toList_map]
      simp [hk, Nat.blt_eq]
    · simp [hk, Nat.blt_eq]

theorem schreierAt_eq (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {i l k : Nat} (hi : i < m) (hl : l ∈ lvK L B NL i) (hk : k < CNT i) :
    schreierAt (trees n m CNT PTS POS PAR LAB) letters qb Q i l k =
      schK L PTS POS PAR LAB CNT QB QL m i l k := by
  have hl' : l < NL := (mem_lvK.1 hl).1
  have P := (rep_of H hi).pt k hk
  have hy : L l (r32 (PTS i) k) < n := lab_lt H hl' _ P.lt
  unfold schreierAt schK
  rw [trees_get hi]
  simp only
  rw [pts_ap hk, ap_letter H hl' P.lt, pos_ap hy, Raw.Orb.strictB_eq,
    Raw.Orb.bAnd_eq, pts_size]
  by_cases hky : r32 (POS i) (L l (r32 (PTS i) k)) < CNT i
  · have hQ := Q_lt H
    have hb1 := bnd_map hQ fun x hx => actN_lt (twL n letters PAR LAB i k) hx
    have hb2 := bnd_map (f := ap letters[l]!) hb1 fun x hx => by rw [ap_letter H hl' hx]; exact lab_lt H hl' x hx
    rw [walk_eq H hi k hk Q hQ, CFSG.KS.TW.apT_map, walkInv_eq H hi _ hky _ hb2,
      sift_eq H (m - (i + 1)) (i + 1) (by omega) _ (bnd_map hb2 fun x hx => actN_lt _ hx)]
    unfold siftK walkK walkInvK
    have hQL := QL_lt H
    rw [walkF_eq H hi k k hk (Nat.le_refl _) QL hQL, mapK_eq,
      walkInvF_eq H hi _ _ hky (Nat.le_refl _) _ (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact lab_lt H hl' _ (actN_lt _ (hQL z hz)))]
    simp only [Array.toList_map, H.chk.1, List.map_map, hky, decide_true, Bool.true_and]
    rw [show Nat.blt (r32 (POS i) (L l (r32 (PTS i) k))) (CNT i) = true from by simpa [Nat.blt_eq] using hky,
      Bool.true_and]
    congr 1
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply]
    rw [ap_letter H hl' (actN_lt _ (hQL x hx))]
  · simp [hky, Nat.blt_eq]

theorem chainOK_of (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hS : ∀ i < m, ∀ l ∈ lvK L B NL i, ∀ k < CNT i,
      schreierAt (trees n m CNT PTS POS PAR LAB) letters qb Q i l k = true)
    (hT : ∀ l ∈ lvK L B NL m, ∀ x ∈ QL, L l x = x) :
    chainTrees n letters base =
        Array.ofFn (n := m) (fun i => tbfsRec n (CNT i.val) (PTS i.val) (POS i.val) (PAR i.val)
          (LAB i.val)) ∧
      ∀ chunks, chainOK n letters base Q qb (chainTrees n letters base) chunks = true := by
  have hct := chainTrees_eq H
  refine ⟨hct, fun chunks => ?_⟩
  rw [hct]
  change chainOK n letters base Q qb (trees n m CNT PTS POS PAR LAB) chunks = true
  obtain ⟨hNL, hL⟩ := H.letters
  obtain ⟨hbs, hb⟩ := H.base
  obtain ⟨hQ, hQlt, hqbs, hqb⟩ := H.chk
  have hQs : Q.size = QL.length := by rw [← hQ, Array.length_toList]
  have hQget : ∀ t, Q[t]! = QL.getD t 0 := fun t => by rw [getElem!_eq_getD, hQ]
  unfold chainOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allIn_iff, hbs, hNL]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨H.inv.1, fun j hj => ?_⟩, by simp⟩, hqbs⟩, fun t ht => ?_⟩, fun i hi => ?_⟩,
    fun i hi => ?_⟩, fun i hi => ?_⟩, ?_⟩
  ·
    unfold invOK
    rw [allIn_iff]
    intro x hx
    obtain ⟨h1, -, h3⟩ := invK_spec H.inv.2 hj hx
    rw [ap_letter H (by omega) hx, ap_letter H (by omega) h1, h3, beq_self_eq_true]
  · rw [hQget]
    exact hQlt t (by omega)
  · obtain ⟨h1, h2, h3⟩ := hqb i hi
    rw [h1, hQget, h3, (hb i hi).1, hQs]
    exact ⟨h2, rfl⟩
  · rw [trees_get hi, (hb i hi).1, levelLetters_eq H i hi.le]
    exact (tree_eq H hi).2
  · rw [levelLetters_eq H i hi.le, Array.all_eq_true']
    intro l hl
    rw [List.mem_toArray] at hl
    apply parAll_of
    intro k hk
    rw [trees_get hi, pts_size] at hk
    exact hS i hi l hl k hk
  · rw [levelLetters_eq H m (Nat.le_refl _), Array.all_eq_true']
    intro l hl
    rw [List.mem_toArray] at hl
    have hl' := (mem_lvK.1 hl).1
    rw [tupleEq_iff_toList, CFSG.KS.TW.apT_map, Array.toList_map, hQ]
    conv_rhs => rw [← List.map_id QL]
    apply List.map_congr_left
    intro x hx
    rw [ap_letter H hl' (QL_lt H x hx), hT l hl x hx]
    rfl

theorem pchainK_sound (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hsch : ∀ i < m, ∀ k < CNT i, ∀ t < (lvK L B NL i).length,
      schK L PTS POS PAR LAB CNT QB QL m i (lvAt L B NL i t) k = true)
    (hterm : termK L B NL m QL = true) :
    chainTrees n letters base =
        Array.ofFn (n := m) (fun i => tbfsRec n (CNT i.val) (PTS i.val) (POS i.val) (PAR i.val)
          (LAB i.val)) ∧
      ∀ chunks, chainOK n letters base Q qb (chainTrees n letters base) chunks = true := by
  refine chainOK_of H (fun i hi l hl k hk => ?_) (fun l hl => ?_)
  · rw [schreierAt_eq H hi hl hk]
    obtain ⟨t, ht, rfl⟩ := exists_lvAt hl
    exact hsch i hi k hk t ht
  · unfold termK at hterm
    rw [List.all_eq_true] at hterm
    have := hterm l hl
    rw [listEqK_iff, mapK_eq] at this
    exact map_self this

end

section Card

variable {n NL m : Nat} {letters : Array Table} {base Q qb : Array Nat}
  {L : Nat → Nat → Nat} {B : Nat → Nat} {QL : List Nat} {QB CNT : Nat → Nat}
  {PTS POS PAR LAB TI : Nat → Nat → Nat}

open CFSG.KS.PCC

noncomputable abbrev grp (n NL : Nat) (letters : Array Table) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure (Set.range fun l : Fin NL => permOfT n letters[l.val]!)

@[expose] def bF (hn : 0 < n) (B : Nat → Nat) (k : Nat) : Fin n := ⟨B k % n, Nat.mod_lt _ hn⟩

theorem bF_val (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) {k : Nat} (hk : k < m) : (bF hn B k : Nat) = B k :=
  Nat.mod_eq_of_lt (H.base.2 k hk).2

private theorem sig_Gs (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) {i l : Nat} (hi : i ≤ m) (hl : l ∈ lvK L B NL i) :
    sig n letters l ∈ Gs (grp n NL letters) (bF hn B) i := by
  obtain ⟨hl', hfix⟩ := mem_lvK.1 hl
  rw [mem_Gs]
  refine ⟨sig_mem ⟨l, hl'⟩, fun k hk => Fin.ext ?_⟩
  rw [sig_val H hl', bF_val H hn (by omega), hfix k hk]

private theorem tw_Gs (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) {i : Nat} (hi : i < m) : ∀ k < CNT i,
      twL n letters PAR LAB i k ∈ Gs (grp n NL letters) (bF hn B) i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [twL, tw_eq]
    by_cases hc : 0 < k ∧ r32 (PAR i) k < k
    · rw [ite_eq_left hc]
      exact Subgroup.mul_mem _ (sig_Gs H hn hi.le (lab_mem H hi hk hc.1)) (ih _ hc.2 (by omega))
    · rw [ite_eq_right hc]
      exact Subgroup.one_mem _

theorem tw_pt (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    {i : Nat} (hi : i < m) : ∀ k < CNT i, actN (twL n letters PAR LAB i k) (B i) = r32 (PTS i) k := by
  have R := rep_of H hi
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [twL, tw_eq]
    by_cases h0 : k = 0
    · subst h0
      rw [ite_eq_right (by omega), actN_one, R.hd.root]
    · obtain ⟨a1, a2, a3, a4, -⟩ := (R.pt k hk).tree (by omega)
      have hl := (mem_lvK.1 (lab_mem H hi hk (by omega))).1
      rw [ite_eq_left ⟨by omega, a1⟩, actN_mul]
      have e := ih _ a1 (by omega)
      rw [twL] at e
      rw [e, actN_sig H hl (R.pt _ (by omega)).lt, a3, a4]

@[expose] noncomputable def dSet (hn : 0 < n) (CNT : Nat → Nat) (PTS : Nat → Nat → Nat) (l : Nat) :
    Finset (Fin n) :=
  (Finset.range (CNT l)).image fun k => ⟨r32 (PTS l) k % n, Nat.mod_lt _ hn⟩

theorem dSet_card (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) {l : Nat} (hl : l < m) : (dSet hn CNT PTS l).card = CNT l := by
  have R := rep_of H hl
  unfold dSet
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb e
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have e' := congrArg Fin.val e
  simp only [Nat.mod_eq_of_lt (R.pt a ha).lt, Nat.mod_eq_of_lt (R.pt b hb).lt] at e'
  exact R.inj ha hb e'

private theorem dSet_sub (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) {l : Nat} (hl : l < m) :
    ∀ x ∈ dSet hn CNT PTS l, x ∈ MulAction.orbit (Gs (grp n NL letters) (bF hn B) l) (bF hn B l) := by
  intro x hx
  unfold dSet at hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
  rw [Finset.mem_range] at hk
  refine mem_orbit_Gs.2 ⟨_, tw_Gs H hn hl k hk, Fin.ext ?_⟩
  rw [← actN_fin, bF_val H hn hl, tw_pt H hl k hk]
  exact (Nat.mod_eq_of_lt ((rep_of H hl).pt k hk).lt).symm

theorem card_dSet (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n)
    (hcard : Nat.card (grp n NL letters) ≤ ((List.range m).map CNT).prod) :
    Nat.card (grp n NL letters) ≤ ∏ l ∈ Finset.range m, (dSet hn CNT PTS l).card := by
  refine hcard.trans (le_of_eq ?_)
  rw [prod_range_map]
  exact Finset.prod_congr rfl fun l hl => (dSet_card H hn (Finset.mem_range.1 hl)).symm

private theorem complete (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) (hcard : Nat.card (grp n NL letters) ≤ ((List.range m).map CNT).prod)
    {l : Nat} (hl : l < m) {g : Equiv.Perm (Fin n)} (hg : g ∈ Gs (grp n NL letters) (bF hn B) l) :
    ∃ k < CNT l, r32 (PTS l) k = g (bF hn B l) := by
  have h := orbit_sub (dSet hn CNT PTS) (L := m) (fun l hl => dSet_sub H hn hl)
    (card_dSet H hn hcard) l hl (g (bF hn B l)) (mem_orbit_Gs.2 ⟨g, hg, rfl⟩)
  unfold dSet at h
  obtain ⟨k, hk, e⟩ := Finset.mem_image.1 h
  rw [Finset.mem_range] at hk
  refine ⟨k, hk, ?_⟩
  rw [← e]
  exact (Nat.mod_eq_of_lt ((rep_of H hl).pt k hk).lt).symm

private theorem stab_trivial (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) (hcard : Nat.card (grp n NL letters) ≤ ((List.range m).map CNT).prod)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Gs (grp n NL letters) (bF hn B) m) : g = 1 := by
  have hc := card_dSet H hn hcard
  have hchain := card_chain (grp n NL letters) (bF hn B) m
  have hle : ∏ l ∈ Finset.range m, (dSet hn CNT PTS l).card ≤
      ∏ l ∈ Finset.range m,
        (MulAction.orbit (Gs (grp n NL letters) (bF hn B) l) (bF hn B l)).ncard := by
    apply Finset.prod_le_prod
    intro l hl
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun x hx => dSet_sub H hn (Finset.mem_range.1 hl) x hx)
  have hG : 0 < Nat.card (grp n NL letters) := Nat.card_pos
  have h1 : Nat.card (Gs (grp n NL letters) (bF hn B) m) ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ Nat.card (Gs (grp n NL letters) (bF hn B) m) := by omega
    have h3 := Nat.mul_le_mul_left (∏ l ∈ Finset.range m,
        (MulAction.orbit (Gs (grp n NL letters) (bF hn B) l) (bF hn B l)).ncard) h2
    omega
  have := Subgroup.eq_bot_of_card_le _ h1
  rw [this] at hg
  exact (Subgroup.mem_bot).1 hg

theorem siftF_succ (L : Nat → Nat → Nat) (POS PAR LAB : Nat → Nat → Nat) (CNT QB : Nat → Nat)
    (QL : List Nat) (d j : Nat) (q : List Nat) :
    siftF L POS PAR LAB CNT QB QL (d + 1) j q =
      (decide (r32 (POS j) (q.getD (QB j) 0) < CNT j) &&
        siftF L POS PAR LAB CNT QB QL d (j + 1)
          (walkInvK L (PAR j) (LAB j) (r32 (POS j) (q.getD (QB j) 0)) q)) := by
  change strictB (r32 (POS j) (q.getD (QB j) 0)) (fun k =>
    Bool.rec (motive := fun _ => Bool) false
      (siftF L POS PAR LAB CNT QB QL d (j + 1) (walkInvK L (PAR j) (LAB j) k q))
      (Nat.blt k (CNT j))) = _
  rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq]
  congr 1

private theorem sift_ok (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) (hcard : Nat.card (grp n NL letters) ≤ ((List.range m).map CNT).prod) :
    ∀ d j, j + d = m → ∀ g ∈ Gs (grp n NL letters) (bF hn B) j,
      siftF L POS PAR LAB CNT QB QL d j (QL.map (actN g)) = true
  | 0, j, hj, g, hg => by
    have e : j = m := by omega
    subst e
    rw [stab_trivial H hn hcard hg]
    have : actN (1 : Equiv.Perm (Fin n)) = id := funext actN_one
    rw [this, List.map_id]
    exact (listEqK_iff _ _).2 rfl
  | d + 1, j, hj, g, hg => by
    have hjm : j < m := by omega
    obtain ⟨hqb, hql, hqv⟩ := (H.chk.2.2.2 j hjm)
    have hBj := (H.base.2 j hjm).2
    have hget : (QL.map (actN g)).getD (QB j) 0 = g (bF hn B j) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hql), List.getElem_map,
        ← List.getD_eq_getElem _ 0 hql, hqv, actN_of_lt _ hBj]
      congr 2
      exact Fin.ext (bF_val H hn hjm).symm
    obtain ⟨k, hk, hkv⟩ := complete H hn hcard hjm hg
    have hpos : r32 (POS j) ((QL.map (actN g)).getD (QB j) 0) = k := by
      rw [hget, ← hkv]
      exact ((rep_of H hjm).pt k hk).pos
    rw [siftF_succ, hpos, decide_eq_true hk, Bool.true_and]
    unfold walkInvK
    rw [walkInvF_eq H hjm k k hk (Nat.le_refl _) _ (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact actN_lt _ (QL_lt H y hy)), List.map_map]
    have e : actN (twL n letters PAR LAB j k)⁻¹ ∘ actN g =
        actN ((twL n letters PAR LAB j k)⁻¹ * g) := funext fun x => (actN_mul _ _ x).symm
    rw [e]
    have hT := (mem_Gs _ _).1 (tw_Gs H hn hjm k hk)
    refine sift_ok H hn hcard d (j + 1) (by omega) _ ?_
    rw [mem_Gs] at hg ⊢
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hT.1) hg.1, fun k' hk' => ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
    · rw [hg.2 k' hk', hT.2 k' hk']
    · apply Fin.ext
      rw [← hkv, ← actN_fin (twL n letters PAR LAB _ k), bF_val H hn hjm, tw_pt H hjm k hk]

theorem sch_of_card (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hcard : Nat.card (grp n NL letters) ≤ ((List.range m).map CNT).prod) :
    ∀ i < m, ∀ k < CNT i, ∀ t < (lvK L B NL i).length,
      schK L PTS POS PAR LAB CNT QB QL m i (lvAt L B NL i t) k = true := by
  intro i hi k hk t ht
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) (H.base.2 i hi).2
  have R := rep_of H hi
  obtain ⟨hy, hky, -⟩ := (R.pt k hk).close t ht
  have hl := lvAt_mem ht
  generalize lvAt L B NL i t = l at hy hky hl ⊢
  have hl' := (mem_lvK.1 hl).1
  have hQL := QL_lt H
  unfold schK
  rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq,
    show Nat.blt (r32 (POS i) (L l (r32 (PTS i) k))) (CNT i) = true by simpa [Nat.blt_eq] using hky,
    Bool.true_and]
  unfold siftK walkK walkInvK
  rw [walkF_eq H hi k k hk (Nat.le_refl _) QL hQL, mapK_eq, List.map_map,
    walkInvF_eq H hi _ _ hky (Nat.le_refl _) _ (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      exact lab_lt H hl' _ (actN_lt _ (hQL z hz))), List.map_map]
  have hT1 := (mem_Gs _ _).1 (tw_Gs H hn hi k hk)
  have hT2 := (mem_Gs _ _).1 (tw_Gs H hn hi _ hky)
  have hS := (mem_Gs _ _).1 (sig_Gs H hn hi.le hl)
  have e : List.map (actN (twL n letters PAR LAB i (r32 (POS i) (L l (r32 (PTS i) k))))⁻¹ ∘
      L l ∘ actN (twL n letters PAR LAB i k)) QL =
      QL.map (actN ((twL n letters PAR LAB i (r32 (POS i) (L l (r32 (PTS i) k))))⁻¹ *
        sig n letters l * twL n letters PAR LAB i k)) := by
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply, actN_mul]
    rw [actN_sig H hl' (actN_lt _ (hQL x hx))]
  rw [e]
  refine sift_ok H hn hcard (m - (i + 1)) (i + 1) (by omega) _ ?_
  rw [mem_Gs]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hT2.1) hS.1) hT1.1,
    fun k' hk' => ?_⟩
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
  · rw [hT1.2 k' hk', hS.2 k' hk', hT2.2 k' hk']
  · apply Fin.ext
    rw [sig_val H hl', ← actN_fin (twL n letters PAR LAB _ k), ← actN_fin (twL n letters PAR LAB _ _),
      bF_val H hn hi, tw_pt H hi k hk, tw_pt H hi _ hky, R.pts_pos hy hky]

theorem term_of_card (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hcard : Nat.card (grp n NL letters) ≤ ((List.range m).map CNT).prod) :
    termK L B NL m QL = true := by
  unfold termK
  rw [List.all_eq_true]
  intro l hl
  rw [listEqK_iff, mapK_eq]
  by_cases hn : 0 < n
  · have e := stab_trivial H hn hcard (sig_Gs H hn (Nat.le_refl _) hl)
    have hl' := (mem_lvK.1 hl).1
    conv_rhs => rw [← List.map_id QL]
    apply List.map_congr_left
    intro x hx
    rw [← actN_sig H hl' (QL_lt H x hx), e, actN_one]
    rfl
  · have : QL = [] := by
      cases QL with
      | nil => rfl
      | cons x q => exact absurd (QL_lt H x (List.mem_cons_self ..)) (by omega)
    rw [this]
    rfl

theorem pchain_of_card (h : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hcard : Nat.card (Subgroup.closure (Set.range fun l : Fin NL => permOfT n letters[l.val]!)) ≤
      ((List.range m).map CNT).prod) :
    chainTrees n letters base =
        Array.ofFn (n := m) (fun i => tbfsRec n (CNT i.val) (PTS i.val) (POS i.val) (PAR i.val)
          (LAB i.val)) ∧
      ∀ chunks, chainOK n letters base Q qb (chainTrees n letters base) chunks = true :=
  pchainK_sound h (sch_of_card h hcard) (term_of_card h hcard)

end Card

end CFSG.KS.PC

end
