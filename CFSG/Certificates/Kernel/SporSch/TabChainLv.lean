module

public import CFSG.Certificates.Kernel.SporSch.PairClTDefs
public import CFSG.Certificates.Kernel.Spor.RawAgree
public import CFSG.Sporadic.Schreier.PairClasses
public import Certificates.Data.Kernel.SporSch.PairJ3Cnt
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import Mathlib.Data.Int.Star

public section

namespace CFSG.KS.SporSch.Tab

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative

variable {n w kS nb BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}

@[expose] noncomputable def trT (n w : Nat) (LR : Nat → Nat) (S : Array (Array Nat))
    (base : Array Nat) (i k : Nat) : Equiv.Perm (Fin n) :=
  treeF (stp n S base i) (rpar w (mask w) (n * w) (LR i)) (rlab n (n * w) (LR i)) k k

@[expose] def nfA (nb F : Nat) : Array Nat :=
  Array.ofFn (n := nb) fun i => F / 2 ^ (16 * i.val) % 65536

theorem land_65535 (a : Nat) : Nat.land a (nat_lit 65535) = a % 65536 := by
  change a &&& (2 ^ 16 - 1) = a % 2 ^ 16
  exact Nat.and_two_pow_sub_one_eq_mod a 16

theorem fld16 (F o : Nat) : Nat.land (Nat.shiftRight F o) (nat_lit 65535) = F / 2 ^ o % 65536 := by
  rw [land_65535, shr_eq]

theorem rcnt_lt (R : Nat) : rcnt R < 65536 := by
  unfold rcnt
  rw [land_65535]
  exact Nat.mod_lt _ (by norm_num)

theorem entry_lo {a b : Nat} (ha : a < 65536) :
    Nat.land (Nat.add a (Nat.shiftLeft b (nat_lit 16))) (nat_lit 65535) = a := by
  rw [land_65535, shl_eq', Nat.add_eq, show (2 : Nat) ^ 16 = 65536 by norm_num]
  omega

theorem entry_hi {a b : Nat} (ha : a < 65536) :
    Nat.shiftRight (Nat.add a (Nat.shiftLeft b (nat_lit 16))) (nat_lit 16) = b := by
  rw [shr_eq, shl_eq', Nat.add_eq, show (2 : Nat) ^ 16 = 65536 by norm_num]
  omega

theorem letterK_invL {PS PSI : Nat → Nat} {kS l : Nat} (hl : l < kS + kS) :
    letterK PS PSI kS (invL kS l) = invLetterK PS PSI kS l ∧ invL kS l < kS + kS := by
  refine ⟨?_, ?_⟩
  · unfold letterK invL invLetterK
    simp only [nIf_eq, blt_dec, decide_eq_true_eq, Nat.add_eq, Nat.sub_eq]
    split_ifs <;> first | omega | rfl | (congr 1; omega)
  · unfold invL
    simp only [nIf_eq, blt_dec, decide_eq_true_eq, Nat.add_eq, Nat.sub_eq]
    split_ifs <;> omega

theorem blk_of {NB B : Nat} {f : Nat → Bool} (h : ∀ s < NB, allBlk (Nat.mul s B) f B = true)
    {k m : Nat} (hm : m ≤ NB * B) (hk : k < m) : f k = true := by
  obtain ⟨hB, hs, e⟩ := slice_cover hm hk
  have h1 := allBlk_spec (h (k / B) hs) (k % B) (Nat.mod_lt _ hB)
  have e' : Nat.add (Nat.mul (k / B) B) (k % B) = k := e
  rwa [e'] at h1

theorem bIf_true {c t e : Bool} (hc : c = true) (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    t = true := by
  subst hc
  exact h

section Levels

variable (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH)

include hb ho hN in
theorem base_lt : ∀ t < nb, base[t]! < n := base_lt_of hb ho.1 ho.2 hN

include ho hN in
theorem recFacts {i : Nat} (hi : i < nb) :
    RecFacts n w PS PSI kS (pg w (mask w) BP i) (stepsAt n w PS kS BP i) (LR i) :=
  recFacts_of (ho.1 i hi) (ho.2 i hi) hN

include ho hN in
theorem ptTK {i : Nat} (hi : i < nb) : ∀ k < n, lvPtTK n w (mask w) (n * w) PS PSI kS
    (stepsAt n w PS kS BP i) (LR i) (rcnt (LR i)) (stCnt (stepsAt n w PS kS BP i)) k = true := by
  intro k hk
  obtain ⟨hCH, hsk, e⟩ := slice_cover hN hk
  have h1 := allN_spec (ho.2 i hi (k / CH) hsk) (k % CH) (Nat.mod_lt _ hCH)
  rw [e] at h1
  exact h1

include hb hp ho hN in
theorem agree {i : Nat} (hi : i < nb) :
    (∀ k < rcnt (LR i), 0 < k → rpar w (mask w) (n * w) (LR i) k < k ∧
      rlab n (n * w) (LR i) k < (rawSteps n S base i).size) ∧
    Agree n w (LR i) (lev n S base i) (trT n w LR S base i) :=
  agree_treeK hb hp (base_lt hb ho hN) hi (ho.1 i hi) (ptTK ho hN hi)

include ho hN in
theorem recOK {i : Nat} (hi : i < nb) :
    RecOK n (pg w (mask w) BP i) (stCnt (stepsAt n w PS kS BP i))
      (fun j x => pg w (mask w) (letterK PS PSI kS (stAt (stepsAt n w PS kS BP i) j)) x)
      (rcnt (LR i)) (rpt w (mask w) (LR i)) (rpos w (mask w) (n * w) (LR i))
      (rpar w (mask w) (n * w) (LR i)) (rlab n (n * w) (LR i)) :=
  (treeK_facts (ho.1 i hi) (ptTK ho hN hi)).2.2

include hb hp ho hN in
theorem cnt_eq {i : Nat} (hi : i < nb) : rcnt (LR i) = (lev n S base i).pts.size :=
  (agree hb hp ho hN hi).2.cnt

include hb hp ho hN in
theorem trT_eq_levT {i k : Nat} (hi : i < nb) (hk : k < rcnt (LR i)) :
    levT n S base i k = trT n w LR S base i k := by
  have A := (agree hb hp ho hN hi).2
  have hr := (A.tr k (A.cnt ▸ hk)).1
  exact (Rep.unique hr (rep_pa hr)).symm

include hb hp ho hN in
theorem steps_tab (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ) {i j : Nat}
    (hi : i < nb) (hj : j < (rawSteps n S base i).size) (x : Fin n) :
    lptK w NR LT (stAt (Ts i) j) x = (stp n S base i j x : Nat) ∧
      lptK w NR LT (invL kS (stAt (Ts i) j)) x = ((stp n S base i j)⁻¹ x : Nat) := by
  have R := recFacts ho hN hi
  have hbl := base_lt hb ho hN
  have hTs : Ts i = stepsAt n w PS kS BP i := Nat.eq_of_beq_eq_true (ht.2.2.2.2.1 i hi)
  obtain ⟨hcnt, hpr, _, hinv⟩ := kernel_steps hb hp R.kS_lt hbl hi.le
  have hk2 : kS + kS < 256 := by have := R.kS_lt; omega
  have hjL : j < ((List.range (kS + kS)).filter
      (tabP kS (fixMaskK w (mask w) PS kS BP i))).length := by
    rw [← stCnt_eq hk2]
    change j < stCnt (stepsAt n w PS kS BP i)
    rw [hcnt]
    exact hj
  have hl : stAt (stepsAt n w PS kS BP i) j < kS + kS := by
    unfold stepsAt
    rw [stAt_eq hk2 hjL]
    have := List.getElem_mem hjL
    rw [List.mem_filter, List.mem_range] at this
    exact this.1
  rw [hTs]
  set l := stAt (stepsAt n w PS kS BP i) j
  have hlt : ∀ l' < kS + kS, lptK w NR LT l' x = pg w (mask w) (letterK PS PSI kS l') x := by
    intro l' hl'
    have hj' : l' * n + x < (kS + kS) * n := by
      have := x.2
      nlinarith
    have h1 := blk_of ht.2.2.2.2.2.1 ht.2.2.1 hj'
    unfold ltOKT at h1
    have h2 := bIf_true (Nat.blt_eq.mpr hj') h1
    have hd : Nat.div (l' * n + x) n = l' := by
      change (l' * n + x) / n = l'
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt x.2, Nat.zero_add]
    have hm : Nat.mod (l' * n + x) n = x := by
      change (l' * n + x) % n = x
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.2]
    rw [Orb.strictB_eq, hd, Orb.strictB_eq, hm] at h2
    exact Nat.eq_of_beq_eq_true h2
  refine ⟨by rw [hlt l hl]; exact hpr j hj x, ?_⟩
  obtain ⟨e, hil⟩ := letterK_invL (PS := PS) (PSI := PSI) hl
  rw [hlt _ hil, ← hinv j hj x, e]

include ho hN in
theorem pt_entry (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ) {i k : Nat}
    (hi : i < nb) (hk : k < rcnt (LR i)) :
    lvT NL (nat_lit 24) PT i k = Nat.add (rpar w (mask w) (n * w) (LR i) k)
      (Nat.shiftLeft (stAt (Ts i) (rlab n (n * w) (LR i) k)) (nat_lit 16)) := by
  have R := recFacts ho hN hi
  have h1 := blk_of (ht.2.2.2.2.2.2.1 i hi) ht.2.2.2.1 (lt_of_lt_of_le hk R.c_le)
  unfold ptOKT at h1
  rw [Orb.strictB_eq] at h1
  exact Nat.eq_of_beq_eq_true (bIf_true (Nat.blt_eq.mpr hk) h1)

omit hb hp ho hN in
theorem lvT_QT (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ) {i z : Nat}
    (hi : i < nb) (hz : z < n) : lvT NL w QT i z = rpos w (mask w) (n * w) (LR i) z := by
  have h1 := blk_of (ht.2.2.2.2.2.2.2 i hi) ht.2.2.2.1 hz
  unfold qtOKT at h1
  exact Nat.eq_of_beq_eq_true (bIf_true (Nat.blt_eq.mpr hz) h1)

@[expose] noncomputable def trR (w NR NL : Nat) (LT PT : Nat → Nat) (i : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => nIf(Nat.beq k (nat_lit 0), x,
      strictN (lvT NL (nat_lit 24) PT i k) (fun e =>
      strictN (ih (Nat.land e (nat_lit 65535)) x) (fun y =>
        lptK w NR LT (Nat.shiftRight e (nat_lit 16)) y))))

@[expose] noncomputable def trIR (w kS NR NL : Nat) (LT PT : Nat → Nat) (i : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => nIf(Nat.beq k (nat_lit 0), x,
      strictN (lvT NL (nat_lit 24) PT i k) (fun e =>
      strictN (lptK w NR LT (invL kS (Nat.shiftRight e (nat_lit 16))) x) (fun y =>
        ih (Nat.land e (nat_lit 65535)) y))))

theorem trR_pos {w NR NL : Nat} {LT PT : Nat → Nat} {i f k x : Nat} (hk : 0 < k) :
    trR w NR NL LT PT i (f + 1) k x = strictN (lvT NL (nat_lit 24) PT i k) (fun e =>
      strictN (trR w NR NL LT PT i f (Nat.land e (nat_lit 65535)) x) (fun y =>
        lptK w NR LT (Nat.shiftRight e (nat_lit 16)) y)) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rfl

theorem trIR_pos {w kS NR NL : Nat} {LT PT : Nat → Nat} {i f k x : Nat} (hk : 0 < k) :
    trIR w kS NR NL LT PT i (f + 1) k x = strictN (lvT NL (nat_lit 24) PT i k) (fun e =>
      strictN (lptK w NR LT (invL kS (Nat.shiftRight e (nat_lit 16))) x) (fun y =>
        trIR w kS NR NL LT PT i f (Nat.land e (nat_lit 65535)) y)) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rfl

include hb hp ho hN in
theorem trPtT_eq (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ) {i k : Nat}
    (hi : i < nb) (hk : k < rcnt (LR i)) (x : Fin n) :
    trPtT w NR NL LT PT i k x = (trT n w LR S base i k x : Nat) := by
  obtain ⟨hpl, -⟩ := agree hb hp ho hN hi
  suffices H : ∀ f k, k < rcnt (LR i) → k ≤ f → ∀ x : Fin n,
      trR w NR NL LT PT i f k x = (treeF (stp n S base i) (rpar w (mask w) (n * w) (LR i))
        (rlab n (n * w) (LR i)) f k x : Nat) from H k k hk le_rfl x
  intro f
  induction f with
  | zero => intro k _ _ x; rfl
  | succ f ih =>
    intro k hk hkf x
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [treeF_zero]
      rfl
    · obtain ⟨hpk, hlk⟩ := hpl k hk hk0
      have hpar : rpar w (mask w) (n * w) (LR i) k < 65536 :=
        lt_trans hpk (lt_trans hk (rcnt_lt _))
      rw [trR_pos hk0, strictN_eq, pt_entry ho hN ht hi hk, strictN_eq, entry_lo hpar,
        entry_hi hpar, ih _ (by omega) (by omega) x]
      rw [(steps_tab hb hp ho hN ht hi hlk _).1]
      simp only [treeF, show k ≠ 0 by omega, ↓reduceIte, Equiv.Perm.mul_apply]

include hb hp ho hN in
theorem trInvPtT_eq (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ) {i k : Nat}
    (hi : i < nb) (hk : k < rcnt (LR i)) (x : Fin n) :
    trInvPtT w kS NR NL LT PT i k x = ((trT n w LR S base i k)⁻¹ x : Nat) := by
  obtain ⟨hpl, -⟩ := agree hb hp ho hN hi
  suffices H : ∀ f k, k < rcnt (LR i) → k ≤ f → ∀ x : Fin n,
      trIR w kS NR NL LT PT i f k x = ((treeF (stp n S base i) (rpar w (mask w) (n * w) (LR i))
        (rlab n (n * w) (LR i)) f k)⁻¹ x : Nat) from H k k hk le_rfl x
  intro f
  induction f with
  | zero => intro k _ _ x; rfl
  | succ f ih =>
    intro k hk hkf x
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [treeF_zero]
      rfl
    · obtain ⟨hpk, hlk⟩ := hpl k hk hk0
      have hpar : rpar w (mask w) (n * w) (LR i) k < 65536 :=
        lt_trans hpk (lt_trans hk (rcnt_lt _))
      rw [trIR_pos hk0, strictN_eq, pt_entry ho hN ht hi hk, strictN_eq, entry_lo hpar,
        entry_hi hpar, (steps_tab hb hp ho hN ht hi hlk x).2]
      rw [ih _ (by omega) (by omega)]
      simp only [treeF, show k ≠ 0 by omega, ↓reduceIte, mul_inv_rev, Equiv.Perm.mul_apply]

include hb hp ho hN in
theorem rpt_eq {i k : Nat} (hi : i < nb) (hk : k < rcnt (LR i)) :
    rpt w (mask w) (LR i) k = (trT n w LR S base i k ⟨base[i]!, base_lt hb ho hN i hi⟩ : Nat) := by
  have K := recOK ho hN hi
  have R := recFacts ho hN hi
  have hbl := base_lt hb ho hN
  obtain ⟨hcnt, hpr, _, _⟩ := kernel_steps hb hp R.kS_lt hbl hi.le
  have hbi : base[i]! = pg w (mask w) BP i := hb.2.2.2.2.2.2 i hi
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [K.root, ← hbi]
      unfold trT
      rw [treeF_zero]
      rfl
    · have hpk := K.par_lt k hk hk0
      have hlk := K.lab_lt k hk hk0
      unfold trT
      rw [treeF_step K.par_lt hk hk0, Equiv.Perm.mul_apply, ← K.edge k hk hk0]
      have e := ih _ hpk (by omega)
      unfold trT at e
      rw [hcnt] at hlk
      have e2 := hpr _ hlk (treeF (stp n S base i) (rpar w (mask w) (n * w) (LR i))
        (rlab n (n * w) (LR i)) (rpar w (mask w) (n * w) (LR i) k)
        (rpar w (mask w) (n * w) (LR i) k) ⟨base[i]!, base_lt hb ho hN i hi⟩)
      rw [← e] at e2
      rw [← e2]

theorem nfA_get {nb F i : Nat} (hi : i < nb) : (nfA nb F)[i]! = F / 2 ^ (16 * i) % 65536 := by
  rw [nfA, getElem!_ofFn_nat _ hi]

include hb hp ho hN in
theorem nfPtT_spec (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ) {F : Nat}
    (hF : nfValidK nb LR F = true) :
    nfOK (rawLevels n S base) (nfA nb F) = true ∧
      ∀ x (hx : x < n), nfPtT w NR NL LT PT nb F x = (nfElt n S base (nfA nb F) ⟨x, hx⟩ : Nat) := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hv : ∀ t < nb, F / 2 ^ (16 * t) % 65536 < rcnt (LR t) := fun t ht' => by
    have := allN_spec hF t ht'
    rw [fld16] at this
    exact Nat.blt_eq.mp this
  have hsz : (nfA nb F).size = nb := by simp [nfA]
  refine ⟨?_, fun x hx => ?_⟩
  · unfold nfOK
    rw [Bool.and_eq_true, beq_iff_eq, allLt_iff, hsz, chainLevels_size, hbs]
    refine ⟨rfl, fun i hi => ?_⟩
    rw [decide_eq_true_eq, nfA_get hi, ← lev, ← cnt_eq hb hp ho hN hi]
    exact hv i hi
  · rw [nfElt, hsz]
    suffices H : ∀ m ≤ nb, ∀ x : Fin n, nfPtT w NR NL LT PT m F x =
        (((List.range m).map fun i => levT n S base i (nfA nb F)[i]!).prod x : Nat) from
      H nb le_rfl ⟨x, hx⟩
    intro m
    induction m with
    | zero => intro _ x; rfl
    | succ m ih =>
      intro hm x
      change strictN (trPtT w NR NL LT PT m (Nat.land (Nat.shiftRight F (Nat.mul (nat_lit 16) m))
        (nat_lit 65535)) x) (fun y => nfPtT w NR NL LT PT m F y) = _
      have hkm := hv m (by omega)
      rw [strictN_eq, fld16, Nat.mul_eq, trPtT_eq hb hp ho hN ht (by omega) hkm,
        ih (by omega), List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, Equiv.Perm.mul_apply, nfA_get (by omega : m < nb),
        trT_eq_levT hb hp ho hN (by omega) hkm]

end Levels

end CFSG.KS.SporSch.Tab

end
