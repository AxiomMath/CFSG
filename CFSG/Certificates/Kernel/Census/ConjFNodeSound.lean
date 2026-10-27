module

public import Certificates.Data.Kernel.Census.PackedConjF
public import CFSG.Certificates.Kernel.Census.ConjProof
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

theorem pid_valid24 {n w : Nat} (hw : n ≤ 2 ^ w) (h24 : n ≤ 2 ^ 24) :
    pvalid n w (pid n w) = true := by
  obtain ⟨-, -, hid⟩ := SP.pid_good24 hw h24
  exact pvalid_of_inj hw (fun i hi => by rw [hid i hi]; exact hi)
    (fun i hi j hj e => by rwa [hid i hi, hid j hj] at e)

theorem pvalid_pprod_proved {n w : Nat} {l : List Nat} (h24 : n ≤ 2 ^ 24) (hn : n < 2 ^ 32)
    (hw : n ≤ 2 ^ w) (hl : ∀ x ∈ l, canon1 n w x = true ∧ pvalid n w x = true) :
    canon1 n w (pprod n w l) = true ∧ pvalid n w (pprod n w l) = true := by
  obtain ⟨e1, e2, -⟩ := SP.pid_good24 hw h24
  have G : SP.Good n w := ⟨hn, hw, e1, e2⟩
  induction l with
  | nil => exact ⟨e2, pid_valid24 hw h24⟩
  | cons a l ih =>
    have ha := hl a List.mem_cons_self
    obtain ⟨c1, v1⟩ := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
    change canon1 n w (pc n w a (pprod n w l)) = true ∧ pvalid n w (pc n w a (pprod n w l)) = true
    exact ⟨SP.pc_canon G _ _, pvalid_pc hn hw ha.1 ha.2 c1 v1⟩

theorem pvalid_ppcA_proved {n w : Nat} {xs : List Nat} (h24 : n ≤ 2 ^ 24) (hn : n < 2 ^ 32)
    (hw : n ≤ 2 ^ w) (hx : ∀ x ∈ xs, canon1 n w x = true ∧ pvalid n w x = true) (m : Nat) :
    canon1 n w (ppcA n w xs m) = true ∧ pvalid n w (ppcA n w xs m) = true := by
  obtain ⟨e1, e2, -⟩ := SP.pid_good24 hw h24
  have G : SP.Good n w := ⟨hn, hw, e1, e2⟩
  exact ⟨(SP.ppcA_eq G xs m fun x hx' => (hx x hx').1).2,
    SP.ppcA_valid G (pid_valid24 hw h24) xs m hx⟩

private noncomputable def toPerm (n w p : Nat) : Equiv.Perm (Fin n) :=
  if h : pvalid n w p = true then
    Equiv.ofBijective (fun i : Fin n => (⟨at' w p i, (inj_of_pvalid h).1 i i.2⟩ : Fin n))
      (Finite.injective_iff_bijective.1 fun i j e =>
        Fin.ext ((inj_of_pvalid h).2 i i.2 j j.2 (congrArg Fin.val e)))
  else 1

private theorem toPerm_apply {n w p : Nat} (hp : pvalid n w p = true) (i : Fin n) :
    ((toPerm n w p i : Fin n) : Nat) = at' w p i := by
  unfold toPerm
  rw [dif_pos hp]
  rfl

private theorem toPerm_inj {n w p q : Nat} (hp : canon1 n w p = true ∧ pvalid n w p = true)
    (hq : canon1 n w q = true ∧ pvalid n w q = true) (h : toPerm n w p = toPerm n w q) :
    p = q :=
  SP.eq_of_at' hp.1 hq.1 fun i hi => by
    have e := congrArg (fun σ : Equiv.Perm (Fin n) => ((σ ⟨i, hi⟩ : Fin n) : Nat)) h
    simpa only [toPerm_apply hp.2, toPerm_apply hq.2] using e

private theorem V_pc {n w p q : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hp : canon1 n w p = true ∧ pvalid n w p = true)
    (hq : canon1 n w q = true ∧ pvalid n w q = true) :
    canon1 n w (pc n w p q) = true ∧ pvalid n w (pc n w p q) = true :=
  ⟨SP.canon_pc hn hw, pvalid_pc hn hw hp.1 hp.2 hq.1 hq.2⟩

private theorem toPerm_pc {n w p q : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hp : canon1 n w p = true ∧ pvalid n w p = true)
    (hq : canon1 n w q = true ∧ pvalid n w q = true) :
    toPerm n w (pc n w p q) = toPerm n w p * toPerm n w q := by
  ext i
  rw [toPerm_apply (V_pc hn hw hp hq).2, Equiv.Perm.mul_apply, toPerm_apply hp.2,
    toPerm_apply hq.2]
  exact CFSG.KS.PF.pg_pcomp hn i.2

private theorem V_pid {n w : Nat} (hw : n ≤ 2 ^ w) (h24 : n ≤ 2 ^ 24) :
    canon1 n w (pid n w) = true ∧ pvalid n w (pid n w) = true :=
  ⟨(SP.pid_good24 hw h24).2.1, pid_valid24 hw h24⟩

private theorem toPerm_pid {n w : Nat} (hw : n ≤ 2 ^ w) (h24 : n ≤ 2 ^ 24) :
    toPerm n w (pid n w) = 1 := by
  ext i
  rw [toPerm_apply (pid_valid24 hw h24), (SP.pid_good24 hw h24).2.2 i i.2]
  rfl

private theorem at'_pinv_eq {n w p : Nat} (hw : n ≤ 2 ^ w) (hp : pvalid n w p = true)
    (j : Fin n) : at' w (pinv n w p) j = (((toPerm n w p)⁻¹ j : Fin n) : Nat) := by
  obtain ⟨hlt, hinj⟩ := inj_of_pvalid hp
  have e : at' w p ((toPerm n w p)⁻¹ j : Fin n) = j := by
    rw [← toPerm_apply hp, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  rw [← e]
  exact at'_pinv hw hlt hinj _ (Fin.isLt _)

private theorem V_pinv {n w p : Nat} (hw : n ≤ 2 ^ w)
    (hp : canon1 n w p = true ∧ pvalid n w p = true) :
    canon1 n w (pinv n w p) = true ∧ pvalid n w (pinv n w p) = true := by
  refine ⟨(SP.unpackP_pinv hw hp.1).2, pvalid_of_inj hw (fun j hj => ?_) fun a ha b hb e => ?_⟩
  · rw [at'_pinv_eq hw hp.2 ⟨j, hj⟩]
    exact Fin.isLt _
  · rw [at'_pinv_eq hw hp.2 ⟨a, ha⟩, at'_pinv_eq hw hp.2 ⟨b, hb⟩] at e
    exact congrArg Fin.val ((toPerm n w p)⁻¹.injective (Fin.ext e))

private theorem toPerm_pinv {n w p : Nat} (hw : n ≤ 2 ^ w)
    (hp : canon1 n w p = true ∧ pvalid n w p = true) :
    toPerm n w (pinv n w p) = (toPerm n w p)⁻¹ := by
  ext j
  rw [toPerm_apply (V_pinv hw hp).2]
  exact at'_pinv_eq hw hp.2 j

private theorem V_pcomm {n w p q : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hp : canon1 n w p = true ∧ pvalid n w p = true)
    (hq : canon1 n w q = true ∧ pvalid n w q = true) :
    canon1 n w (pcomm n w p q) = true ∧ pvalid n w (pcomm n w p q) = true :=
  V_pc hn hw (V_pc hn hw hp hq) (V_pc hn hw (V_pinv hw hp) (V_pinv hw hq))

private theorem toPerm_pcomm {n w p q : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hp : canon1 n w p = true ∧ pvalid n w p = true)
    (hq : canon1 n w q = true ∧ pvalid n w q = true) :
    toPerm n w (pcomm n w p q) =
      toPerm n w p * toPerm n w q * (toPerm n w p)⁻¹ * (toPerm n w q)⁻¹ := by
  unfold pcomm
  rw [toPerm_pc hn hw (V_pc hn hw hp hq) (V_pc hn hw (V_pinv hw hp) (V_pinv hw hq)),
    toPerm_pc hn hw hp hq, toPerm_pc hn hw (V_pinv hw hp) (V_pinv hw hq), toPerm_pinv hw hp,
    toPerm_pinv hw hq]
  simp only [mul_assoc]

private theorem toPerm_pprod {n w : Nat} (h24 : n ≤ 2 ^ 24) (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) :
    ∀ {l : List Nat}, (∀ x ∈ l, canon1 n w x = true ∧ pvalid n w x = true) →
      toPerm n w (pprod n w l) = (l.map (toPerm n w)).prod
  | [], _ => toPerm_pid hw h24
  | a :: l, hl => by
    have ih := toPerm_pprod h24 hn hw (l := l) fun x hx => hl x (List.mem_cons_of_mem _ hx)
    change toPerm n w (pc n w a (pprod n w l)) = _
    rw [toPerm_pc hn hw (hl a List.mem_cons_self)
      (pvalid_pprod_proved h24 hn hw fun x hx => hl x (List.mem_cons_of_mem _ hx)), ih,
      List.map_cons, List.prod_cons]

private theorem eq_pc_pinv {n w X Q R : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hX : canon1 n w X = true) (hQ : canon1 n w Q = true ∧ pvalid n w Q = true)
    (h : pc n w X Q = R) : X = pc n w R (pinv n w Q) :=
  SP.eq_of_at' hX (SP.canon_pc hn hw) fun i hi => by
    have e1 := at'_pinv_eq hw hQ.2 ⟨i, hi⟩
    have e2 : at' w Q (at' w (pinv n w Q) i) = i := by
      rw [e1, ← toPerm_apply hQ.2, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have e3 : at' w (pinv n w Q) i < n := by
      rw [e1]
      exact Fin.isLt _
    have f1 : at' w (pc n w R (pinv n w Q)) i = at' w R (at' w (pinv n w Q) i) :=
      CFSG.KS.PF.pg_pcomp hn hi
    have f2 : at' w (pc n w X Q) (at' w (pinv n w Q) i) =
        at' w X (at' w Q (at' w (pinv n w Q) i)) := CFSG.KS.PF.pg_pcomp hn e3
    rw [f1, ← h, f2, e2]

private theorem maskProd_xor {M : Type} [Monoid M] (f : Nat → M) : ∀ (s : Nat),
    (∀ a < s, ∀ b < s, Commute (f a) (f b)) → (∀ a < s, f a * f a = 1) → ∀ k < s, ∀ i : Nat,
    (((List.range s).filter fun j => (i ^^^ 2 ^ k).testBit j).map f).prod =
      f k * (((List.range s).filter fun j => i.testBit j).map f).prod
  | 0, _, _, k, hk, _ => absurd hk (Nat.not_lt_zero k)
  | s + 1, hc, hi, k, hk, i => by
    have last : ∀ x : Nat, (((List.range (s + 1)).filter fun j => x.testBit j).map f).prod =
        (((List.range s).filter fun j => x.testBit j).map f).prod *
          (if x.testBit s = true then f s else 1) := by
      intro x
      rw [List.range_succ, List.filter_append, List.map_append, List.prod_append]
      cases hx : x.testBit s <;> simp [List.filter_cons, hx]
    rw [last, last]
    rcases Nat.lt_or_ge k s with hks | hks
    · rw [maskProd_xor f s (fun a ha b hb => hc a (by omega) b (by omega))
        (fun a ha => hi a (by omega)) k hks i, mul_assoc]
      have e : (i ^^^ 2 ^ k).testBit s = i.testBit s := by
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        simp [show k ≠ s by omega]
      rw [e]
    · obtain rfl : k = s := by omega
      have hf : ((List.range k).filter fun j => (i ^^^ 2 ^ k).testBit j) =
          (List.range k).filter fun j => i.testBit j := by
        refine List.filter_congr fun j hj => ?_
        have hjk : k ≠ j := by have := List.mem_range.1 hj; omega
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        simp [hjk]
      have e : (i ^^^ 2 ^ k).testBit k = !i.testBit k := by
        rw [Nat.testBit_xor, Nat.testBit_two_pow_self, Bool.xor_true]
      rw [hf, e]
      have hcomm : Commute (f k) (((List.range k).filter fun j => i.testBit j).map f).prod :=
        Commute.list_prod_right _ _ fun x hx => by
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
          exact hc k (by omega) j (by have := List.mem_range.1 (List.mem_filter.1 hj).1; omega)
      cases i.testBit k
      · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, mul_one]
        exact hcomm.eq.symm
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mul_one]
        rw [← hcomm.eq, ← mul_assoc, hi k (by omega), one_mul]

private theorem ppointsOK_of {n w : Nat} {gs : Array Nat} {c : ArrCertP} :
    ∀ (i : Nat) (us : List Nat) (es : List (Array Nat)) (ps ls : List Nat),
      (∀ j (hj : j < us.length),
        ppointAt n w gs c (i + j) us[j] (es.getD j #[]) (ps.getD j 0) (ls.getD j 0) = true) →
      ppointsOK n w gs c i us es ps ls = true
  | _, [], _, _, _, _ => rfl
  | i, u :: us, es, ps, ls, h => by
    simp only [ppointsOK, Bool.and_eq_true]
    refine ⟨?_, ppointsOK_of (i + 1) us es.tail ps.tail ls.tail fun j hj => ?_⟩
    · have h0 := h 0 (by simp)
      cases es <;> cases ps <;> cases ls <;> simpa using h0
    · have := h (j + 1) (by simpa using hj)
      have e1 : es.tail.getD j #[] = es.getD (j + 1) #[] := by cases es <;> simp
      have e2 : ∀ l : List Nat, l.tail.getD j 0 = l.getD (j + 1) 0 := fun l => by
        cases l <;> simp
      rw [e1, e2, e2, show i + 1 + j = i + (j + 1) by omega]
      simpa using this

private theorem getElem!_mapRange {α : Type} [Inhabited α] (f : Nat → α) {N x : Nat}
    (hx : x < N) : ((List.range N).map f).toArray[x]! = f x := by
  rw [getElem!_pos _ x (by simpa using hx)]
  simp

private theorem xor_log2 {j : Nat} (j0 : j ≠ 0) : (j - 2 ^ j.log2) ^^^ 2 ^ j.log2 = j := by
  have hL1 := Nat.log2_self_le j0
  have hL2 : j < 2 ^ (j.log2 + 1) := Nat.lt_log2_self
  rw [Nat.pow_succ] at hL2
  have hm : j - 2 ^ j.log2 = j % 2 ^ j.log2 := by
    rw [Nat.mod_eq_sub_mod hL1, Nat.mod_eq_of_lt (by omega)]
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy b j.log2 with hb | rfl | hb
  · simp [hb, show j.log2 ≠ b by omega]
  · have ht : j.testBit j.log2 = true := by
      by_contra hc
      have : j < 2 ^ j.log2 := Nat.lt_pow_two_of_testBit j fun i hi => by
        rcases Nat.eq_or_lt_of_le hi with rfl | hi'
        · simpa using hc
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by rw [Nat.pow_succ]; exact hL2)
            (Nat.pow_le_pow_right (by omega) hi'))
      omega
    simp [ht]
  · have hlt : j < 2 ^ b := Nat.lt_of_lt_of_le (by rw [Nat.pow_succ]; exact hL2)
      (Nat.pow_le_pow_right (by omega) hb)
    simp [show ¬ b < j.log2 by omega, show j.log2 ≠ b by omega, Nat.testBit_lt_two_pow hlt]

private theorem pwitF_order4 {n w : Nat} {ps : List Nat} {inX outX : Nat → Bool}
    {allowPW allowInX allowU : Bool} {basis : Array Nat} {cE : ArrCertP} {cs : Array ArrCertP}
    {aux : Nat × Nat} {e t c₁ c₂ m : Nat} (h24 : n ≤ 2 ^ 24) (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hX : ∀ P, inX P = true → canon1 n w P = true ∧ pvalid n w P = true)
    (hb : ∀ k < basis.size, canon1 n w basis[k]! = true ∧ pvalid n w basis[k]! = true)
    (ha : canon1 n w aux.1 = true ∧ canon1 n w aux.2 = true)
    (h : pwitF n w ps inX outX allowPW allowInX allowU basis cE cs aux
      (.order4 [⟨e, [⟨t, c₁, c₂⟩]⟩] m) = true) :
    pwitOK n w ps inX outX allowPW allowInX allowU basis cE cs
      (.order4 [⟨e, [⟨t, c₁, c₂⟩]⟩] m) = true := by
  have pmV : ∀ m, canon1 n w (pmask n w basis m) = true ∧ pvalid n w (pmask n w basis m) = true :=
    fun m => pvalid_pprod_proved h24 hn hw fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact hb k (List.mem_range.1 (List.mem_filter.1 hk).1)
  simp only [pwitF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hi1, hi2⟩, hT⟩, hc1⟩, hc2⟩, hA⟩, hB⟩, hE⟩, hY1⟩, hY2⟩ := h
  have v1 := hX c₁ hi1
  have v2 := hX c₂ hi2
  have vE := pmV e
  have eA := Nat.eq_of_beq_eq_true hA
  have eB := Nat.eq_of_beq_eq_true hB
  have eE := Nat.eq_of_beq_eq_true hE
  have vA : canon1 n w aux.1 = true ∧ pvalid n w aux.1 = true := by
    rw [eq_pc_pinv hn hw ha.1 (V_pc hn hw v2 v1) eA]
    exact V_pc hn hw (V_pc hn hw v1 v2) (V_pinv hw (V_pc hn hw v2 v1))
  have vB : canon1 n w aux.2 = true ∧ pvalid n w aux.2 = true := by
    rw [eq_pc_pinv hn hw ha.2 vA eB]
    exact V_pc hn hw (V_pid hw h24) (V_pinv hw vA)
  have sA : toPerm n w aux.1 * (toPerm n w c₂ * toPerm n w c₁) =
      toPerm n w c₁ * toPerm n w c₂ := by
    rw [← toPerm_pc hn hw v2 v1, ← toPerm_pc hn hw vA (V_pc hn hw v2 v1), eA,
      toPerm_pc hn hw v1 v2]
  have sB : toPerm n w aux.2 * toPerm n w aux.1 = 1 := by
    rw [← toPerm_pc hn hw vB vA, eB, toPerm_pid hw h24]
  have sE : toPerm n w (pmask n w basis e) * toPerm n w (pmask n w basis e) = 1 := by
    rw [← toPerm_pc hn hw vE vE, eE, toPerm_pid hw h24]
  have vG := V_pcomm hn hw v1 v2
  have mg : ∀ x ∈ [GFacP.mk t c₁ c₂].map (GFacP.val n w),
      canon1 n w x = true ∧ pvalid n w x = true := fun x hx => by
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
    subst hx
    exact vG
  have vg : canon1 n w (pgamma n w [⟨t, c₁, c₂⟩]) = true ∧
      pvalid n w (pgamma n w [⟨t, c₁, c₂⟩]) = true := pvalid_pprod_proved h24 hn hw mg
  have vN := V_pcomm hn hw vE vg
  have mN : ∀ x ∈ [NFacP.mk e [⟨t, c₁, c₂⟩]].map (NFacP.val n w basis),
      canon1 n w x = true ∧ pvalid n w x = true := fun x hx => by
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
    subst hx
    exact vN
  have vX := V_pc hn hw vE (V_pc hn hw vA (V_pc hn hw vE vB))
  have key : pnA n w basis [⟨e, [⟨t, c₁, c₂⟩]⟩] =
      pc n w (pmask n w basis e) (pc n w aux.1 (pc n w (pmask n w basis e) aux.2)) := by
    refine toPerm_inj (pvalid_pprod_proved h24 hn hw mN) vX ?_
    have hg : toPerm n w (pgamma n w [⟨t, c₁, c₂⟩]) = toPerm n w aux.1 := by
      unfold pgamma
      rw [toPerm_pprod h24 hn hw mg, List.map_cons, List.map_nil, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
      change toPerm n w (pcomm n w c₁ c₂) = _
      rw [toPerm_pcomm hn hw v1 v2, eq_mul_inv_of_mul_eq sA, mul_inv_rev]
      simp only [mul_assoc]
    unfold pnA
    rw [toPerm_pprod h24 hn hw mN, List.map_cons, List.map_nil, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    change toPerm n w (pcomm n w (pmask n w basis e) (pgamma n w [⟨t, c₁, c₂⟩])) = _
    rw [toPerm_pcomm hn hw vE vg, hg, toPerm_pc hn hw vE (V_pc hn hw vA (V_pc hn hw vE vB)),
      toPerm_pc hn hw vA (V_pc hn hw vE vB), toPerm_pc hn hw vE vB,
      inv_eq_of_mul_eq_one_right sE, ← eq_inv_of_mul_eq_one_left sB]
    simp only [mul_assoc]
  have vY := pvalid_pprod_proved h24 hn hw (l := List.replicate m
    (pc n w (pmask n w basis e) (pc n w aux.1 (pc n w (pmask n w basis e) aux.2))))
    fun x hx => (List.eq_of_mem_replicate hx) ▸ vX
  change canon1 n w (ppow n w _ m) = true ∧ pvalid n w (ppow n w _ m) = true at vY
  unfold pwitOK
  simp only [key, List.all_cons, List.all_nil, Bool.and_true, NFacP.ok, GFacP.ok,
    Bool.and_eq_true]
  generalize ppow n w (pc n w (pmask n w basis e)
    (pc n w aux.1 (pc n w (pmask n w basis e) aux.2))) m = Y at vY hY1 hY2 ⊢
  have eY := Nat.eq_of_beq_eq_true hY2
  have hrep : ∀ x ∈ List.replicate 4 Y, canon1 n w x = true ∧ pvalid n w x = true :=
    fun x hx => (List.eq_of_mem_replicate hx) ▸ vY
  have h4 : ppow n w Y 4 = pid n w := by
    refine toPerm_inj (pvalid_pprod_proved h24 hn hw hrep) (V_pid hw h24) ?_
    rw [← eY, toPerm_pc hn hw (V_pc hn hw vY vY) (V_pc hn hw vY vY), toPerm_pc hn hw vY vY]
    unfold ppow
    rw [toPerm_pprod h24 hn hw hrep, List.map_replicate, List.prod_replicate,
      show (4 : Nat) = 2 * 2 from rfl, pow_mul, sq, sq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hT, v1.2⟩, v2.2⟩, hi1⟩, hi2⟩, hc1⟩, hc2⟩, vE.2⟩, vg.2⟩, hY1⟩, ?_⟩
  rw [h4]
  exact Nat.beq_refl _

theorem penumF_sound {n w : Nat} {basis : Array Nat} {ps : List Nat} (h24 : n ≤ 2 ^ 24)
    (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hb : ∀ k < basis.size, canon1 n w basis[k]! = true ∧ pvalid n w basis[k]! = true)
    (h : penumF n w basis ps = true) : penumOK n w basis ps (pmaskCert n w basis) = true := by
  have hmV : ∀ m : Nat, ∀ x ∈ ((List.range basis.size).filter fun k => m.testBit k).map
      fun k => basis[k]!, canon1 n w x = true ∧ pvalid n w x = true := by
    intro m x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hb k (List.mem_range.1 (List.mem_filter.1 hk).1)
  have pmV : ∀ m, canon1 n w (pmask n w basis m) = true ∧ pvalid n w (pmask n w basis m) = true :=
    fun m => pvalid_pprod_proved h24 hn hw (hmV m)
  have pmP : ∀ m : Nat, toPerm n w (pmask n w basis m) =
      (((List.range basis.size).filter fun j => m.testBit j).map
        fun k => toPerm n w basis[k]!).prod := by
    intro m
    unfold pmask
    rw [toPerm_pprod h24 hn hw (hmV m), List.map_map]
    rfl
  unfold penumF at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.beq_eq] at h
  obtain ⟨⟨hinv, hcomm⟩, hasc⟩ := h
  have hc : ∀ a < basis.size, ∀ b < basis.size,
      Commute (toPerm n w basis[a]!) (toPerm n w basis[b]!) := by
    have key : ∀ a < basis.size, ∀ b < a,
        Commute (toPerm n w basis[a]!) (toPerm n w basis[b]!) := fun a ha b hba => by
      have e : pc n w basis[a]! basis[b]! = pc n w basis[b]! basis[a]! :=
        Nat.eq_of_beq_eq_true (hcomm a ha b hba)
      change toPerm n w basis[a]! * toPerm n w basis[b]! =
        toPerm n w basis[b]! * toPerm n w basis[a]!
      rw [← toPerm_pc hn hw (hb a ha) (hb b (by omega)), e,
        toPerm_pc hn hw (hb b (by omega)) (hb a ha)]
    intro a ha b hb'
    rcases Nat.lt_trichotomy a b with hab | rfl | hab
    · exact (key b hb' a hab).symm
    · exact Commute.refl _
    · exact key a ha b hab
  have hi : ∀ a < basis.size, toPerm n w basis[a]! * toPerm n w basis[a]! = 1 := fun a ha => by
    rw [← toPerm_pc hn hw (hb a ha) (hb a ha), hinv a ha, toPerm_pid hw h24]
  have edge : ∀ i, ∀ k < basis.size,
      pmask n w basis (i ^^^ 2 ^ k) = pc n w basis[k]! (pmask n w basis i) := fun i k hk =>
    toPerm_inj (pmV _) (V_pc hn hw (hb k hk) (pmV i)) (by
      rw [pmP, toPerm_pc hn hw (hb k hk) (pmV i), pmP]
      exact maskProd_xor (fun k => toPerm n w basis[k]!) basis.size hc hi k hk i)
  have hpts : (pmaskCert n w basis).pts =
      ((List.range (2 ^ basis.size)).map (pmask n w basis)).toArray := rfl
  have hedges : (pmaskCert n w basis).edges = ((List.range (2 ^ basis.size)).map fun i =>
      ((List.range basis.size).map fun k => i ^^^ 2 ^ k).toArray).toArray := rfl
  have hpar : (pmaskCert n w basis).par =
      ((List.range (2 ^ basis.size)).map fun i => i - 2 ^ Nat.log2 i).toArray := rfl
  have hlab : (pmaskCert n w basis).lab =
      ((List.range (2 ^ basis.size)).map Nat.log2).toArray := rfl
  have hsize : (pmaskCert n w basis).pts.size = 2 ^ basis.size := by
    rw [hpts]
    simp
  unfold penumOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq, Nat.beq_eq]
  refine ⟨fun k hk => (hb k hk).2, ⟨⟨⟨?_, ?_⟩, ?_⟩, hasc⟩⟩
  · rw [hsize]
    exact Nat.two_pow_pos _
  · rw [hpts, getElem!_mapRange _ (Nat.two_pow_pos _)]
    unfold pmask
    simp [Nat.zero_testBit, pprod]
  · apply ppointsOK_of
    intro j hj
    have hj' : j < 2 ^ basis.size := by simpa [hpts] using hj
    have hu : (pmaskCert n w basis).pts.toList[j] = pmask n w basis j := by
      simp [hpts]
    have he : (pmaskCert n w basis).edges.toList.getD j #[] =
        ((List.range basis.size).map fun k => j ^^^ 2 ^ k).toArray := by
      simp [hedges, hj']
    have hpa : (pmaskCert n w basis).par.toList.getD j 0 = j - 2 ^ Nat.log2 j := by
      simp [hpar, hj']
    have hla : (pmaskCert n w basis).lab.toList.getD j 0 = Nat.log2 j := by
      simp [hlab, hj']
    rw [hu, he, hpa, hla, Nat.zero_add]
    unfold ppointAt
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq,
      Nat.beq_eq, hsize]
    refine ⟨⟨⟨(pmV j).2, by simp⟩, fun k hk => ?_⟩, ?_⟩
    · rw [getElem!_mapRange _ hk]
      refine ⟨Nat.xor_lt_two_pow hj' (Nat.pow_lt_pow_right (by omega) hk), ?_⟩
      rw [hpts, getElem!_mapRange _ (Nat.xor_lt_two_pow hj' (Nat.pow_lt_pow_right (by omega) hk)),
        edge j k hk]
    · by_cases j0 : j = 0
      · exact Or.inl j0
      · right
        have hL1 := Nat.log2_self_le j0
        have hLs : j.log2 < basis.size := (Nat.log2_lt j0).2 hj'
        have hpos := Nat.two_pow_pos j.log2
        refine ⟨⟨by omega, hLs⟩, ?_⟩
        rw [hpts, getElem!_mapRange _ (by omega)]
        conv_lhs => rw [← xor_log2 j0]
        exact edge _ _ hLs

theorem pwitF_sound {n w : Nat} {ps : List Nat} {inX outX : Nat → Bool}
    {allowPW allowInX allowU : Bool} {basis : Array Nat} {cE : ArrCertP} {cs : Array ArrCertP}
    {aux : Nat × Nat} {wt : WitP} (h24 : n ≤ 2 ^ 24) (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hX : ∀ P, inX P = true → canon1 n w P = true ∧ pvalid n w P = true)
    (hb : ∀ k < basis.size, canon1 n w basis[k]! = true ∧ pvalid n w basis[k]! = true)
    (ha : canon1 n w aux.1 = true ∧ canon1 n w aux.2 = true)
    (h : pwitF n w ps inX outX allowPW allowInX allowU basis cE cs aux wt = true) :
    pwitOK n w ps inX outX allowPW allowInX allowU basis cE cs wt = true := by
  match wt, h with
  | .order4 [⟨e, [⟨t, c₁, c₂⟩]⟩] m, h => exact pwitF_order4 h24 hn hw hX hb ha h
  | .order4 [] _, h => exact h
  | .order4 [⟨_, []⟩] _, h => exact h
  | .order4 [⟨_, _ :: _ :: _⟩] _, h => exact h
  | .order4 (⟨_, []⟩ :: _ :: _) _, h => exact h
  | .order4 (⟨_, [_]⟩ :: _ :: _) _, h => exact h
  | .order4 (⟨_, _ :: _ :: _⟩ :: _ :: _) _, h => exact h
  | .twoGroup .., h => exact h
  | .perfect .., h => exact h
  | .inX, h => exact h
  | .small, h => exact h
  | .closing .., h => exact h

end CFSG.KC.Census
