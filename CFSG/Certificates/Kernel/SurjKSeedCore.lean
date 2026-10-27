module

public import CFSG.Certificates.Kernel.Co1M.VOrbitFull
public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.Certificates.Kernel.Co1BTrSound
public import Certificates.Data.Kernel.SurjK
public import Certificates.Data.CFSGNative.Bridge.SurjD

public section

namespace CFSG.KC.SurjSeed

open CFSG.KC.VecK CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

open CFSG.KC.VOrbFull (PInv size_le push_lt push_last)

theorem ofNat_ne_none' {x : Nat} (hx : x < 4294967295) : UInt32.ofNat x ≠ none32 := by
  intro e
  have h := congrArg UInt32.toNat e
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at h
  have h2 : (none32 ()).toNat = 4294967295 := rfl
  omega

theorem toNat_ofNat' {x : Nat} (hx : x < 4294967295) : (UInt32.ofNat x).toNat = x := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

variable {d n v0 : Nat} {R : Finset Nat}

theorem ins_inv {pos : Array UInt32} {pts : Array Nat} {x : Nat} (hR : R.card = n)
    (hn : n < 4294967295) (hRlt : ∀ y ∈ R, y < 2 ^ d) (H : PInv d v0 R pos pts) (hx : x ∈ R) :
    PInv d v0 R (if (pos[x]! == none32) = true then pos.set! x (UInt32.ofNat pts.size) else pos)
      (if (pos[x]! == none32) = true then pts.push x else pts) ∧
    pts.size ≤ (if (pos[x]! == none32) = true then pts.push x else pts).size ∧
    (∀ i < pts.size, (if (pos[x]! == none32) = true then pts.push x else pts)[i]! = pts[i]!) ∧
    ∃ i < (if (pos[x]! == none32) = true then pts.push x else pts).size,
      (if (pos[x]! == none32) = true then pts.push x else pts)[i]! = x ∧
      (if (pos[x]! == none32) = true then pos.set! x (UInt32.ofNat pts.size) else pos)[x]! =
        UInt32.ofNat i := by
  have hsz : pts.size ≤ n := hR ▸ size_le H.mem H.inj
  have hxd := hRlt x hx
  by_cases hc : ∃ i < pts.size, pts[i]! = x
  · obtain ⟨i, hi, rfl⟩ := hc
    have hget := H.hit i hi
    have hne : (pos[pts[i]!]! == none32) = false := by
      rw [hget]
      exact beq_false_of_ne (ofNat_ne_none' (by omega))
    have hc' : ¬ ((pos[pts[i]!]! == none32) = true) := by rw [hne]; exact Bool.false_ne_true
    rw [ite_eq_right hc', ite_eq_right hc']
    exact ⟨H, le_refl _, fun _ _ => rfl, i, hi, rfl, hget⟩
  · have hall : ∀ i < pts.size, pts[i]! ≠ x := fun i hi e => hc ⟨i, hi, e⟩
    have hmiss : pos[x]! = none32 := H.miss x hxd hall
    have hcond : (pos[x]! == none32) = true := by rw [hmiss]; exact beq_self_eq_true _
    rw [ite_eq_left hcond, ite_eq_left hcond]
    have hself : (pos.set! x (UInt32.ofNat pts.size))[x]! = UInt32.ofNat pts.size := by
      rw [Array.getElem!_set!_self _ _ _ (by rw [H.psz]; exact hxd)]
    have hs1 : (pts.push x).size = pts.size + 1 := by simp
    have hget : ∀ i < pts.size + 1, (pts.push x)[i]! = if i < pts.size then pts[i]! else x := by
      intro i hi
      by_cases h : i < pts.size
      · rw [push_lt _ _ h, ite_eq_left h]
      · have : i = pts.size := by omega
        subst this
        rw [push_last, ite_eq_right h]
    refine ⟨⟨by omega, ?_, fun i hi => ?_, fun i hi j hj e => ?_, by rw [Array.size_set!, H.psz],
      fun i hi => ?_, fun y hy hy' => ?_⟩, by omega, fun i hi => push_lt _ _ hi,
      pts.size, by omega, push_last _ _, hself⟩
    · rw [push_lt _ _ H.pos0]
      exact H.p0
    · rw [hs1] at hi
      rw [hget i hi]
      split
      · exact H.mem i (by assumption)
      · exact hx
    · rw [hs1] at hi hj
      rw [hget i hi, hget j hj] at e
      by_cases h1 : i < pts.size <;> by_cases h2 : j < pts.size
      · rw [ite_eq_left h1, ite_eq_left h2] at e
        exact H.inj i h1 j h2 e
      · rw [ite_eq_left h1, ite_eq_right h2] at e
        exact absurd e (hall i h1)
      · rw [ite_eq_right h1, ite_eq_left h2] at e
        exact absurd e.symm (hall j h2)
      · omega
    · rw [hs1] at hi
      rw [hget i hi]
      by_cases h1 : i < pts.size
      · rw [ite_eq_left h1, Array.getElem!_set!_ne _ _ _ _ (fun e => hall i h1 e.symm)]
        exact H.hit i h1
      · rw [ite_eq_right h1, hself]
        congr 1
        omega
    · have hyx : x ≠ y := fun e => by
        subst e
        exact hy' pts.size (by omega) (push_last _ _)
      rw [Array.getElem!_set!_ne _ _ _ _ hyx]
      refine H.miss y hy fun i hi e => hy' i (by omega) ?_
      rw [push_lt _ _ hi, e]

structure FInv (d v0 : Nat) (R : Finset Nat) (cA cB : Array Nat) (h : Nat) (s : VSt) : Prop where
  pt : PInv d v0 R s.1 s.2.1
  h_le : h ≤ s.2.1.size
  asz : s.2.2.1.size = h
  bsz : s.2.2.2.size = h
  aok : ∀ j < h, ap s.2.2.1 j < s.2.1.size ∧ s.2.1[ap s.2.2.1 j]! = vecMulN d cA s.2.1[j]!
  bok : ∀ j < h, ap s.2.2.2 j < s.2.1.size ∧ s.2.1[ap s.2.2.2 j]! = vecMulN d cB s.2.1[j]!

variable {cA cB : Array Nat}

theorem table_step {pts pts2 : Array Nat} {al : Table} {h i : Nat} {f : Nat → Nat}
    (hal : al.size = h) (hlt : h < pts.size) (hsz : pts.size ≤ pts2.size)
    (hpre : ∀ j < pts.size, pts2[j]! = pts[j]!) (hi : i < pts2.size) (hi30 : i < 4294967295)
    (hpi : pts2[i]! = f pts[h]!)
    (hold : ∀ j < h, ap al j < pts.size ∧ pts[ap al j]! = f pts[j]!) :
    ∀ j < h + 1, ap (al.push (UInt32.ofNat i)) j < pts2.size ∧
      pts2[ap (al.push (UInt32.ofNat i)) j]! = f pts2[j]! := by
  intro j hj
  have e : ap (al.push (UInt32.ofNat i)) j = if j < h then ap al j else i := by
    unfold ap
    by_cases h1 : j < h
    · rw [push_lt _ _ (by omega), ite_eq_left h1]
    · have : j = h := by omega
      subst this
      rw [ite_eq_right h1, ← hal, push_last, toNat_ofNat' hi30]
  rw [e, hpre j (by omega)]
  by_cases h1 : j < h
  · rw [ite_eq_left h1]
    obtain ⟨a1, a2⟩ := hold j h1
    exact ⟨by omega, by rw [hpre _ a1, a2]⟩
  · rw [ite_eq_right h1]
    have : j = h := by omega
    subst this
    exact ⟨hi, hpi⟩

theorem step_inv (hR : R.card = n) (hn : n < 4294967295) (hRlt : ∀ y ∈ R, y < 2 ^ d)
    (hA : ∀ x ∈ R, vecMulN d cA x ∈ R) (hB : ∀ x ∈ R, vecMulN d cB x ∈ R) (h : Nat) (s : VSt)
    (H : FInv d v0 R cA cB h s) :
    (∃ s', vBody d cA cB h s = pure (.yield s') ∧ FInv d v0 R cA cB (h + 1) s') ∨
      (∃ s', vBody d cA cB h s = pure (.done s') ∧ FInv d v0 R cA cB s'.2.1.size s') := by
  rcases s with ⟨pos, pts, al, be⟩
  obtain ⟨Hp, hle, has, hbs, hao, hbo⟩ := H
  dsimp only at Hp hle has hbs hao hbo
  by_cases hlt : h < pts.size
  · left
    have hv := Hp.mem h hlt
    obtain ⟨H1, hs1, hpre1, i1, hi1, hpi1, hpos1⟩ := ins_inv hR hn hRlt Hp (hA _ hv)
    obtain ⟨H2, hs2, hpre2, i2, hi2, hpi2, hpos2⟩ := ins_inv hR hn hRlt H1 (hB _ hv)
    have hsz2 := hR ▸ size_le H2.mem H2.inj
    unfold vBody
    rw [ite_eq_left hlt]
    simp only [vIns_eq]
    refine ⟨_, rfl, ⟨H2, by dsimp only; omega, by simp [has], by simp [hbs],
      ?_, ?_⟩⟩
    · dsimp only
      rw [hpos1]
      refine table_step has hlt (by omega) ?_ (by omega) (by omega) ?_ hao
      · intro j hj
        rw [hpre2 j (by omega), hpre1 j hj]
      · rw [hpre2 i1 hi1, hpi1]
    · dsimp only
      rw [hpos2]
      refine table_step hbs hlt (by omega) ?_ hi2 (by omega) hpi2 hbo
      intro j hj
      rw [hpre2 j (by omega), hpre1 j hj]
  · right
    unfold vBody
    simp only [hlt, ite_false]
    have : h = pts.size := by omega
    subst this
    exact ⟨_, rfl, ⟨Hp, hle, has, hbs, hao, hbo⟩⟩

private theorem forIn_range_inv {β : Type} (P : Nat → β → Prop) (Q : β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → P j b →
      (∃ b', f j b = pure (.yield b') ∧ P (j + 1) b') ∨ (∃ b', f j b = pure (.done b') ∧ Q b'))
    (hE : ∀ b, P E b → Q b) :
    ∀ k a (init : β), a + k = E → P a init → Q (forIn (List.range' a k) init f)
  | 0, a, init, hk, h => by
    rw [List.range'_zero, List.forIn_nil]
    rw [Nat.add_zero] at hk
    subst hk
    exact hE init h
  | k + 1, a, init, hk, h => by
    rcases hf a init (by omega) h with ⟨b', hb, hR⟩ | ⟨b', hb, hQ⟩
    · rw [List.range'_succ, List.forIn_cons, hb]
      exact forIn_range_inv P Q E f hf hE k (a + 1) b' (by omega) hR
    · rw [List.range'_succ, List.forIn_cons, hb]
      exact hQ

theorem vOrbitBFS_full (hR : R.card = n) (hn : n < 4294967295) (hRlt : ∀ y ∈ R, y < 2 ^ d)
    (hv0 : v0 ∈ R) (hA : ∀ x ∈ R, vecMulN d cA x ∈ R) (hB : ∀ x ∈ R, vecMulN d cB x ∈ R)
    (hmin : ∀ S : Set Nat, v0 ∈ S → (∀ x ∈ S, vecMulN d cA x ∈ S ∧ vecMulN d cB x ∈ S) →
      ∀ x ∈ R, x ∈ S) :
    (vOrbitBFS d cA cB v0 n).pts.size = n ∧ (vOrbitBFS d cA cB v0 n).alpha.size = n ∧
      (vOrbitBFS d cA cB v0 n).beta.size = n ∧ (vOrbitBFS d cA cB v0 n).pts[0]! = v0 ∧
      (∀ i < n, (vOrbitBFS d cA cB v0 n).pts[i]! ∈ R) ∧
      (∀ i < n, ∀ j < n, (vOrbitBFS d cA cB v0 n).pts[i]! = (vOrbitBFS d cA cB v0 n).pts[j]! →
        i = j) ∧
      (∀ i < n, ap (vOrbitBFS d cA cB v0 n).alpha i < n ∧
        (vOrbitBFS d cA cB v0 n).pts[ap (vOrbitBFS d cA cB v0 n).alpha i]! =
          vecMulN d cA (vOrbitBFS d cA cB v0 n).pts[i]!) ∧
      (∀ i < n, ap (vOrbitBFS d cA cB v0 n).beta i < n ∧
        (vOrbitBFS d cA cB v0 n).pts[ap (vOrbitBFS d cA cB v0 n).beta i]! =
          vecMulN d cB (vOrbitBFS d cA cB v0 n).pts[i]!) := by
  have hv0d := hRlt v0 hv0
  have hrs : (Array.replicate (1 <<< d) (none32 ())).size = 2 ^ d := by
    rw [Array.size_replicate, Nat.one_shiftLeft]
  have hinit : FInv d v0 R cA cB 0 ((Array.replicate (1 <<< d) none32).set! v0 0, #[v0], #[], #[]) :=
    ⟨⟨by simp, rfl, fun i hi => by
        have : i = 0 := by simpa using hi
        subst this
        exact hv0,
      fun i hi j hj _ => by simp at hi hj; omega, by rw [Array.size_set!, hrs],
      fun i hi => by
        have : i = 0 := by simpa using hi
        subst this
        change ((Array.replicate (1 <<< d) none32).set! v0 0)[v0]! = UInt32.ofNat 0
        rw [Array.getElem!_set!_self _ _ _ (by rw [hrs]; exact hv0d)]
        rfl,
      fun x hx hall => by
        have hne : v0 ≠ x := fun e => hall 0 (by simp) (by rw [← e]; rfl)
        change ((Array.replicate (1 <<< d) none32).set! v0 0)[x]! = none32
        rw [Array.getElem!_set!_ne _ _ _ _ hne, getElem!_pos _ x (by rw [hrs]; exact hx)]
        simp⟩,
      Nat.zero_le _, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hfin := forIn_range_inv (FInv d v0 R cA cB) (fun s => FInv d v0 R cA cB s.2.1.size s) n
    (vBody d cA cB) (fun j b _ H => step_inv hR hn hRlt hA hB j b H)
    (fun b H => by
      have h1 := H.h_le
      have h2 := hR ▸ size_le H.pt.mem H.pt.inj
      have : b.2.1.size = n := by omega
      rw [this]
      exact H) n 0 _ (Nat.zero_add n) hinit
  rw [vOrbitBFS_eq, Std.Legacy.Range.forIn_eq_forIn_range']
  have hr : ([0:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  simp only [hr]
  generalize (forIn (List.range' 0 n) _ (vBody d cA cB) : Id VSt) = s at hfin
  obtain ⟨Hp, -, has, hbs, hao, hbo⟩ := hfin
  set m := s.2.1.size with hm
  have hcl : ∀ x ∈ R, ∃ i < m, s.2.1[i]! = x := by
    refine hmin {x | ∃ i < m, s.2.1[i]! = x} ⟨0, Hp.pos0, Hp.p0⟩ ?_
    rintro x ⟨i, hi, rfl⟩
    exact ⟨⟨_, (hao i hi).1, (hao i hi).2⟩, ⟨_, (hbo i hi).1, (hbo i hi).2⟩⟩
  have hmn : m = n := by
    have h1 : m ≤ n := hR ▸ size_le Hp.mem Hp.inj
    have h2 : R ⊆ (Finset.range m).image fun i => s.2.1[i]! := by
      intro x hx
      obtain ⟨i, hi, e⟩ := hcl x hx
      exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, e⟩
    have h3 := (Finset.card_le_card h2).trans Finset.card_image_le
    rw [Finset.card_range, hR] at h3
    omega
  rw [hmn] at has hbs hao hbo
  refine ⟨hmn, has, hbs, Hp.p0, fun i hi => Hp.mem i (by omega),
    fun i hi j hj e => Hp.inj i (by omega) j (by omega) e, fun i hi => ?_, fun i hi => ?_⟩
  · exact hao i hi
  · exact hbo i hi

end CFSG.KC.SurjSeed


namespace CFSG.KC.SurjSeed

open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.SurjK
  CFSG.Sporadic.SmallF2.Native
open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply toVecD_injective rowsMatrix rowsMatrix_mulRows
  rowsMatrix_idRows rowsMatrix_apply rowsMatrix_mulVec)
open scoped Matrix

theorem parB_succ (d X : Nat) :
    parB (d + 1) X = if X.testBit d then parB d X ^^^ 1 else parB d X := by
  change nIf(bit X d, Nat.xor (parB d X) 1, parB d X) = _
  rw [bit_eq]
  cases X.testBit d <;> rfl

theorem parB_le (d X : Nat) : parB d X = 0 ∨ parB d X = 1 := by
  induction d with
  | zero => exact Or.inl rfl
  | succ d ih =>
    rw [parB_succ]
    split
    · rcases ih with h | h <;> rw [h] <;> simp
    · exact ih

theorem parB_cast (d X : Nat) :
    ((parB d X : Nat) : ZMod 2) = ∑ i ∈ Finset.range d, if X.testBit i then 1 else 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [parB_succ, Finset.sum_range_succ, ← ih]
    split
    · rcases parB_le d X with h | h <;> rw [h] <;> decide
    · simp

theorem mvK_eq (d M v : Nat) : mvK d M v = orN d fun i =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0) (pw2 i)
      (decide (parB d (Nat.land (rowF d M i) v) = 1)) := by
  unfold mvK
  congr 1
  funext i
  rcases parB_le d (Nat.land (rowF d M i) v) with h | h
  · rw [h]
    change (0 <<< i : Nat) = 0
    exact Nat.zero_shiftLeft i
  · rw [h]; rfl

theorem testBit_mvK (d M v j : Nat) : (mvK d M v).testBit j =
    (decide (j < d) && decide (parB d (Nat.land (rowF d M j) v) = 1)) := by
  rw [mvK_eq, testBit_orN_bits]

theorem mvK_lt (d M v : Nat) : mvK d M v < 2 ^ d :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by
    rw [testBit_mvK]; simp [Nat.not_lt.2 hk]

noncomputable def Mat (d M : Nat) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  rowsMatrix d (unpackR d M)

theorem toVecD_mvK (d M v : Nat) : toVecD d (mvK d M v) = Mat d M *ᵥ toVecD d v := by
  funext j
  rw [toVecD_apply, testBit_mvK]
  simp only [j.isLt, decide_true, Bool.true_and, Matrix.mulVec, dotProduct, Mat,
    rowsMatrix_apply]
  have h1 : (if decide (parB d (Nat.land (rowF d M j) v) = 1) = true then (1 : ZMod 2) else 0) =
      ((parB d (Nat.land (rowF d M j) v) : Nat) : ZMod 2) := by
    rcases parB_le d (Nat.land (rowF d M j) v) with h | h <;> rw [h] <;> simp
  rw [h1, parB_cast, ← Fin.sum_univ_eq_sum_range (fun i =>
    if (Nat.land (rowF d M j) v).testBit i then (1 : ZMod 2) else 0) d]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hr : (unpackR d M)[j.val]?.getD 0 = rowF d M j := by simp [unpackR, j.isLt, rowF_eq]
  rw [hr, toVecD_apply, toVecD_apply]
  have : Nat.land (rowF d M j) v = rowF d M j &&& v := rfl
  rw [this, Nat.testBit_and]
  cases (rowF d M j).testBit k <;> cases v.testBit k <;> simp

theorem unpackR_idF_gen (d : Nat) : unpackR d (idF d) = idRows d := by
  have hI : idF d = orN d fun i => pw2 i <<< (d * i) := rfl
  rw [idRows, unpackR]
  congr 1
  funext i
  have hlt : ∀ i < d, pw2 i < 2 ^ d := fun i hi => by
    change 1 <<< i < 2 ^ d
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by omega) hi
  rw [← rowF_eq, hI, rowF_orN d hlt i.isLt]
  rfl

theorem Mat_mul (d X Y : Nat) : Mat d (mulF d X Y) = Mat d X * Mat d Y := by
  unfold Mat
  rw [← mulRows_unpackR, rowsMatrix_mulRows]

theorem Mat_id (d : Nat) : Mat d (idF d) = 1 := by
  unfold Mat
  rw [unpackR_idF_gen, rowsMatrix_idRows]

theorem mvK_mul (d X Y v : Nat) : mvK d (mulF d X Y) v = mvK d X (mvK d Y v) := by
  apply toVecD_injective (mvK_lt d _ _) (mvK_lt d _ _)
  rw [toVecD_mvK, toVecD_mvK, toVecD_mvK, Mat_mul, Matrix.mulVec_mulVec]

theorem mvK_id {d v : Nat} (hv : v < 2 ^ d) : mvK d (idF d) v = v := by
  apply toVecD_injective (mvK_lt d _ _) hv
  rw [toVecD_mvK, Mat_id, Matrix.one_mulVec]

theorem mvK_inv {d M N v : Nat} (h : mulF d M N = idF d) (hv : v < 2 ^ d) :
    mvK d N (mvK d M v) = v := by
  have h1 : Mat d M * Mat d N = 1 := by rw [← Mat_mul, h, Mat_id]
  have h2 : Mat d N * Mat d M = 1 := mul_eq_one_comm.1 h1
  apply toVecD_injective (mvK_lt d _ _) hv
  rw [toVecD_mvK, toVecD_mvK, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

theorem vecMulN_lt {d : Nat} (R : Array Nat) (hR : ∀ j : Nat, R[j]?.getD 0 < 2 ^ d) (v : Nat) :
    vecMulN d R v < 2 ^ d := by
  have key : ∀ (m acc : Nat), acc < 2 ^ d →
      (List.range m).foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc)
        acc < 2 ^ d := by
    intro m
    induction m with
    | zero => intro acc h; simpa using h
    | succ m ih =>
      intro acc h
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have := ih acc h
      split_ifs
      · exact Nat.xor_lt_two_pow this (hR m)
      · exact this
  exact key d 0 (Nat.two_pow_pos d)

theorem cols_lt' (d : Nat) (M : Array Nat) (j : Nat) :
    (transposeRows d M)[j]?.getD 0 < 2 ^ d := by
  unfold transposeRows
  by_cases hj : j < d
  · simp only [Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
    exact CFSG.Sporadic.SmallF2.ofBits_lt _ _
  · simp [hj]

theorem vecMulN_cols {d M : Nat} {cs : List Char} (hb : m1Bind cs d M = true) (v : Nat) :
    vecMulN d (transposeRows d (rowsOfPayload d (String.ofList cs))) v = mvK d M v := by
  apply toVecD_injective (vecMulN_lt _ (cols_lt' d _) v) (mvK_lt d _ _)
  rw [← rowsMatrix_mulVec, bind_sound hb, toVecD_mvK]
  rfl

open CFSG.Sporadic.Th.Native
open CFSG.KS.TW (TR idT_TR invT_TR invOK_of allIn_iff)

def Rep (d n : Nat) (pts : Array Nat) (M : Nat) (T : Table) : Prop :=
  T.size = n ∧ ∀ i < n, ap T i < n ∧ pts[ap T i]! = mvK d M pts[i]!

structure Good (d n : Nat) (pts : Array Nat) : Prop where
  n32 : n < 4294967295
  lt : ∀ i < n, pts[i]! < 2 ^ d
  inj : ∀ i < n, ∀ j < n, pts[i]! = pts[j]! → i = j

variable {d n : Nat} {pts : Array Nat}

theorem Rep.id (G : Good d n pts) : Rep d n pts (idF d) (idT n) := by
  obtain ⟨hs, hv⟩ := idT_TR (n := n) (by have := G.n32; omega)
  refine ⟨hs, fun i hi => ?_⟩
  obtain ⟨h1, h2⟩ := hv i hi
  exact ⟨by rw [h1]; exact h2, by rw [h1, mvK_id (G.lt i hi)]⟩

theorem Rep.ext (G : Good d n pts) {M : Nat} {T T' : Table} (h : Rep d n pts M T)
    (h' : Rep d n pts M T') : T = T' := by
  apply Array.ext (by rw [h.1, h'.1])
  intro i h1 h2
  have hi : i < n := by rw [← h.1]; exact h1
  have e : ap T i = ap T' i := by
    refine G.inj _ ((h.2 i hi).1) _ ((h'.2 i hi).1) ?_
    rw [(h.2 i hi).2, (h'.2 i hi).2]
  unfold ap at e
  rw [getElem!_pos T i h1, getElem!_pos T' i h2] at e
  exact UInt32.toNat_inj.1 e

theorem Rep.cons (G : Good d n pts) {M N : Nat} {T L : Table} (hT : Rep d n pts M T)
    (hL : Rep d n pts N L) :
    Rep d n pts (mulF d N M) (T.map fun t => L[t.toNat]!) := by
  refine ⟨by simp [hT.1], fun i hi => ?_⟩
  obtain ⟨a1, a2⟩ := hT.2 i hi
  obtain ⟨b1, b2⟩ := hL.2 _ a1
  have e : ap (T.map fun t => L[t.toNat]!) i = ap L (ap T i) := by
    unfold ap
    rw [getElem!_pos _ i (by rw [Array.size_map, hT.1]; exact hi), Array.getElem_map,
      ← getElem!_pos T i (by rw [hT.1]; exact hi)]
  rw [e, mvK_mul, ← a2]
  exact ⟨b1, b2⟩

theorem Rep.word (G : Good d n pts) (F : Int → Nat) (L : Int → Table) :
    ∀ w : List Int, (∀ z ∈ w, Rep d n pts (F z) (L z)) →
      Rep d n pts (matW d F w) (wordT n L w)
  | [], _ => by
    change Rep d n pts (idF d) (idT n)
    exact Rep.id G
  | l :: w, h => by
    have e : wordT n L (l :: w) = (wordT n L w).map fun t => (L l)[t.toNat]! := rfl
    have e2 : matW d F (l :: w) = mulF d (F l) (matW d F w) := by
      change strictN (matW d F w) (fun T => mulF d (F l) T) = _
      rw [strictN_eq]
    rw [e, e2]
    exact Rep.cons G (Rep.word G F L w fun z hz => h z (List.mem_cons_of_mem l hz))
      (h l List.mem_cons_self)

theorem Rep.inv (G : Good d n pts) {M N : Nat} {T : Table} (hT : Rep d n pts M T)
    (h : mulF d M N = idF d) :
    Rep d n pts N (invT n T) ∧ invOK n T (invT n T) = true := by
  have hinj : ∀ i < n, ∀ j < n, ap T i = ap T j → i = j := by
    intro i hi j hj e
    refine G.inj i hi j hj ?_
    have := congrArg (fun x => mvK d N (pts[x]!)) e
    simp only [(hT.2 i hi).2, (hT.2 j hj).2, mvK_inv h (G.lt i hi), mvK_inv h (G.lt j hj)] at this
    exact this
  have hsurj : ∀ j < n, ∃ i < n, ap T i = j := by
    have := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
      (fun i _ => ap T i) (fun i hi => Finset.mem_range.2 (hT.2 i (Finset.mem_range.1 hi)).1)
      (fun i j hi hj e => hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e) le_rfl
    intro j hj
    obtain ⟨i, hi, e⟩ := this j (Finset.mem_range.2 hj)
    exact ⟨i, Finset.mem_range.1 hi, e.symm⟩
  classical
  let g : Nat → Nat := fun j => if hj : ∃ i < n, ap T i = j then Classical.choose hj else 0
  have hg1 : ∀ j < n, g j < n ∧ ap T (g j) = j := by
    intro j hj
    have hex := hsurj j hj
    simp only [g, dif_pos hex]
    exact Classical.choose_spec hex
  have hg : ∀ j < n, g j < n ∧ ap T (g j) = j ∧ g (ap T j) = j := by
    intro j hj
    obtain ⟨a, b⟩ := hg1 j hj
    refine ⟨a, b, ?_⟩
    have := hg1 (ap T j) (hT.2 j hj).1
    exact hinj _ this.1 _ hj this.2
  have hn2 : n < 2 ^ 32 := by have := G.n32; omega
  have hP : TR n T (ap T) := ⟨hT.1, fun i hi => ⟨rfl, (hT.2 i hi).1⟩⟩
  have hR := invT_TR hn2 hP hg
  refine ⟨⟨hR.1, fun j hj => ?_⟩, invOK_of hP hR fun i hi => (hg i hi).2.2⟩
  obtain ⟨y1, y2⟩ := hR.2 j hj
  rw [y1]
  obtain ⟨a, b⟩ := hg1 j hj
  refine ⟨a, ?_⟩
  have h2 := (hT.2 (g j) a).2
  rw [b] at h2
  rw [h2, mvK_inv h (G.lt _ a)]

theorem strictB_id (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem rec_and (a b : Bool) : (Bool.rec (motive := fun _ => Bool) false b a) = (a && b) := by
  cases a <;> rfl

theorem rec_ifB (c t e : Bool) : (Bool.rec (motive := fun _ => Bool) e t c) = cond c t e := by
  cases c <;> rfl

theorem rec_ifN (c : Bool) (t e : Nat) : (Bool.rec (motive := fun _ => Nat) e t c) = cond c t e := by
  cases c <;> rfl

theorem orbStep_facts {d n A B v0 : Nat} {PT PA LB AP BP SO SOI : Nat → Nat} {k : Nat}
    (h : orbStep d n A B v0 PT PA LB AP BP SO SOI k = true) :
    PT k < 2 ^ d ∧ (k = 0 → PT k = v0) ∧
      (k ≠ 0 → PA k < k ∧ LB k < 2 ∧
        PT k = mvK d (if LB k = 0 then A else B) (PT (PA k))) ∧
      AP k < n ∧ PT (AP k) = mvK d A (PT k) ∧ BP k < n ∧ PT (BP k) = mvK d B (PT k) ∧
      SO k < n ∧ SOI k < n ∧ SO (SOI k) = k ∧
      (k + 1 < n → PT (SO k) < PT (SO (k + 1))) := by
  unfold orbStep at h
  simp only [strictB_id, rec_and, rec_ifB, rec_ifN, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    cond_eq_if, Nat.shiftLeft_eq, Nat.one_mul, beq_iff_eq] at h
  simp [Nat.beq_eq, Nat.blt_eq, Nat.succ_eq_add_one] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11⟩ := h
  rw [Nat.one_shiftLeft] at h1
  refine ⟨h1, fun hk => ?_, fun hk => ?_, h3, h4, h5, h6, h7, h8, h9, fun hk => ?_⟩
  · rw [if_pos hk] at h2
    exact h2
  · rw [if_neg hk] at h2
    exact ⟨h2.1, by omega, h2.2.2⟩
  · rcases h11 with h | h
    · omega
    · exact h

open CFSG.Sporadic.Bridge.SurjD.Native
open CFSG.KS (lget)

theorem checks_of {D : VecData} {S : Spec} {A B AI BI : Nat} {Ims ImsI : List Nat}
    {Li Ls : List (List Int)} {α β : Table} (G : Good D.d D.n pts)
    (hα : Rep D.d D.n pts A α) (hβ : Rep D.d D.n pts B β)
    (hAI : mulF D.d A AI = idF D.d) (hBI : mulF D.d B BI = idF D.d)
    (hm : S.m = Ims.length)
    (hi : S.imgWords = Li.toArray) (hs : S.surjWords = Ls.toArray) (hli : Li.length = S.m)
    (hls : Ls.length = 2)
    (hbase : Li.all (fun w => w.all fun z => decide (0 ≤ z) && decide (z < 4)) = true)
    (himg : ∀ k < S.m, matW D.d (baseF A AI B BI) (Li.getD k []) = lget Ims k)
    (hinv : ∀ k < S.m, mulF D.d (lget Ims k) (lget ImsI k) = idF D.d)
    (hrel : S.rels.all (fun r => r.all (fun l => decide (l.1 < S.m)) &&
      Nat.beq (matW D.d (imgF Ims ImsI) (r.map letterOf)) (idF D.d)) = true)
    (hsl : Ls.all (fun w => w.all fun z => z != 0 && decide (z.natAbs ≤ S.m)) = true)
    (hsA' : matW D.d (imgF Ims ImsI) (Ls.getD 0 []) = A)
    (hsB' : matW D.d (imgF Ims ImsI) (Ls.getD 1 []) = B) :
    wordChecks D.n S #[α, invT D.n α, β, invT D.n β] α β = true := by
  have hαI := (Rep.inv G hα hAI).1
  have hβI := (Rep.inv G hβ hBI).1
  have hbl : ∀ z : Int, 0 ≤ z → z < 4 →
      Rep D.d D.n pts (baseF A AI B BI z) (baseLetter #[α, invT D.n α, β, invT D.n β] z) := by
    intro z h0 h4
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have : k < 4 := by omega
    interval_cases k
    · exact hα
    · exact hαI
    · exact hβ
    · exact hβI
  have hLi : ∀ k < S.m, ∀ z ∈ Li.getD k [], 0 ≤ z ∧ z < 4 := by
    intro k hk z hz
    have hmem : Li.getD k [] ∈ Li := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have h1 := List.all_eq_true.1 hbase _ hmem
    have h2 := List.all_eq_true.1 h1 z hz
    simpa using h2
  unfold wordChecks inverseChecks
  generalize hG4 : (#[α, invT D.n α, β, invT D.n β] : Array Table) = G4 at hbl ⊢
  have hIeq : S.imgWords.map (wordT D.n (baseLetter G4)) =
      (Li.map (wordT D.n (baseLetter G4))).toArray := by
    rw [hi, List.map_toArray]
  have hIk : ∀ k < S.m, (S.imgWords.map (wordT D.n (baseLetter G4)))[k]!
      = wordT D.n (baseLetter G4) (Li.getD k []) := by
    intro k hk
    have hk' : k < Li.length := by omega
    rw [hIeq, getElem!_pos _ k (by simp; omega), List.getD_eq_getElem _ _ hk']
    simp
  have hIsize : (S.imgWords.map (wordT D.n (baseLetter G4))).size = S.m := by
    rw [hIeq]; simpa using hli
  have hRI : ∀ k < S.m, Rep D.d D.n pts (lget Ims k)
      (S.imgWords.map (wordT D.n (baseLetter G4)))[k]! := by
    intro k hk
    rw [hIk k hk]
    have := Rep.word G (baseF A AI B BI) (baseLetter G4) (Li.getD k []) fun z hz =>
      hbl z (hLi k hk z hz).1 (hLi k hk z hz).2
    rwa [himg k hk] at this
  generalize S.imgWords.map (wordT D.n (baseLetter G4)) = I at hIsize hRI ⊢
  have hIv : ∀ k < S.m, Rep D.d D.n pts (lget ImsI k) (I.map (invT D.n))[k]! ∧
      invOK D.n I[k]! (I.map (invT D.n))[k]! = true := by
    intro k hk
    have h := Rep.inv G (hRI k hk) (hinv k hk)
    have e : (I.map (invT D.n))[k]! = invT D.n I[k]! := by
      rw [getElem!_pos _ k (by simp; omega), Array.getElem_map, ← getElem!_pos I k (by omega)]
    rw [e]
    exact h
  have hG4s : G4.size = 4 := by rw [← hG4]; rfl
  have hlet : ∀ z : Int, z ≠ 0 → z.natAbs ≤ S.m →
      Rep D.d D.n pts (imgF Ims ImsI z) (imgLetter I (I.map (invT D.n)) z) := by
    intro z hz0 hzm
    unfold imgF imgLetter
    have hb : Nat.blt 0 z.natAbs = true := by simp [Nat.blt_eq]; omega
    simp only [rec_ifN, hb, cond_true]
    by_cases h : 0 < z
    · have e : (z - 1).toNat = z.natAbs - 1 := by omega
      simp only [h, decide_true, cond_true, if_true, e]
      exact hRI _ (by omega)
    · have e : (-z - 1).toNat = z.natAbs - 1 := by omega
      simp only [h, decide_false, cond_false, if_false, e]
      exact (hIv _ (by omega)).1
  have hrels : ∀ r ∈ S.rels, (∀ l ∈ r, l.1 < S.m) ∧
      matW D.d (imgF Ims ImsI) (r.map letterOf) = idF D.d := by
    intro r hr
    have h := List.all_eq_true.1 hrel r hr
    rw [Bool.and_eq_true] at h
    exact ⟨fun l hl => by simpa using List.all_eq_true.1 h.1 l hl, Nat.eq_of_beq_eq_true h.2⟩
  have hrelL : ∀ r ∈ S.rels, ∀ z ∈ r.map letterOf, z ≠ 0 ∧ z.natAbs ≤ S.m := by
    intro r hr z hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    have := (hrels r hr).1 l hl
    unfold letterOf
    split <;> omega
  have hsw : ∀ k, k < 2 → S.surjWords[k]! = Ls.getD k [] := by
    intro k hk
    have hk' : k < Ls.length := by omega
    have e : S.surjWords = Ls.toArray := hs
    rw [e, getElem!_pos _ k (by simp; omega), List.getD_eq_getElem _ _ hk']
    simp
  have hslL : ∀ k, k < 2 → ∀ z ∈ Ls.getD k [], z ≠ 0 ∧ z.natAbs ≤ S.m := by
    intro k hk z hz
    have hmem : Ls.getD k [] ∈ Ls := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have h1 := List.all_eq_true.1 hsl _ hmem
    have h2 := List.all_eq_true.1 h1 z hz
    simpa using h2
  unfold imageChecks
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hi]; simpa using hli
  · rw [hs]; simpa using hls
  · exact List.all_eq_true.2 fun r hr => List.all_eq_true.2 fun l hl => by
      simpa using (hrels r hr).1 l hl
  · rw [hi, List.all_toArray]
    refine List.all_eq_true.2 fun w hw => List.all_eq_true.2 fun z hz => ?_
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 hbase w hw) z hz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
    rw [hG4s]
    omega
  · rw [hs, List.all_toArray]; exact hsl
  · exact List.all_eq_true.2 fun k hk => (hIv k (List.mem_range.1 hk)).2
  · refine List.all_eq_true.2 fun r hr => ?_
    rw [beq_iff_eq]
    refine Rep.ext G (Rep.word G (imgF Ims ImsI) (imgLetter I (I.map (invT D.n))) _
      fun z hz => hlet z (hrelL r hr z hz).1 (hrelL r hr z hz).2) ?_
    rw [(hrels r hr).2]
    exact Rep.id G
  · rw [hsw 0 (by omega)]
    refine Rep.ext G (Rep.word G (imgF Ims ImsI) (imgLetter I (I.map (invT D.n))) _
      fun z hz => hlet z (hslL 0 (by omega) z hz).1 (hslL 0 (by omega) z hz).2) ?_
    rw [hsA']
    exact hα
  · rw [hsw 1 (by omega)]
    refine Rep.ext G (Rep.word G (imgF Ims ImsI) (imgLetter I (I.map (invT D.n))) _
      fun z hz => hlet z (hslL 1 (by omega) z hz).1 (hslL 1 (by omega) z hz).2) ?_
    rw [hsB']
    exact hβ

theorem seed_checks {D : VecData} {S : Spec} {csA csB : List Char} {A B AI BI : Nat}
    {Ims ImsI : List Nat} {Li Ls : List (List Int)} {PT PA LB AP BP SO SOI : Nat → Nat}
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (hA : m1Bind csA D.d A = true) (hB : m1Bind csB D.d B = true)
    (hAI : mulF D.d A AI = idF D.d) (hBI : mulF D.d B BI = idF D.d)
    (hn : 0 < D.n) (hn32 : D.n < 4294967295)
    (horb : ∀ k < D.n, orbStep D.d D.n A B D.v0 PT PA LB AP BP SO SOI k = true)
    (hm : S.m = Ims.length)
    (hi : S.imgWords = Li.toArray) (hs : S.surjWords = Ls.toArray) (hli : Li.length = S.m)
    (hls : Ls.length = 2)
    (hbase : Li.all (fun w => w.all fun z => decide (0 ≤ z) && decide (z < 4)) = true)
    (himg : ∀ k < S.m, matW D.d (baseF A AI B BI) (Li.getD k []) = lget Ims k)
    (hinv : ∀ k < S.m, mulF D.d (lget Ims k) (lget ImsI k) = idF D.d)
    (hrel : S.rels.all (fun r => r.all (fun l => decide (l.1 < S.m)) &&
      Nat.beq (matW D.d (imgF Ims ImsI) (r.map letterOf)) (idF D.d)) = true)
    (hsl : Ls.all (fun w => w.all fun z => z != 0 && decide (z.natAbs ≤ S.m)) = true)
    (hsA' : matW D.d (imgF Ims ImsI) (Ls.getD 0 []) = A)
    (hsB' : matW D.d (imgF Ims ImsI) (Ls.getD 1 []) = B) :
    seedLetterChecks D S = true := by
  have hf := fun k (hk : k < D.n) => orbStep_facts (horb k hk)
  have hcA : ∀ v, vecMulN D.d D.colsA v = mvK D.d A v := fun v => by
    have := vecMulN_cols hA v
    unfold VecData.colsA VecData.rowsA
    rw [hsA]
    exact this
  have hcB : ∀ v, vecMulN D.d D.colsB v = mvK D.d B v := fun v => by
    have := vecMulN_cols hB v
    unfold VecData.colsB VecData.rowsB
    rw [hsB]
    exact this
  have hmono : ∀ a b, a < b → b < D.n → PT (SO a) < PT (SO b) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => intro hb; exact (hf a (by omega)).2.2.2.2.2.2.2.2.2.2 hb
    | succ b hab ih =>
      intro hb
      exact lt_trans (ih (by omega)) ((hf b (by omega)).2.2.2.2.2.2.2.2.2.2 hb)
  have hPTinj : ∀ i < D.n, ∀ j < D.n, PT i = PT j → i = j := by
    intro i hi j hj e
    have hi' := (hf i hi).2.2.2.2.2.2.2.2.1
    have hj' := (hf j hj).2.2.2.2.2.2.2.2.1
    have hSi := (hf i hi).2.2.2.2.2.2.2.2.2.1
    have hSj := (hf j hj).2.2.2.2.2.2.2.2.2.1
    rcases lt_trichotomy (SOI i) (SOI j) with h | h | h
    · have := hmono _ _ h hj'
      rw [hSi, hSj] at this
      omega
    · rw [← hSi, ← hSj, h]
    · have := hmono _ _ h hi'
      rw [hSi, hSj] at this
      omega
  let R : Finset Nat := (Finset.range D.n).image PT
  have hR : R.card = D.n := by
    rw [Finset.card_image_of_injOn (fun i hi j hj e =>
      hPTinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e), Finset.card_range]
  have hmemR : ∀ k < D.n, PT k ∈ R := fun k hk => Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, rfl⟩
  have hRlt : ∀ y ∈ R, y < 2 ^ D.d := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    exact (hf k (Finset.mem_range.1 hk)).1
  have hv0 : D.v0 ∈ R := by
    have := hmemR 0 hn
    rwa [(hf 0 hn).2.1 rfl] at this
  have hAR : ∀ x ∈ R, vecMulN D.d D.colsA x ∈ R := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    have hk := Finset.mem_range.1 hk
    rw [hcA, ← (hf k hk).2.2.2.2.1]
    exact hmemR _ (hf k hk).2.2.2.1
  have hBR : ∀ x ∈ R, vecMulN D.d D.colsB x ∈ R := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    have hk := Finset.mem_range.1 hk
    rw [hcB, ← (hf k hk).2.2.2.2.2.2.1]
    exact hmemR _ (hf k hk).2.2.2.2.2.1
  have hmin : ∀ S : Set Nat, D.v0 ∈ S →
      (∀ x ∈ S, vecMulN D.d D.colsA x ∈ S ∧ vecMulN D.d D.colsB x ∈ S) → ∀ x ∈ R, x ∈ S := by
    intro T h0 hcl x hx
    obtain ⟨k0, hk0, rfl⟩ := Finset.mem_image.1 hx
    have key : ∀ k, k < D.n → PT k ∈ T := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        by_cases hk0 : k = 0
        · subst hk0
          rw [(hf 0 hk).2.1 rfl]
          exact h0
        · obtain ⟨h1, h2, h3⟩ := (hf k hk).2.2.1 hk0
          have := ih _ h1 (by omega)
          rw [h3]
          have hc := hcl _ this
          by_cases hl : LB k = 0
          · rw [if_pos hl, ← hcA]; exact hc.1
          · rw [if_neg hl, ← hcB]; exact hc.2
    exact key k0 (Finset.mem_range.1 hk0)
  obtain ⟨hsz, hasz, hbsz, h0, hmem, hinj, hao, hbo⟩ :=
    CFSG.KC.SurjSeed.vOrbitBFS_full (d := D.d) (cA := D.colsA) (cB := D.colsB) hR hn32 hRlt hv0
      hAR hBR hmin
  have G : Good D.d D.n (D.orbit ()).pts := ⟨hn32, fun i hi => hRlt _ (hmem i hi), hinj⟩
  have hαR : Rep D.d D.n (D.orbit ()).pts A (D.orbit ()).alpha :=
    ⟨hasz, fun i hi => ⟨(hao i hi).1, (hao i hi).2.trans (hcA _)⟩⟩
  have hβR : Rep D.d D.n (D.orbit ()).pts B (D.orbit ()).beta :=
    ⟨hbsz, fun i hi => ⟨(hbo i hi).1, (hbo i hi).2.trans (hcB _)⟩⟩
  exact checks_of G hαR hβR hAI hBI hm hi hs hli hls hbase himg hinv hrel hsl hsA' hsB'

end CFSG.KC.SurjSeed

end
