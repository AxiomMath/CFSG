module

public import Certificates.Data.Kernel.GMS78RuSClo
import CFSG.Certificates.Kernel.GMS78RuP.Basic
import CFSG.Certificates.Kernel.GMS78RuS17.Basic
import CFSG.Certificates.Kernel.GMS78RuS17.Idx
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.GMS.S17

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

private theorem brec_eq (b : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t b = if b then t else e := by cases b <;> rfl

private noncomputable def zInner (m : Nat → Nat → Nat) (IDX : Nat) (C0 : List Nat) (p : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun q _ ih2 => List.cons (Nat.sub (fget IDX (m p q) 9) 1) ih2) C0

private theorem zInner_eq (m : Nat → Nat → Nat) (IDX p : Nat) :
    ∀ C0 : List Nat, zInner m IDX C0 p = C0.map fun q => Nat.sub (fget IDX (m p q) 9) 1
  | [] => rfl
  | q :: C0 => by
    have : zInner m IDX (q :: C0) p =
        Nat.sub (fget IDX (m p q) 9) 1 :: zInner m IDX C0 p := rfl
    rw [this, zInner_eq m IDX p C0, List.map_cons]

private noncomputable def zRows (m : Nat → Nat → Nat) (IDX : Nat) (C0 : List Nat) : List Nat → List Nat :=
  fun L => List.rec (motive := fun _ => List Nat) []
    (fun p _ ih => List.cons (czPack8 (zInner m IDX C0 p)) ih) L

private theorem zRows_eq (m : Nat → Nat → Nat) (IDX : Nat) (C0 : List Nat) :
    ∀ L : List Nat, zRows m IDX C0 L =
      L.map fun p => czPack8 (C0.map fun q => Nat.sub (fget IDX (m p q) 9) 1)
  | [] => rfl
  | p :: L => by
    have : zRows m IDX C0 (p :: L) = czPack8 (zInner m IDX C0 p) :: zRows m IDX C0 L := rfl
    rw [this, zRows_eq m IDX C0 L, List.map_cons, zInner_eq]

private noncomputable def zG (rows : List Nat) (t i : Nat) : Bool :=
  allN 256 fun j => orB (Nat.beq (fget (neGet 0 rows i) j 8) (fget (neGet 0 rows j) i 8))
    (Nat.beq (fget (neGet 0 rows i) j 8) (fget (neGet 0 rows t) (fget (neGet 0 rows j) i 8) 8))

private noncomputable def zStep (rows : List Nat) (iu i2 i a : Nat) : Nat :=
  Nat.add a (Nat.add (Bool.rec (motive := fun _ => Nat) 0 1 (zG rows iu i))
    (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (zG rows i2 i)) 9))

private noncomputable def zLoop (rows : List Nat) (iu i2 : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => strictN acc (zStep rows iu i2 i)) n

private noncomputable def zN (m : Nat → Nat → Nat) (C : List Nat) (u n : Nat) : Nat :=
  (fun IDX => (fun rows => (fun iu i2 =>
      Nat.rec (motive := fun _ => Nat) 0 (fun i acc => strictN acc fun a =>
        (fun Ri => (fun f1 f2 => Nat.add a (Nat.add (Bool.rec (motive := fun _ => Nat) 0 1 f1)
            (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 f2) 9)))
          (allN (nat_lit 256) fun j => (fun pq qp => orB (Nat.beq pq qp)
              (Nat.beq pq (fget (neGet 0 rows iu) qp 8))) (fget Ri j 8) (fget (neGet 0 rows j) i 8))
          (allN (nat_lit 256) fun j => (fun pq qp => orB (Nat.beq pq qp)
              (Nat.beq pq (fget (neGet 0 rows i2) qp 8))) (fget Ri j 8) (fget (neGet 0 rows j) i 8)))
        (neGet 0 rows i)) n)
      (Nat.sub (fget IDX u 9) 1) (Nat.sub (fget IDX 256 9) 1))
    (List.rec (motive := fun _ => List Nat) []
      (fun p _ ih => List.cons (czPack8 (List.rec (motive := fun _ => List Nat) []
        (fun q _ ih2 => List.cons (Nat.sub (fget IDX (m p q) 9) 1) ih2) C)) ih) C))
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.lor (Nat.shiftLeft (Nat.succ i) (Nat.mul 9 x)) (ih (Nat.succ i))) C 0)



private noncomputable def idxf (C : List Nat) (x : Nat) : Nat := Nat.sub (fget (sIdx C) x 9) 1

private noncomputable def rowsOf (m : Nat → Nat → Nat) (C : List Nat) : List Nat :=
  zRows m (sIdx C) C C

private theorem zN_eq (m : Nat → Nat → Nat) (C : List Nat) (u n : Nat) :
    zN m C u n = zLoop (rowsOf m C) (idxf C u) (idxf C 256) n := rfl

private theorem sZx_eq_zN (m : Nat → Nat → Nat) (C : List Nat) (u : Nat) :
    sZx m C u = zN m C u (nat_lit 256) := by
  delta sZx zN
  rfl

private theorem zLoop_eq (rows : List Nat) (iu i2 : Nat) : ∀ n,
    zLoop rows iu i2 n = (List.range n).countP (zG rows iu) +
      (List.range n).countP (zG rows i2) * 512
  | 0 => by simp [zLoop]
  | n + 1 => by
    have e : zLoop rows iu i2 (n + 1) = strictN (zLoop rows iu i2 n) (zStep rows iu i2 n) := rfl
    rw [e, P117.strictN_eq, zLoop_eq rows iu i2 n]
    simp only [zStep, brec_eq, Nat.shiftLeft_eq, Nat.add_eq, List.range_succ, List.countP_append,
      List.countP_cons, List.countP_nil]
    cases h1 : zG rows iu n <;> cases h2 : zG rows i2 n <;> simp <;> omega

section Sem

variable {m : Nat → Nat → Nat} {C : List Nat}

private theorem idxf_eq (hnd : C.Nodup) (hlen : C.length = 256) {x : Nat} (hx : x ∈ C) :
    idxf C x = C.idxOf x := by
  unfold idxf
  rw [sIdx_fget hnd (by omega), if_pos hx]
  rfl

private theorem idxf_lt (hnd : C.Nodup) (hlen : C.length = 256) {x : Nat} (hx : x ∈ C) :
    idxf C x < 256 := by
  rw [idxf_eq hnd hlen hx]
  have := List.idxOf_lt_length_of_mem hx
  omega

private theorem e_mem (hlen : C.length = 256) {i : Nat} (hi : i < 256) : C.getD i 0 ∈ C := by
  rw [getD_eq' _ _ (by omega)]
  exact List.getElem_mem _

private theorem e_idxf (hnd : C.Nodup) (hlen : C.length = 256) {x : Nat} (hx : x ∈ C) :
    C.getD (idxf C x) 0 = x := by
  have := List.idxOf_lt_length_of_mem hx
  rw [idxf_eq hnd hlen hx, getD_eq' _ _ (by omega)]
  exact List.getElem_idxOf _

private theorem idxf_inj (hnd : C.Nodup) (hlen : C.length = 256) {x y : Nat} (hx : x ∈ C)
    (hy : y ∈ C) : idxf C x = idxf C y ↔ x = y := by
  rw [idxf_eq hnd hlen hx, idxf_eq hnd hlen hy]
  exact List.idxOf_inj hx

private theorem rowsOf_get (hlen : C.length = 256) {i : Nat} (hi : i < 256) :
    neGet 0 (rowsOf m C) i = czPack8 (C.map fun q => idxf C (m (C.getD i 0) q)) := by
  have h : i < C.length := by omega
  unfold rowsOf
  rw [neGet_eq, zRows_eq, getD_eq' _ _ (by simpa using h), List.getElem_map,
    getD_eq' _ 0 h]
  rfl

private theorem field (hnd : C.Nodup) (hlen : C.length = 256)
    (hcl : ∀ p ∈ C, ∀ q ∈ C, m p q ∈ C) {i j : Nat} (hi : i < 256) (hj : j < 256) :
    fget (neGet 0 (rowsOf m C) i) j 8 = idxf C (m (C.getD i 0) (C.getD j 0)) := by
  rw [rowsOf_get hlen hi, czPack8_fget]
  · rw [getD_eq' _ _ (n := j) (by simp; omega), List.getElem_map,
      ← getD_eq' C 0 (n := j) (by omega)]
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    exact idxf_lt hnd hlen (hcl _ (e_mem hlen hi) q hq)

private theorem cond_eq (hnd : C.Nodup) (hlen : C.length = 256)
    (hcl : ∀ p ∈ C, ∀ q ∈ C, m p q ∈ C) {t : Nat} (ht : t ∈ C) {i j : Nat} (hi : i < 256)
    (hj : j < 256) :
    orB (Nat.beq (fget (neGet 0 (rowsOf m C) i) j 8) (fget (neGet 0 (rowsOf m C) j) i 8))
      (Nat.beq (fget (neGet 0 (rowsOf m C) i) j 8)
        (fget (neGet 0 (rowsOf m C) (idxf C t)) (fget (neGet 0 (rowsOf m C) j) i 8) 8)) = true ↔
      (m (C.getD i 0) (C.getD j 0) = m (C.getD j 0) (C.getD i 0) ∨
        m (C.getD i 0) (C.getD j 0) = m t (m (C.getD j 0) (C.getD i 0))) := by
  have hei := e_mem hlen hi
  have hej := e_mem hlen hj
  have hij := hcl _ hei _ hej
  have hji := hcl _ hej _ hei
  have htji := hcl _ ht _ hji
  rw [field hnd hlen hcl hi hj, field hnd hlen hcl hj hi,
    field hnd hlen hcl (idxf_lt hnd hlen ht) (idxf_lt hnd hlen hji), e_idxf hnd hlen ht,
    e_idxf hnd hlen hji, P117.orB_eq, Bool.or_eq_true, P117.beq_eq, P117.beq_eq, beq_iff_eq,
    beq_iff_eq, idxf_inj hnd hlen hij hji, idxf_inj hnd hlen hij htji]

private theorem zG_iff (hnd : C.Nodup) (hlen : C.length = 256)
    (hcl : ∀ p ∈ C, ∀ q ∈ C, m p q ∈ C) {t : Nat} (ht : t ∈ C) {i : Nat} (hi : i < 256) :
    zG (rowsOf m C) (idxf C t) i = true ↔
      ∀ q ∈ C, m (C.getD i 0) q = m q (C.getD i 0) ∨
        m (C.getD i 0) q = m t (m q (C.getD i 0)) := by
  unfold zG
  rw [allN_iff]
  constructor
  · intro h q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
    have hj' : j < 256 := by omega
    have := (cond_eq hnd hlen hcl ht hi hj').1 (h j hj')
    rwa [getD_eq' _ 0 hj] at this
  · intro h j hj
    refine (cond_eq hnd hlen hcl ht hi hj).2 (h _ (e_mem hlen hj))

private theorem countP_getD (P : Nat → Bool) : ∀ l : List Nat,
    l.countP P = (List.range l.length).countP fun i => P (l.getD i 0)
  | [] => rfl
  | a :: l => by
    have ih := countP_getD P l
    simp only [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
      Function.comp, List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]
    rfl

private theorem zG_count (hnd : C.Nodup) (hlen : C.length = 256)
    (hcl : ∀ p ∈ C, ∀ q ∈ C, m p q ∈ C) {t : Nat} (ht : t ∈ C) :
    (List.range 256).countP (zG (rowsOf m C) (idxf C t)) =
      C.countP fun p => C.all fun q => m p q == m q p || m p q == m t (m q p) := by
  rw [countP_getD (fun p => C.all fun q => m p q == m q p || m p q == m t (m q p)) C, hlen]
  refine List.countP_congr fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [zG_iff hnd hlen hcl ht hi', List.all_eq_true]
  simp only [Bool.or_eq_true, beq_iff_eq]

theorem sZx_val (hnd : C.Nodup) (hlen : C.length = 256) (hcl : ∀ p ∈ C, ∀ q ∈ C, m p q ∈ C)
    {u : Nat} (hu : u ∈ C) (h256 : 256 ∈ C) :
    sZx m C u =
      (C.countP fun p => C.all fun q => m p q == m q p || m p q == m u (m q p)) +
      (C.countP fun p => C.all fun q => m p q == m q p || m p q == m 256 (m q p)) * 512 := by
  rw [sZx_eq_zN, zN_eq, zLoop_eq, zG_count hnd hlen hcl hu, zG_count hnd hlen hcl h256]

theorem kZ_read (hnd : C.Nodup) (hlen : C.length = 256) (hcl : ∀ p ∈ C, ∀ q ∈ C, m p q ∈ C)
    {u : Nat} (hu : u ∈ C) (h256 : 256 ∈ C) {k : Nat} (hk : sZx m C u = Nat.shiftRight k 42) :
    kZ1 k = (C.countP fun p => C.all fun q => m p q == m q p || m p q == m u (m q p)) ∧
      kZ2 k = (C.countP fun p => C.all fun q => m p q == m q p || m p q == m 256 (m q p)) := by
  rw [sZx_val hnd hlen hcl hu h256] at hk
  have h1 := (List.countP_le_length (p := fun p => C.all fun q =>
    m p q == m q p || m p q == m u (m q p)) (l := C))
  have h2 := (List.countP_le_length (p := fun p => C.all fun q =>
    m p q == m q p || m p q == m 256 (m q p)) (l := C))
  generalize (C.countP fun p => C.all fun q => m p q == m q p || m p q == m u (m q p)) = z1 at *
  generalize (C.countP fun p => C.all fun q => m p q == m q p || m p q == m 256 (m q p)) = z2 at *
  unfold kZ1 kZ2
  rw [← hk, fget_eq', fget_eq']
  rw [hlen] at h1 h2
  constructor <;> simp <;> omega

end Sem

end CFSG.KC.GMS.S17

end
