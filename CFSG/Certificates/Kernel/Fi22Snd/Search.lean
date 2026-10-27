module

public import CFSG.Certificates.Kernel.Fi22Snd.Colour
public import CFSG.Certificates.Kernel.Fi22Snd.Node

public section

namespace CFSG.KC.Fi22Snd

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KC.S2071 CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore.Native

private theorem parLt_of_all {m chunks : Nat} {p : Nat → Bool} (h : ∀ i < m, p i = true) :
    parLt m chunks p = true := by
  unfold parLt
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply]
  intro c _
  change allLt (m / chunks + 1) (fun k => !(decide (c * (m / chunks + 1) + k < m)) ||
    p (c * (m / chunks + 1) + k)) = true
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro k _
  by_cases hk : c * (m / chunks + 1) + k < m
  · simp [hk, h _ hk]
  · simp [hk]

private theorem lenL_len (l : List Nat) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change Nat.add (lenL l) 1 = _
    rw [ih]
    rfl

private theorem getL_getD : ∀ (l : List Nat) (i : Nat), getL l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | a :: l, i + 1 => by
    change Bool.rec (motive := fun _ => Nat) (getL l (Nat.sub (i + 1) 1)) a
      (Nat.beq (i + 1) 0) = _
    rw [show Nat.beq (i + 1) 0 = false from rfl, show Nat.sub (i + 1) 1 = i from rfl,
      getL_getD l i]
    rfl

private theorem srcs_get {n K e : Nat} {nbr : Array (List Nat)} {t : Array Nat}
    {base : List Nat} (he : e < base.length + 1) :
    (((List.range (base.length + 1)).map fun d => colourT n nbr t (base.take d) K).toArray)[e]! =
      colourT n nbr t (base.take e) K := by
  rw [getElem!_pos _ _ (by simpa using he)]
  simp

theorem search_sound' {n d np na k chunks T P : Nat} {nbr : Array (List Nat)} {t : Array Nat}
    {base SC : List Nat} {pool acc : Array (Array Nat)} {nodes : Array SNode}
    {R M S PL AC DT : Nat → Nat} (hn : n < 4096) (hnbr : nbr = rowsArr n d R)
    (hrow : ∀ x < n, rowOK n d R M S x = true) (hsym : ∀ x < n, ∀ y ∈ nbr[x]!, x ∈ nbr[y]!)
    (ht : t = unpack n 12 T) (hbase : base.length < 65536)
    (hpre : ∀ i < nodes.size, (nodes[i]!).pre.length < 65536)
    (hpreN : ∀ i < nodes.size, ∀ x ∈ (nodes[i]!).pre, x < n)
    (hpool : pool.size = np) (hPL : ∀ j < np, pool[j]! = unpack n 12 (PL j))
    (hacc : acc.size = na) (hAC : ∀ i < na, acc[i]! = unpack n 12 (AC i))
    (hinj : injK n S T base k P = true)
    (hsc : ∀ e < base.length, srcColK n S T base k e (SC.getD e 0) = true)
    (h0 : 0 < nodes.size) (hroot : (nodes[0]!).pre = [])
    (hnode : ∀ i < nodes.size, nodeK n S T PL np AC na nodes base SC k DT i = true) :
    searchOK n nbr t base pool nodes acc k chunks = true := by
  have hcol : ∀ pre : List Nat, pre.length < 65536 → ∀ u,
      cget (colourK n S T pre k) u = (colourT n nbr t pre k)[u]! :=
    fun pre hp => cget_colourK hn hnbr hrow hsym ht hp
  unfold searchOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨h0, hroot⟩, ?_⟩, parLt_of_all fun i hi => ?_⟩
  · rw [srcs_get (by omega), List.take_length]
    exact colInj_of_injK hn hnbr hrow hsym ht hbase hinj
  · have hN := hnode i hi
    unfold nodeK at hN
    rw [CFSG.KS.Raw.Orb.bIf_eq] at hN
    simp only [lenL_len, Nat.blt_eq] at hN
    by_cases hlt : (nodes[i]!).pre.length < base.length
    · rw [if_pos hlt] at hN
      rw [if_pos hlt]
      have hsc' := hsc _ hlt
      unfold srcColK at hsc'
      have hlen : (base.take (nodes[i]!).pre.length).length < 65536 := by
        rw [List.length_take]
        omega
      rw [srcs_get (by omega), ← hcol _ hlen, Nat.eq_of_beq_eq_true hsc', ← getL_getD]
      exact branchOK_of_branchK hpool hPL (hpreN i hi) (fun w _ => hcol _ (hpre i hi) w) hN
    · rw [if_neg hlt] at hN
      rw [if_neg hlt, srcs_get (by omega), List.take_length]
      exact leafOK_of_leafK hacc hAC (fun w _ => hcol _ (hpre i hi) w)
        (fun w _ => hcol base hbase w) (inj_of_injK hn hnbr hrow hsym ht hbase hinj) hN

end CFSG.KC.Fi22Snd

end
