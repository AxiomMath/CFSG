module

public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.RouteP.Objects
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.RouteP

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

@[expose] def lowBit (k : Nat) : Nat := ((List.range 11).find? fun j => k >>> j &&& 1 == 1).getD 0

theorem lowBit_lt (k : Nat) : lowBit k < 11 := by
  unfold lowBit
  cases h : (List.range 11).find? fun j => k >>> j &&& 1 == 1 with
  | none => decide
  | some j => exact List.mem_range.1 (List.mem_of_find?_eq_some h)

theorem sub_lowBit_lt {k : Nat} (hk : 0 < k) : k - 1 <<< lowBit k < k := by
  have : 0 < 1 <<< lowBit k := by rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos _
  omega

@[expose] def epsPt (tabs : Array Table) (p : Nat) : Nat → Nat
  | 0 => p
  | k + 1 => ap tabs[epsReg (lowBit (k + 1))]! (epsPt tabs p (k + 1 - 1 <<< lowBit (k + 1)))
termination_by k => k
decreasing_by exact sub_lowBit_lt (Nat.succ_pos k)

theorem epsPt_zero (tabs : Array Table) (p : Nat) : epsPt tabs p 0 = p := by
  rw [epsPt]

theorem epsPt_pos (tabs : Array Table) (p : Nat) {k : Nat} (hk : 0 < k) :
    epsPt tabs p k = ap tabs[epsReg (lowBit k)]! (epsPt tabs p (k - 1 <<< lowBit k)) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [epsPt]

@[expose] def epsPar (k : Nat) : Nat := if k = 0 then 0 else k - 1 <<< lowBit k

@[expose] def epsLab (k : Nat) : Nat := if k = 0 then 0 else lowBit k

theorem getElem!_map_range {α : Type} [Inhabited α] (f : Nat → α) {m k : Nat} (hk : k < m) :
    ((List.range m).map f).toArray[k]! = f k := by
  rw [getElem!_pos _ k (by simpa using hk)]
  simp

private theorem epsTree_loop (tabs : Array Table) (p q : Nat) :
    ∀ s,
      (List.range' 1 s).foldl
          (fun b a =>
            (b.fst.push
                (ap tabs[epsReg ((List.find? (fun j => a >>> j &&& 1 == 1) (List.range 11)).getD 0)]!
                  b.fst[a - 1 <<< (List.find? (fun j => a >>> j &&& 1 == 1) (List.range 11)).getD 0]!),
              b.snd.fst.push
                (ap tabs[epsReg ((List.find? (fun j => a >>> j &&& 1 == 1) (List.range 11)).getD 0)]!
                  b.snd.fst[a - 1 <<< (List.find? (fun j => a >>> j &&& 1 == 1) (List.range 11)).getD 0]!),
              b.snd.snd.fst.push (a - 1 <<< (List.find? (fun j => a >>> j &&& 1 == 1) (List.range 11)).getD 0),
              b.snd.snd.snd.push ((List.find? (fun j => a >>> j &&& 1 == 1) (List.range 11)).getD 0)))
          ((#[p], #[q], #[0], #[0]) : Array Nat × Array Nat × Array Nat × Array Nat) =
        (((List.range (s + 1)).map (epsPt tabs p)).toArray,
          ((List.range (s + 1)).map (epsPt tabs q)).toArray,
          ((List.range (s + 1)).map epsPar).toArray, ((List.range (s + 1)).map epsLab).toArray) := by
  intro s
  induction s with
  | zero => simp [epsPt_zero, epsPar, epsLab]
  | succ s ih =>
    rw [List.range'_concat, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    have e1 : 1 + 1 * s = s + 1 := by omega
    rw [e1]
    change ((_, _, _, _) : Array Nat × Array Nat × Array Nat × Array Nat) = _
    have hlt : s + 1 - 1 <<< lowBit (s + 1) < s + 1 := sub_lowBit_lt (Nat.succ_pos s)
    rw [List.range_succ (n := s + 1), List.map_append, List.map_append, List.map_append,
      List.map_append]
    simp only [List.map_cons, List.map_nil, ← List.push_toArray]
    change (_, _, _, _) = ((_ : Array Nat).push (epsPt tabs p (s + 1)), _, _, _)
    have g1 := getElem!_map_range (epsPt tabs p) (m := s + 1) hlt
    have g2 := getElem!_map_range (epsPt tabs q) (m := s + 1) hlt
    unfold lowBit at g1 g2 hlt
    rw [g1, g2, epsPt_pos tabs p (Nat.succ_pos s), epsPt_pos tabs q (Nat.succ_pos s)]
    simp only [epsPar, epsLab, Nat.succ_ne_zero, if_false, lowBit]

theorem epsTreeData_eq (tabs : Array Table) (p q : Nat) :
    epsTreeData tabs p q =
      ⟨((List.range 2048).map (epsPt tabs p)).toArray, ((List.range 2048).map (epsPt tabs q)).toArray,
        ((List.range 2048).map epsPar).toArray, ((List.range 2048).map epsLab).toArray⟩ := by
  unfold epsTreeData
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, pure_bind, bind_pure, Prod.eta]
  rw [epsTree_loop tabs p q (2048 - 1)]
  rfl

theorem epsPt_lt (tabs : Array Table)
    (hlt : ∀ j < 11, ∀ x < degree, ap tabs[epsReg j]! x < degree) {p : Nat} (hp : p < degree) :
    ∀ k, epsPt tabs p k < degree := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : 0 < k
    · rw [epsPt_pos tabs p hk]
      exact hlt _ (lowBit_lt k) _ (ih _ (sub_lowBit_lt hk))
    · rw [show k = 0 by omega, epsPt_zero]
      exact hp

theorem epsTreeOK_of (tabs : Array Table)
    (hlt : ∀ j < 11, ∀ x < degree, ap tabs[epsReg j]! x < degree)
    (hd : ∀ i < 2048, ∀ j < i, epsPt tabs 3 i ≠ epsPt tabs 3 j ∨ epsPt tabs 6 i ≠ epsPt tabs 6 j) :
    epsTreeOK tabs = true := by
  unfold epsTreeOK pairTreeOK
  rw [epsTreeData_eq]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allIn_eq_true, List.size_toArray,
    List.length_map, List.length_range, Bool.or_eq_true, bne_iff_ne, ne_eq, and_assoc]
  refine ⟨trivial, trivial, trivial, trivial, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · rw [getElem!_map_range _ (by decide : 0 < 2048), epsPt_zero]
  · rw [getElem!_map_range _ (by decide : 0 < 2048), epsPt_zero]
  · intro k _ hk
    rw [getElem!_map_range _ hk, getElem!_map_range _ hk]
    exact ⟨epsPt_lt tabs hlt (by decide) k, epsPt_lt tabs hlt (by decide) k⟩
  · intro k hk1 hk
    have hk0 : k ≠ 0 := by omega
    have hpar : k - 1 <<< lowBit k < k := sub_lowBit_lt (by omega)
    rw [getElem!_map_range _ hk, getElem!_map_range _ hk, getElem!_map_range _ hk,
      getElem!_map_range _ hk]
    simp only [epsPar, epsLab, hk0, if_false]
    rw [getElem!_map_range _ (by omega : k - 1 <<< lowBit k < 2048),
      getElem!_map_range _ (by omega : k - 1 <<< lowBit k < 2048),
      ← epsPt_pos tabs 3 (by omega), ← epsPt_pos tabs 6 (by omega)]
    exact ⟨hpar, lowBit_lt k, rfl, rfl⟩
  · intro i _ hi j _ hj
    rw [getElem!_map_range _ hi, getElem!_map_range _ hi, getElem!_map_range _ (by omega),
      getElem!_map_range _ (by omega)]
    exact hd i hi j hj

variable {G : Type*} [Group G]

@[expose] def epsProd (e : Nat → G) : Nat → G
  | 0 => 1
  | k + 1 => e (lowBit (k + 1)) * epsProd e (k + 1 - 1 <<< lowBit (k + 1))
termination_by k => k
decreasing_by exact sub_lowBit_lt (Nat.succ_pos k)

theorem epsProd_zero (e : Nat → G) : epsProd e 0 = 1 := by rw [epsProd]

theorem epsProd_pos (e : Nat → G) {k : Nat} (hk : 0 < k) :
    epsProd e k = e (lowBit k) * epsProd e (k - 1 <<< lowBit k) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [epsProd]

theorem epsPt_eq_idx [MulAction G (Fin degree)] {tabs : Array Table} {e : Nat → G}
    (he : ∀ j < 11, Rep degree tabs[epsReg j]! (e j)) {p : Nat} (hp : p < degree) (k : Nat) :
    epsPt tabs p k = idx degree (epsProd e k) p := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : 0 < k
    · rw [epsPt_pos tabs p hk, epsProd_pos e hk, idx_mul, ← ih _ (sub_lowBit_lt hk)]
      have hlt : epsPt tabs p (k - 1 <<< lowBit k) < degree := by
        rw [ih _ (sub_lowBit_lt hk)]
        exact idx_lt _ hp
      exact he _ (lowBit_lt k) _ hlt
    · rw [show k = 0 by omega, epsPt_zero, epsProd_zero, idx_one]

end CFSG.KS.RouteP

end
