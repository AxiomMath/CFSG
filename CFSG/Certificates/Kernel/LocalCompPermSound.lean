module

public import Certificates.Data.CFSGNative.PSL3Four.Basic
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.Kernel.LocalComp.ThreeW
import CFSG.Certificates.Kernel.MonsterB.Co2PermSound

public section

namespace CFSG.KC.LocalComp.Perm

open CFSG.PSL3Four.Native

@[expose] def permK (n : Nat) (t : Array Nat) : Bool :=
  t.size == n && (t.toList.foldl (fun (st : Bool × Nat) a =>
    (st.1 && decide (a < n) && (st.2 >>> a) % 2 == 0, st.2 ||| (1 <<< a))) (true, 0)).1

@[expose] def invTabK (n : Nat) (t s : Array Nat) : Bool :=
  t.size == n && s.size == n &&
    CFSG.KC.LocalComp.ThreeW.allFrom 0 (fun i => decide (t[i]! < n) && s[t[i]!]! == i) n

private theorem permFold_spec (n : Nat) : ∀ (l : List Nat) (b : Bool) (m : Nat),
    (l.foldl (fun (st : Bool × Nat) a =>
      (st.1 && decide (a < n) && (st.2 >>> a) % 2 == 0, st.2 ||| (1 <<< a))) (b, m)).1 = true →
    b = true ∧ l.Nodup ∧ ∀ x ∈ l, x < n ∧ m.testBit x = false
  | [], b, m, h => ⟨h, List.nodup_nil, fun x hx => absurd hx List.not_mem_nil⟩
  | a :: l, b, m, h => by
    obtain ⟨hb, hnd, hl⟩ := permFold_spec n l _ _ h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
    obtain ⟨⟨hb0, han⟩, hbit⟩ := hb
    have hma : m.testBit a = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rw [Nat.shiftRight_eq_div_pow] at hbit
      simp [hbit]
    have key : ∀ x ∈ l, x < n ∧ m.testBit x = false ∧ x ≠ a := by
      intro x hx
      obtain ⟨hxn, hxb⟩ := hl x hx
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_false_iff] at hxb
      refine ⟨hxn, hxb.1, fun hxa => ?_⟩
      subst hxa
      simp at hxb
    refine ⟨hb0, List.nodup_cons.2 ⟨fun hm => (key a hm).2.2 rfl, hnd⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact ⟨han, hma⟩
    · exact ⟨(key x hx').1, (key x hx').2.1⟩

private theorem allFrom_spec {p : Nat → Bool} {lo : Nat} :
    ∀ {m : Nat}, CFSG.KC.LocalComp.ThreeW.allFrom lo p m = true → ∀ k < m, p (lo + k) = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | m + 1, h, k, hk => by
    have h' : (CFSG.KC.LocalComp.ThreeW.allFrom lo p m && p (lo + m)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact allFrom_spec h'.1 k hk
    · exact h'.2

private theorem invTab_eq_of_K {n : Nat} {t s : Array Nat} (h : invTabK n t s = true) :
    invTab n t = s := by
  unfold invTabK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨ht, hs⟩, hall⟩ := h
  have hp : ∀ i < n, t[i]! < n ∧ s[t[i]!]! = i := by
    intro i hi
    have := allFrom_spec hall i hi
    rw [Nat.zero_add] at this
    simpa using this
  have hb : ∀ i < n, t[i]! < n := fun i hi => (hp i hi).1
  have hinj : ∀ i j, i < n → j < n → t[i]! = t[j]! → i = j := fun i j hi hj e => by
    rw [← (hp i hi).2, ← (hp j hj).2, e]
  have hsurj : ∀ q < n, ∃ i < n, t[i]! = q := by
    let f : Fin n → Fin n := fun i => ⟨t[i.1]!, hb i.1 i.2⟩
    have hf : Function.Injective f := fun a b e =>
      Fin.ext (hinj a.1 b.1 a.2 b.2 (congrArg Fin.val e))
    intro q hq
    obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 hf) ⟨q, hq⟩
    exact ⟨i.1, i.2, congrArg Fin.val hi⟩
  have hspec := CFSG.KC.Co2Mem.invCand_spec hb hinj
  have e : invTab n t = CFSG.Monster.B.Co2.Native.invCand n t := rfl
  have hsize : (CFSG.Monster.B.Co2.Native.invCand n t).size = n := by
    have e2 : CFSG.Monster.B.Co2.Native.invCand n t =
        (List.range' 0 n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
      simp [CFSG.Monster.B.Co2.Native.invCand, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
        List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size]
      rfl
    rw [e2]
    exact (CFSG.KC.Co2Mem.foldl_set_spec (g := fun i => t[i]!) hb hinj n le_rfl).1
  rw [e]
  apply Array.ext
  · rw [hsize, hs]
  · intro q h1 h2
    rw [hsize] at h1
    obtain ⟨i, hi, hiq⟩ := hsurj q h1
    rw [← getElem!_pos (CFSG.Monster.B.Co2.Native.invCand n t) q (by omega),
      ← getElem!_pos s q (by omega), ← hiq, hspec i hi, (hp i hi).2]

theorem isInvA_invCand_of_K {n : Nat} {t : Array Nat} (h : permK n t = true) :
    CFSG.Monster.B.Co2.Native.isInvA n t (CFSG.Monster.B.Co2.Native.invCand n t) = true := by
  unfold permK at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hsz, hf⟩ := h
  obtain ⟨-, hnd, hlt⟩ := permFold_spec n t.toList true 0 hf
  have hmem : ∀ i < n, t[i]! ∈ t.toList := fun i hi => by
    rw [getElem!_pos t i (by omega)]
    exact Array.getElem_mem_toList _
  have hb : ∀ i < n, t[i]! < n := fun i hi => (hlt _ (hmem i hi)).1
  have hi : ∀ i j, i < n → j < n → t[i]! = t[j]! → i = j := fun i j hi hj e => by
    have hi' : i < t.toList.length := by simp; omega
    have hj' : j < t.toList.length := by simp; omega
    rw [getElem!_pos t i (by omega), getElem!_pos t j (by omega)] at e
    exact (hnd.getElem_inj_iff (hi := hi') (hj := hj')).1 (by simpa using e)
  exact CFSG.KC.Co2Mem.isInvA_invCand hb hi

theorem map_invTab_of_K {n : Nat} {T S : Array Tab}
    (h : (T.size == S.size && (T.toList.zip S.toList).all fun p => invTabK n p.1 p.2) = true) :
    T.map (invTab n) = S := by
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hsz, hall⟩ := h
  apply Array.ext
  · simp [hsz]
  · intro i h1 h2
    rw [Array.size_map] at h1
    rw [Array.getElem_map]
    exact invTab_eq_of_K (hall (T[i], S[i]) (by
      rw [List.mem_iff_getElem]
      refine ⟨i, by simp [hsz, h1, h2], ?_⟩
      simp))

end CFSG.KC.LocalComp.Perm

end
