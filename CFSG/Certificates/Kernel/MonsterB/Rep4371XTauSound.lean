module

public import Certificates.Data.Kernel.MonsterB.Rep4371XTau
public import CFSG.Certificates.Kernel.MonsterB.Rep4371XNf

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Rep4371Row CFSG.KC.BM.Pkt

theorem revT_eq : ∀ (L M : Terms), revT L M = L.reverse ++ M
  | [], _ => rfl
  | e :: L, M => by
    change revT L (e :: M) = _
    rw [revT_eq L, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem eqI_true {m m' : Int} (h : eqI m m' = true) : m = m' := by
  have h0 : Int.sub m m' = 0 := isZI_true h
  change m - m' = 0 at h0
  omega

theorem eqTL_true : ∀ {L M : Terms}, eqTL L M = true → L = M
  | [], M, h => (nilB_eq h).symm
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | e :: L, e' :: M, h => by
    change bAnd(Nat.beq e.1 e'.1, bAnd(eqI e.2 e'.2, eqTL L M)) = true at h
    obtain ⟨h1, h⟩ := bAnd_true h
    obtain ⟨h2, h3⟩ := bAnd_true h
    rw [eqTL_true h3, Prod.ext (Nat.eq_of_beq_eq_true h1) (eqI_true h2)]

theorem tauStep_eq (st : Nat × Terms × Bool) (v : Nat) :
    tauStep st v = Bool.rec (motive := fun _ => Nat × Terms × Bool)
      (st.1, (v % 8192, numT (v / 8192 % 8)) :: st.2.1, st.2.2)
      (st.1 + 1, [], st.2.2 && eqTL (revT ((v % 8192, numT (v / 8192 % 8)) :: st.2.1) []) (tauT st.1))
      (Nat.beq (v / 65536) 1) := by
  obtain ⟨k, acc, ok⟩ := st
  cases ok <;> rfl

theorem tauStep_end {st : Nat × Terms × Bool} {v : Nat} (h : v / 65536 = 1) : tauStep st v =
    (st.1 + 1, [], st.2.2 && eqTL (revT ((v % 8192, numT (v / 8192 % 8)) :: st.2.1) []) (tauT st.1)) := by
  have hb : Nat.beq (v / 65536) 1 = true := by
    rw [h]
    rfl
  rw [tauStep_eq, hb]

theorem tauStep_mid {st : Nat × Terms × Bool} {v : Nat} (h : v / 65536 ≠ 1) :
    tauStep st v = (st.1, (v % 8192, numT (v / 8192 % 8)) :: st.2.1, st.2.2) := by
  have hb : Nat.beq (v / 65536) 1 = false := by
    cases e : Nat.beq (v / 65536) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h
  rw [tauStep_eq, hb]

@[expose] def TInv (rr : Array (Array (Nat × Int)) × Array (Nat × Int)) (st : Nat × Terms × Bool) : Prop :=
  st.1 = rr.1.size ∧ st.2.1 = rr.2.toList.reverse ∧
    (st.2.2 = true → ∀ j < rr.1.size, (rr.1[j]!).toList = tauT j)

theorem tInv_step {rr : Array (Array (Nat × Int)) × Array (Nat × Int)} {st : Nat × Terms × Bool}
    (h : TInv rr st) (v : Nat) : TInv (entStep rr v) (tauStep st v) := by
  obtain ⟨e1, e2, e3⟩ := h
  have ht : numT (v / 8192 % 8) = CFSG.Monster.B.Native.numOfCode (v / 8192 % 8) :=
    numT_eq _ (Nat.mod_lt _ (by decide))
  by_cases hv : v / 65536 = 1
  · rw [tauStep_end hv, ht]
    have ex : entStep rr v =
        (rr.1.push (rr.2.push (v % 8192, CFSG.Monster.B.Native.numOfCode (v / 8192 % 8))), #[]) := by
      unfold entStep
      rw [if_pos hv]
    rw [ex]
    refine ⟨by rw [Array.size_push, e1], rfl, ?_⟩
    intro hok j hj
    rw [Bool.and_eq_true] at hok
    obtain ⟨hok1, hok2⟩ := hok
    rw [Array.size_push] at hj
    change ((rr.1.push _)[j]!).toList = tauT j
    rw [CFSG.KC.BM.Pkt.getElem!_push]
    by_cases h1 : j < rr.1.size
    · rw [if_pos h1]
      exact e3 hok1 j h1
    · have h2 : j = rr.1.size := by omega
      rw [if_neg h1, if_pos h2, h2, ← e1, ← eqTL_true hok2, revT_eq, List.append_nil, List.reverse_cons,
        e2, List.reverse_reverse, Array.toList_push]
  · rw [tauStep_mid hv, ht]
    have ex : entStep rr v =
        (rr.1, rr.2.push (v % 8192, CFSG.Monster.B.Native.numOfCode (v / 8192 % 8))) := by
      unfold entStep
      rw [if_neg hv]
    rw [ex]
    refine ⟨e1, ?_, e3⟩
    change _ :: st.2.1 = (rr.2.push _).toList.reverse
    rw [Array.toList_push, List.reverse_append, List.reverse_singleton, List.singleton_append, e2]

theorem tInv_foldl : ∀ (vs : List Nat) (rr : Array (Array (Nat × Int)) × Array (Nat × Int))
    (st : Nat × Terms × Bool), TInv rr st → TInv (vs.foldl entStep rr) (vs.foldl tauStep st)
  | [], _, _, h => h
  | v :: vs, _, _, h => tInv_foldl vs _ _ (tInv_step h v)

theorem tauScan_foldl (N : Nat) (st : Nat × Terms × Bool) : ∀ n : Nat,
    tauScan N n st = ((List.range n).map (entV N)).foldl tauStep st
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.foldl_append, ← tauScan_foldl N st n]
    rfl

theorem tauLineChk_eq {p : Nat × Nat} (h : tauLineChk p = true) :
    tauScan p.1 (p.2 / 3) (0, [], true) = (4371, [], true) := by
  unfold tauLineChk at h
  generalize tauScan p.1 (p.2 / 3) (0, [], true) = st at h ⊢
  obtain ⟨a, L, ok⟩ := st
  change Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false ok (nilB L)) (Nat.beq a 4371) = true at h
  cases hb : Nat.beq a 4371
  · rw [hb] at h
    change false = true at h
    exact Bool.noConfusion h
  rw [hb] at h
  cases hn : nilB L
  · rw [hn] at h
    change false = true at h
    exact Bool.noConfusion h
  rw [hn] at h
  change ok = true at h
  rw [Nat.eq_of_beq_eq_true hb, nilB_eq hn, h]

theorem tau_rows {p : Nat × Nat} (h : tauLineChk p = true) :
    (lineRows p).size = 4371 ∧ ∀ k < 4371, ((lineRows p)[k]!).toList = tauT k := by
  have h' := tauLineChk_eq h
  rw [tauScan_foldl] at h'
  have hI : TInv (#[], #[]) (0, [], true) := ⟨rfl, rfl, fun _ j hj => absurd hj (Nat.not_lt_zero _)⟩
  have hF := tInv_foldl ((List.range (p.2 / 3)).map (entV p.1)) _ _ hI
  rw [h'] at hF
  obtain ⟨e1, -, e3⟩ := hF
  unfold lineRows
  exact ⟨e1.symm, fun k hk => e3 rfl k (e1 ▸ hk)⟩

end CFSG.KC.Rep4371X

end
