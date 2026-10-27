module

public import CFSG.Certificates.Kernel.Spor.F3LaneSound
public import Certificates.Data.Kernel.Spor.F3LaneRows
import all CFSG.Certificates.Kernel.Spor.F3LaneSound

public section

namespace CFSG.KS.F3L

open CFSG.F3.Native CFSG.KC.Enum

theorem bitK_eq (x j : Nat) : bitK x j = (x.testBit j).toNat := by
  unfold bitK
  change (x >>> j) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

theorem entR_spec {rp rm j e : Nat} (h : entR rp rm j e = true) :
    rp.testBit j = decide (e % 3 = 1) ∧ rm.testBit j = decide (e % 3 = 2) := by
  unfold entR at h
  rw [strictB_eq', bAnd_eq, Bool.and_eq_true, bitK_eq, bitK_eq] at h
  have e1 : Nat.mod e 3 = e % 3 := rfl
  rw [e1] at h
  obtain ⟨h1, h2⟩ := h
  have ht : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize e % 3 = t at h1 h2 ht ⊢
  interval_cases t <;> cases hp : rp.testBit j <;> cases hm : rm.testBit j <;>
    simp_all [nbeq]

theorem rowsBody_spec {d : Nat} (hd : 0 < d) (L : V) (cs : List Char) : ∀ (i j : Nat), j < d →
    rowsBody d L.p L.m cs i j (blk d L i).p (blk d L i).m = true →
    d * d ≤ d * i + j + (entsOf cs).length ∧
      ∀ idx (hi : idx < (entsOf cs).length), d * i + j + idx < d * d →
        L.p.testBit (d * i + j + idx) = decide ((entsOf cs)[idx] % 3 = 1) ∧
        L.m.testBit (d * i + j + idx) = decide ((entsOf cs)[idx] % 3 = 2) := by
  induction cs with
  | nil =>
    intro i j _ h
    have : d ≤ i := Nat.le_of_ble_eq_true h
    have := Nat.mul_le_mul_left d this
    exact ⟨by omega, fun idx hi => absurd hi (by simp [entsOf])⟩
  | cons ch cs ih =>
    intro i j hj h
    by_cases hi : i < d
    swap
    · have := Nat.mul_le_mul_left d (Nat.le_of_not_lt hi)
      exact ⟨by omega, fun idx _ h' => absurd h' (by omega)⟩
    change strictB (Char.toNat ch) (fun c =>
      bIf(wsK c, rowsBody d L.p L.m cs i j (blk d L i).p (blk d L i).m,
        bIf(Nat.blt i d,
          bAnd(entR (blk d L i).p (blk d L i).m j (entK c),
            strictB (Nat.succ j) fun j' =>
              bIf(Nat.beq j' d,
                strictB (Nat.succ i) fun i' =>
                  rowAt d L.p L.m i' (rowsBody d L.p L.m cs i' (nat_lit 0)),
                rowsBody d L.p L.m cs i j' (blk d L i).p (blk d L i).m)),
          true))) = true at h
    rw [strictB_eq', wsK_eq] at h
    cases hw : wsChar ch <;> rw [hw] at h
    · have e : entsOf (ch :: cs) = dg ch :: entsOf cs := by
        simp [entsOf, hw]
      rw [e]
      have hb : Nat.blt i d = true := Nat.blt_eq.mpr hi
      rw [hb, bAnd_eq, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have hent := entR_spec h1
      rw [blk_p, blk_m] at hent
      simp only [hj, decide_true, Bool.true_and, entK_eq] at hent
      rw [strictB_eq'] at h2
      have key : d * d ≤ d * i + (j + 1) + (entsOf cs).length ∧
          ∀ idx (hi : idx < (entsOf cs).length), d * i + (j + 1) + idx < d * d →
            L.p.testBit (d * i + (j + 1) + idx) = decide ((entsOf cs)[idx] % 3 = 1) ∧
            L.m.testBit (d * i + (j + 1) + idx) = decide ((entsOf cs)[idx] % 3 = 2) := by
        cases hb2 : Nat.beq (Nat.succ j) d <;> rw [hb2] at h2
        · have hj' : j + 1 < d := by
            have := Nat.ne_of_beq_eq_false hb2
            omega
          exact ih i (j + 1) hj' h2
        · have hj' : j + 1 = d := Nat.eq_of_beq_eq_true hb2
          change strictB (Nat.succ i) (fun i' =>
            rowAt d L.p L.m i' (rowsBody d L.p L.m cs i' (nat_lit 0))) = true at h2
          rw [strictB_eq'] at h2
          unfold rowAt at h2
          rw [strictB_eq', strictB_eq'] at h2
          have := ih (i + 1) 0 hd h2
          have ee : d * (i + 1) + 0 = d * i + (j + 1) := by
            rw [Nat.mul_succ]
            omega
          rw [ee] at this
          exact this
      obtain ⟨a, b⟩ := key
      refine ⟨by simp; omega, fun idx hidx hk => ?_⟩
      rcases idx with _ | idx
      · simpa using hent
      · rw [List.getElem_cons_succ, show d * i + j + (idx + 1) = d * i + (j + 1) + idx by omega]
        exact b idx (by simpa using hidx) (by omega)
    · have e : entsOf (ch :: cs) = entsOf cs := by
        simp [entsOf, hw]
      rw [e]
      exact ih i j hj h

theorem rowsHead_spec {d : Nat} {L : V} : ∀ cs : List Char, rowsHead d L.p L.m cs = true →
    rowsBody d L.p L.m ((cs.dropWhile (· != '\n')).drop 1) 0 0 (blk d L 0).p (blk d L 0).m = true
  | [], h => by
    change Nat.ble d 0 = true at h
    exact h
  | ch :: cs, h => by
    change Bool.rec (motive := fun _ => Bool) (rowsHead d L.p L.m cs)
      (rowAt d L.p L.m (nat_lit 0) (rowsBody d L.p L.m cs (nat_lit 0) (nat_lit 0)))
      (Nat.beq (Char.toNat ch) 10) = true at h
    cases hb : Nat.beq (Char.toNat ch) 10 <;> rw [hb] at h
    · have hne : (ch != '\n') = true := by
        rw [bne, beq_char]
        have : ('\n' : Char).toNat = 10 := rfl
        rw [this, ← nbeq, hb]
        rfl
      rw [List.dropWhile_cons_of_pos (p := fun x => x != '\n') hne]
      exact rowsHead_spec cs h
    · have hne : (ch != '\n') = false := by
        rw [bne, beq_char]
        have : ('\n' : Char).toNat = 10 := rfl
        rw [this, ← nbeq, hb]
        rfl
      rw [List.dropWhile_cons_of_neg (p := fun x => x != '\n') (by simp [hne])]
      change rowAt d L.p L.m (nat_lit 0) (rowsBody d L.p L.m cs (nat_lit 0) (nat_lit 0)) = true at h
      unfold rowAt at h
      rw [strictB_eq', strictB_eq'] at h
      exact h

theorem rowsOf_seedRows {d : Nat} (hd : 0 < d) {L : V} {cs : List Char}
    (h : seedRowsK d L cs = true) : rowsOf d (String.ofList cs) = unlane d L := by
  unfold seedRowsK at h
  rw [strictB_eq', strictB_eq'] at h
  obtain ⟨hlen, hent⟩ := rowsBody_spec hd L _ 0 0 hd (rowsHead_spec cs h)
  have hdec : decodeEntries (String.ofList cs) = entsOf ((cs.dropWhile (· != '\n')).drop 1) := by
    unfold decodeEntries entsOf dg
    rw [String.toList_ofList]
  generalize entsOf ((cs.dropWhile (· != '\n')).drop 1) = E at hdec hlen hent
  simp only [Nat.mul_zero, Nat.zero_add] at hlen hent
  apply Array.ext
  · unfold rowsOf
    rw [Array.size_ofFn, unlane_size]
  · intro i h1 h2
    have hi : i < d := by rwa [unlane_size] at h2
    rw [← getElem!_pos (unlane d L) i h2, unlane_get L hi]
    unfold rowsOf
    simp only [Array.getElem_ofFn, hdec]
    rw [ofFn_eq_fold]
    apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro j
    · rw [(fold_ofFnStep_bits _ j d).1, blk_p]
      by_cases hj : j < d
      · have hk : d * i + j < d * d := by
          have : d * i + j < d * (i + 1) := by rw [Nat.mul_succ]; omega
          exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ (by omega))
        have hidx : i * d + j < E.length := by
          have : i * d + j = d * i + j := by rw [Nat.mul_comm]
          omega
        have := (hent (i * d + j) hidx (by
          have : i * d + j = d * i + j := by rw [Nat.mul_comm]
          omega)).1
        rw [show d * i + j = i * d + j by rw [Nat.mul_comm], this]
        simp only [hj, decide_true, Bool.true_and, List.getElem?_toArray,
          List.getElem?_eq_getElem hidx, Option.getD_some]
      · simp [hj]
    · rw [(fold_ofFnStep_bits _ j d).2, blk_m]
      by_cases hj : j < d
      · have hk : d * i + j < d * d := by
          have : d * i + j < d * (i + 1) := by rw [Nat.mul_succ]; omega
          exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ (by omega))
        have hidx : i * d + j < E.length := by
          have : i * d + j = d * i + j := by rw [Nat.mul_comm]
          omega
        have := (hent (i * d + j) hidx (by
          have : i * d + j = d * i + j := by rw [Nat.mul_comm]
          omega)).2
        rw [show d * i + j = i * d + j by rw [Nat.mul_comm], this]
        simp only [hj, decide_true, Bool.true_and, List.getElem?_toArray,
          List.getElem?_eq_getElem hidx, Option.getD_some]
      · simp [hj]

end CFSG.KS.F3L

end
