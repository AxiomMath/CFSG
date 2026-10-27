module

public import Certificates.Data.Kernel.Spor.Co2Shape
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.Co2Shape

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem hasBit_eq (M l : Nat) : hasBit M l = M.testBit l := by
  unfold hasBit
  change decide (0 < M &&& 1 <<< l) = M.testBit l
  rw [Nat.one_shiftLeft]
  by_cases h : M.testBit l
  · have hx : (M &&& 2 ^ l).testBit l = true := by
      rw [Nat.testBit_and, h, Nat.testBit_two_pow_self]
      rfl
    have hpos : 0 < M &&& 2 ^ l := by
      rcases Nat.eq_zero_or_pos (M &&& 2 ^ l) with h0 | h0
      · rw [h0, Nat.zero_testBit] at hx
        exact absurd hx (by decide)
      · exact h0
    rw [h]
    exact decide_eq_true hpos
  · have h0 : M &&& 2 ^ l = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : l = j
      · subst hj
        simp [h]
      · simp [hj]
    rw [h0, Bool.not_eq_true _ |>.mp h]
    rfl

theorem distinctL_sound {n : Nat} : ∀ {l : List Nat} {M : Nat}, distinctL n l M = true →
    l.Nodup ∧ ∀ x ∈ l, x < n ∧ M.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, M, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (strictB (Nat.lor M (Nat.shiftLeft (nat_lit 1) x)) (distinctL n l))
          (Bool.rec (motive := fun _ => Bool) true false (hasBit M x)))
        (Nat.blt x n) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    rw [strictB_eq] at h4
    have hx : M.testBit x = false := by
      rw [← hasBit_eq]
      cases hb : hasBit M x
      · rfl
      · rw [hb] at h3
        exact absurd h3 (by decide)
    obtain ⟨hnd, hl⟩ := distinctL_sound h4
    have key : ∀ y ∈ l, y < n ∧ M.testBit y = false ∧ y ≠ x := by
      intro y hy
      obtain ⟨hyn, hyb⟩ := hl y hy
      have e : (Nat.lor M (Nat.shiftLeft 1 x)).testBit y = (M.testBit y || decide (y = x)) := by
        change (M ||| 1 <<< x).testBit y = _
        rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
        by_cases hxy : y = x
        · subst hxy
          simp
        · simp [hxy, Ne.symm hxy]
      rw [e, Bool.or_eq_false_iff] at hyb
      exact ⟨hyn, hyb.1, by simpa using hyb.2⟩
    refine ⟨List.nodup_cons.2 ⟨fun hm => (key x hm).2.2 rfl, hnd⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact ⟨Nat.le_of_ble_eq_true h1, hx⟩
    · exact ⟨(key y hy').1, (key y hy').2.1⟩

@[expose] def bucketL (k b : Nat) (l : List Nat) : List Nat :=
  (l.filter fun x => x / 2 ^ k == b).map (· % 2 ^ k)

theorem nodup_of_buckets {l : List Nat} {k : Nat}
    (h : ∀ b, (bucketL k b l).Nodup) : l.Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro a
  have hb := h (a / 2 ^ k)
  unfold bucketL at hb
  have hf : (l.filter fun x => x / 2 ^ k == a / 2 ^ k).Nodup := hb.of_map _
  have e : (l.filter fun x => x / 2 ^ k == a / 2 ^ k).count a = l.count a := by
    rw [List.count_filter]
    simp
  rw [← e]
  exact List.nodup_iff_count_le_one.1 hf a

theorem bucketL_nil_of_ge {l : List Nat} {k b n : Nat} (hl : ∀ x ∈ l, x < n * 2 ^ k)
    (hb : n ≤ b) : bucketL k b l = [] := by
  unfold bucketL
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro x hx
  have := hl x hx
  have : x / 2 ^ k < n := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
    exact this
  simp only [beq_iff_eq]
  omega

theorem nodup_of_bucketsK {l : List Nat} {k n : Nat} (hl : ∀ x ∈ l, x < n * 2 ^ k)
    (h : ∀ b < n, distinctL (2 ^ k) (bucketL k b l) 0 = true) : l.Nodup := by
  refine nodup_of_buckets (k := k) fun b => ?_
  rcases Nat.lt_or_ge b n with hb | hb
  · exact (distinctL_sound (h b hb)).1
  · rw [bucketL_nil_of_ge hl hb]
    exact List.nodup_nil

end CFSG.KS.Co2Shape

end
