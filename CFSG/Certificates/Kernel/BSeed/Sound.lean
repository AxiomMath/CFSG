module

public import Certificates.Data.Kernel.BSeed.Seed
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.KC.BSeed

open CFSG.KC

@[expose] noncomputable def rowsMat (d : Nat) (R : Nat → Nat) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  fun i j => if (R i.val).testBit j.val then 1 else 0

end CFSG.KC.BSeed

end

namespace CFSG.KC.BSeed

open CFSG.KC

def bitOf (d : Nat) (R : Nat → Nat) (p : Nat) : Nat := if (R (p / d)).testBit (p % d) then 1 else 0

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem range'_join {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    List.range' a (b - a) ++ List.range' b (c - b) = List.range' a (c - a) := by
  have := @List.range'_append_1 a (b - a) (c - b)
  rw [Nat.add_sub_cancel' h1] at this
  rw [this]
  congr 1
  omega

theorem seedRun_cons0 (d i1 : Nat) (R : Nat → Nat) (c : Nat) (bs : List Nat) (i j r : Nat) :
    seedRun d i1 R (c :: bs) 0 i j r =
      bIf(Nat.beq c 10, seedRun d i1 R bs 0 i j r,
        bIf(Nat.ble 48 c, bIf(Nat.ble c 49,
          andB (Nat.blt i i1) (andB (Nat.beq (c - 48) (r &&& 1))
            (strictB (j + 1) (fun j' => Bool.rec (motive := fun _ => Bool)
              (strictB (r >>> 1) (fun r' => seedRun d i1 R bs 0 i j' r'))
              (andB (Nat.beq (r >>> 1) 0)
                (strictB (i + 1) (fun i' => seedRun d i1 R bs 0 i' 0 (R i'))))
              (Nat.beq j' d)))), false), false)) := rfl

theorem seedRun_cons1 (d i1 : Nat) (R : Nat → Nat) (c : Nat) (bs : List Nat) (i j r : Nat) :
    seedRun d i1 R (c :: bs) 1 i j r =
      bIf(Nat.beq c 10, seedRun d i1 R bs 0 i j r, seedRun d i1 R bs 1 i j r) := rfl

theorem seedRun_body {d i1 : Nat} {R : Nat → Nat} : ∀ (bs : List Nat) (i j r : Nat),
    (i < i1 → j < d ∧ r = R i >>> j) → seedRun d i1 R bs 0 i j r = true →
      (∀ c ∈ bs, c = 10 ∨ c = 48 ∨ c = 49) ∧ i * d + j ≤ i1 * d ∧
        (bs.filter (· != 10)).map (· - 48) =
          (List.range' (i * d + j) (i1 * d - (i * d + j))).map (bitOf d R)
  | [], i, j, r, _, h => by
    have h' : andB (Nat.beq 0 0) (andB (Nat.beq i i1) (Nat.beq j 0)) = true := h
    obtain ⟨-, h2⟩ := andB_true h'
    obtain ⟨h2, h3⟩ := andB_true h2
    obtain rfl := Nat.eq_of_beq_eq_true h2
    obtain rfl := Nat.eq_of_beq_eq_true h3
    simp
  | c :: bs, i, j, r, hinv, h => by
    rw [seedRun_cons0] at h
    by_cases h10 : c = 10
    · subst h10
      obtain ⟨ha, hb, hc⟩ := seedRun_body bs i j r hinv h
      refine ⟨?_, hb, ?_⟩
      · intro c hc'
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact Or.inl rfl
        · exact ha c hc'
      · simpa using hc
    have hb10 : Nat.beq c 10 = false := beq_false h10
    rw [hb10] at h
    cases h48 : Nat.ble 48 c
    · rw [h48] at h
      exact absurd h Bool.false_ne_true
    rw [h48] at h
    cases h49 : Nat.ble c 49
    · rw [h49] at h
      exact absurd h Bool.false_ne_true
    rw [h49] at h
    have hc4 : c = 48 ∨ c = 49 := by
      have := Nat.le_of_ble_eq_true h48
      have := Nat.le_of_ble_eq_true h49
      omega
    obtain ⟨hi, h⟩ := andB_true h
    obtain ⟨hdig, h⟩ := andB_true h
    have hi : i < i1 := Nat.le_of_ble_eq_true hi
    obtain ⟨hj, rfl⟩ := hinv hi
    have hdig : c - 48 = bitOf d R (i * d + j) := by
      have e1 : (i * d + j) / d = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
      have e2 : (i * d + j) % d = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      rw [Nat.eq_of_beq_eq_true hdig, bitOf, e1, e2, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
        Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (R i / 2 ^ j) with h' | h' <;> simp [h']
    rw [strictB_eq] at h
    have hcons : ((c :: bs).filter (· != 10)).map (· - 48) =
        (c - 48) :: (bs.filter (· != 10)).map (· - 48) := by
      simp [h10]
    have hmem : (∀ c ∈ bs, c = 10 ∨ c = 48 ∨ c = 49) → ∀ c' ∈ c :: bs, c' = 10 ∨ c' = 48 ∨ c' = 49 :=
      fun hbs c' hc' => by
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact Or.inr hc4
        · exact hbs c' hc'
    by_cases hjd : j + 1 = d
    · have e : Nat.beq (j + 1) d = true := hjd ▸ Nat.beq_refl _
      simp only [e] at h
      obtain ⟨-, h⟩ := andB_true h
      rw [strictB_eq] at h
      obtain ⟨ha, hb, hc⟩ := seedRun_body bs (i + 1) 0 (R (i + 1))
        (fun _ => ⟨by omega, by rw [Nat.shiftRight_zero]⟩) h
      have hp : (i + 1) * d + 0 = i * d + j + 1 := by rw [Nat.add_mul]; omega
      rw [hp] at hb hc
      refine ⟨hmem ha, by omega, ?_⟩
      rw [hcons, hc, hdig, show i1 * d - (i * d + j) = (i1 * d - (i * d + j + 1)) + 1 by omega,
        List.range'_succ, List.map_cons]
    · have e : Nat.beq (j + 1) d = false := beq_false hjd
      simp only [e] at h
      rw [strictB_eq] at h
      obtain ⟨ha, hb, hc⟩ := seedRun_body bs i (j + 1) (R i >>> j >>> 1)
        (fun _ => ⟨by omega, by rw [Nat.shiftRight_add]⟩) h
      refine ⟨hmem ha, by omega, ?_⟩
      rw [hcons, hc, hdig, show i1 * d - (i * d + j) = (i1 * d - (i * d + (j + 1))) + 1 by omega,
        List.range'_succ, List.map_cons]
      rfl

theorem seedRun_hdr {d i1 : Nat} {R : Nat → Nat} : ∀ (bs : List Nat) (i j r : Nat),
    seedRun d i1 R bs 1 i j r = true →
      ∃ pre rest, bs = pre ++ 10 :: rest ∧ (∀ c ∈ pre, c ≠ 10) ∧ seedRun d i1 R rest 0 i j r = true
  | [], i, j, _, h => by
    have h' : andB (Nat.beq 1 0) (andB (Nat.beq i i1) (Nat.beq j 0)) = true := h
    exact absurd (andB_true h').1 Bool.false_ne_true
  | c :: bs, i, j, r, h => by
    rw [seedRun_cons1] at h
    by_cases h10 : c = 10
    · subst h10
      exact ⟨[], bs, rfl, fun _ h => absurd h List.not_mem_nil, h⟩
    · rw [beq_false h10] at h
      obtain ⟨pre, rest, rfl, hpre, hr⟩ := seedRun_hdr bs i j r h
      refine ⟨c :: pre, rest, rfl, fun c' hc' => ?_, hr⟩
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact h10
      · exact hpre c' hc'

theorem ofNat_eq_nl {c : Nat} (h : Char.ofNat c = '\n') : c = 10 := by
  have h2 := congrArg Char.toNat h
  unfold Char.ofNat at h2
  split at h2
  · exact h2
  · exact absurd h2 (by decide)

theorem dropWhile_nl (pre : List Nat) (hpre : ∀ c ∈ pre, c ≠ 10) (t : List Char) :
    (pre.map Char.ofNat ++ '\n' :: t).dropWhile (· != '\n') = '\n' :: t := by
  induction pre with
  | nil => simp
  | cons c pre ih =>
    have hc : (Char.ofNat c != '\n') = true :=
      bne_iff_ne.2 fun h => hpre c List.mem_cons_self (ofNat_eq_nl h)
    rw [List.map_cons, List.cons_append, List.dropWhile_cons]
    simp only [hc, ↓reduceIte]
    exact ih fun c' h => hpre c' (List.mem_cons_of_mem _ h)

theorem digits_eq : ∀ (L : List Nat), (∀ c ∈ L, c = 10 ∨ c = 48 ∨ c = 49) →
    ((L.map Char.ofNat).filter fun c => !CFSG.Blueprint.NativeSporadic.asciiWhitespace c).map
        (fun c => if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0) =
      (L.filter (· != 10)).map (· - 48)
  | [], _ => rfl
  | c :: L, h => by
    have ih := digits_eq L fun c' h' => h c' (List.mem_cons_of_mem _ h')
    rcases h c List.mem_cons_self with rfl | rfl | rfl
    · rw [List.map_cons, List.filter_cons_of_neg (by decide), ih]
      rfl
    · rw [List.map_cons, List.filter_cons_of_pos (by decide), List.map_cons, ih,
        List.filter_cons_of_pos (by decide), List.map_cons]
      rfl
    · rw [List.map_cons, List.filter_cons_of_pos (by decide), List.map_cons, ih,
        List.filter_cons_of_pos (by decide), List.map_cons]
      rfl

end CFSG.KC.BSeed

public section

namespace CFSG.KC.BSeed

open CFSG.KC

theorem decode_of_seedChunkOK {d K : Nat} {B : Nat → List Nat} {st R : Nat → Nat} (hK : 0 < K)
    (h0 : st 0 = 0) (hd : st K = d)
    (h : ∀ k < K, seedChunkOK d (B k) (Nat.beq k 0) (st k) (st (k + 1)) R = true) :
    CFSG.Blueprint.NativeSporadic.decode 2 d 1
      (String.ofList (((List.range K).flatMap B).map Char.ofNat)) = rowsMat d R := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · funext i
    exact i.elim0
  have hch : ∀ k < K, st k ≤ st (k + 1) ∧
      seedRun d (st (k + 1)) R (B k) (if k = 0 then 1 else 0) (st k) 0 (R (st k)) = true := by
    intro k hk
    obtain ⟨h1, h2⟩ := andB_true (h k hk)
    refine ⟨Nat.le_of_ble_eq_true h1, ?_⟩
    by_cases hk0 : k = 0
    · subst hk0
      exact h2
    · rw [beq_false hk0] at h2
      simp only [hk0, ↓reduceIte]
      exact h2
  have inv : ∀ k, st k < st (k + 1) → 0 < d ∧ R (st k) = R (st k) >>> 0 :=
    fun _ _ => ⟨hd0, Nat.shiftRight_zero.symm⟩
  obtain ⟨pre, rest, hB0, hpre, hrest⟩ := by
    have := (hch 0 hK).2
    simp only [↓reduceIte] at this
    exact seedRun_hdr _ _ _ _ this
  obtain ⟨ra, rb, rc⟩ := seedRun_body rest (st 0) 0 _ (fun h => inv 0 h) hrest
  have tail : ∀ n, n + 1 ≤ K → (∀ c ∈ (List.range' 1 n).flatMap B, c = 10 ∨ c = 48 ∨ c = 49) ∧
      st 1 ≤ st (n + 1) ∧
      (((List.range' 1 n).flatMap B).filter (· != 10)).map (· - 48) =
        (List.range' (st 1 * d) (st (n + 1) * d - st 1 * d)).map (bitOf d R) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      obtain ⟨ia, ib, ic⟩ := ih (by omega)
      obtain ⟨hle, hk⟩ := hch (n + 1) (by omega)
      simp only [Nat.add_one_ne_zero, ↓reduceIte] at hk
      obtain ⟨ka, kb, kc⟩ := seedRun_body (B (n + 1)) (st (n + 1)) 0 _ (fun h => inv _ h) hk
      rw [List.range'_1_concat, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, Nat.add_comm 1 n]
      refine ⟨fun c hc => ?_, by omega, ?_⟩
      · rcases List.mem_append.1 hc with hc | hc
        · exact ia c hc
        · exact ka c hc
      · rw [List.filter_append, List.map_append, ic, kc, ← List.map_append]
        simp only [Nat.add_zero]
        rw [range'_join (Nat.mul_le_mul_right d ib) (Nat.mul_le_mul_right d hle)]
  obtain ⟨ta, tb, tc⟩ := tail (K - 1) (by omega)
  rw [Nat.sub_add_cancel hK, hd] at tb tc
  have hflat : (List.range K).flatMap B = pre ++ 10 :: (rest ++ (List.range' 1 (K - 1)).flatMap B) := by
    rw [List.range_eq_range', show K = (K - 1) + 1 by omega, List.range'_succ, List.flatMap_cons,
      hB0, Nat.add_sub_cancel, List.append_assoc, List.cons_append]
  have hall : ∀ c ∈ rest ++ (List.range' 1 (K - 1)).flatMap B, c = 10 ∨ c = 48 ∨ c = 49 := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact ra c hc
    · exact ta c hc
  have hent : (((rest ++ (List.range' 1 (K - 1)).flatMap B).filter (· != 10)).map (· - 48)) =
      (List.range' 0 (d * d)).map (bitOf d R) := by
    rw [List.filter_append, List.map_append, rc, tc, ← List.map_append]
    have := range'_join (Nat.zero_le _) (Nat.mul_le_mul_right d tb)
    simp only [h0, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.sub_zero] at this ⊢
    rw [this]
  funext i j
  unfold CFSG.Blueprint.NativeSporadic.decode
  simp only [↓reduceIte]
  rw [String.toList_ofList, hflat, List.map_append, List.map_cons, show Char.ofNat 10 = '\n' from rfl,
    dropWhile_nl pre hpre, List.drop_one, List.tail_cons, digits_eq _ hall, hent]
  have hij : i.val * d + j.val < d * d := by
    have := i.isLt
    have := j.isLt
    nlinarith
  rw [List.getElem?_map, List.getElem?_range' hij, Option.map_some, Option.getD_some, rowsMat,
    bitOf]
  have e1 : (i.val * d + j.val) / d = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd0, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have e2 : (i.val * d + j.val) % d = j.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  rw [Nat.zero_add, Nat.one_mul, e1, e2]
  split <;> simp

end CFSG.KC.BSeed

end
