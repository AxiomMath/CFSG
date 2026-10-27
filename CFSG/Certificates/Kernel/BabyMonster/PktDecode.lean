module

public import CFSG.Certificates.Kernel.BabyMonster.PktCheck
public import CFSG.Certificates.Kernel.BabyMonster.DySound
public import Certificates.Data.CFSGNative.MonsterB.PacketData

public section

namespace CFSG.KC.BM.Dy

theorem fld_shl16 (b i c : Nat) : fld (b <<< (16 * i)) c = if c < i then 0 else fld b (c - i) := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [fld_testBit, Nat.testBit_shiftLeft]
  by_cases hr : r < 16
  · rw [decide_eq_true hr, Bool.true_and]
    by_cases hc : c < i
    · rw [ite_eq_left hc, Nat.zero_testBit, decide_eq_false (by omega), Bool.false_and]
    · rw [ite_eq_right hc, fld_testBit, decide_eq_true hr, Bool.true_and,
        decide_eq_true (by omega), Bool.true_and,
        show 16 * c + r - 16 * i = 16 * (c - i) + r by omega]
  · rw [decide_eq_false hr, Bool.false_and]
    split
    · rw [Nat.zero_testBit]
    · rw [fld_testBit, decide_eq_false hr, Bool.false_and]

theorem fld_lor (a b t : Nat) : fld (a ||| b) t = fld a t ||| fld b t := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, fld_testBit, fld_testBit, fld_testBit, Nat.testBit_or]
  cases decide (i < 16) <;> rfl

theorem fld_small {c : Nat} (hc : c < 65536) (t : Nat) : fld c t = if t = 0 then c else 0 := by
  rcases t with _ | t
  · rw [fld_zero, Nat.mod_eq_of_lt hc, ite_eq_left rfl]
  · rw [fld_succ, Nat.div_eq_of_lt hc, ite_eq_right (Nat.succ_ne_zero t)]
    simp [fld]

theorem fld_recOr {s : Nat → Nat → Nat} {c : Nat → Nat}
    (hs : ∀ k acc, s k acc = acc ||| (c k <<< (16 * k))) (hc : ∀ k, c k < 65536) :
    ∀ n t, fld (Nat.rec (motive := fun _ => Nat) 0 s n) t = if t < n then c t else 0
  | 0, t => by
    change fld 0 t = if t < 0 then c t else 0
    simp [fld]
  | n + 1, t => by
    change fld (s n (Nat.rec (motive := fun _ => Nat) 0 s n)) t = _
    rw [hs, fld_lor, fld_recOr hs hc n t, fld_shl16, fld_small (hc n)]
    by_cases h1 : t < n
    · simp [h1, show t < n + 1 by omega]
    · by_cases h2 : t = n
      · subst h2
        simp
      · simp [h1, show ¬ t < n + 1 by omega, show t - n ≠ 0 by omega]

end CFSG.KC.BM.Dy

namespace CFSG.KC.BM.Pkt

open CFSG.KC.BM CFSG.KC.BM.B64 CFSG.KC.BM.Lat CFSG.KC.YModel CFSG.KC.BM.Dy

@[expose] noncomputable def tfield (T t : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 16) t)) (nat_lit 65535)

@[expose] noncomputable def tabOK (T : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => andB ih (andB (Nat.blt (Nat.mod (tfield T t) (nat_lit 8192)) (nat_lit 4371))
      (Nat.blt (tfield T t) (nat_lit 16384))))
    (nat_lit 4371)

theorem tfield_fld (T t : Nat) : tfield T t = Dy.fld T t := by
  unfold tfield
  rw [Dy.land65535, Dy.fld_zero, Dy.fld]
  change T >>> (16 * t) % 65536 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem tab_facts {T : Nat} (h : tabOK T = true) :
    ∀ t < 4371, Dy.fld T t % 8192 < 4371 ∧ Dy.fld T t < 16384 := by
  intro t ht
  unfold tabOK at h
  obtain ⟨h1, h2⟩ := Dy.andB_true (@Dy.recAnd_sound (fun t =>
    andB (Nat.blt (Nat.mod (tfield T t) (nat_lit 8192)) (nat_lit 4371))
      (Nat.blt (tfield T t) (nat_lit 16384))) (nat_lit 4371) h t ht)
  have h1' := Nat.le_of_ble_eq_true h1
  have h2' := Nat.le_of_ble_eq_true h2
  rw [tfield_fld] at h1' h2'
  exact ⟨h1', h2'⟩

theorem chAt_testBit (N i k : Nat) :
    (chAt N i).testBit k = (decide (k < 8) && N.testBit (8 * i + k)) := by
  unfold chAt
  change ((N >>> (8 * i)) &&& (2 ^ 8 - 1)).testBit k = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem chAt_lt (N i : Nat) : chAt N i < 256 := by
  unfold chAt
  change (N >>> (8 * i)) &&& (2 ^ 8 - 1) < 256
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem chAt_lor {A B a : Nat} (hA : A < 2 ^ (8 * a)) (i : Nat) :
    chAt (A ||| (B <<< (8 * a))) i = if i < a then chAt A i else chAt B (i - a) := by
  apply Nat.eq_of_testBit_eq
  intro k
  split
  · rw [chAt_testBit, chAt_testBit, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hk : k < 8
    · simp [hk, show ¬ (8 * i + k ≥ 8 * a) by omega]
    · simp [hk]
  · rw [chAt_testBit, chAt_testBit, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hk : k < 8
    · have h0 : A.testBit (8 * i + k) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hk, h0, show 8 * i + k ≥ 8 * a by omega,
        show 8 * i + k - 8 * a = 8 * (i - a) + k by omega]
    · simp [hk]

theorem chAt_shr8 (N i : Nat) : chAt (Nat.shiftRight N 8) i = chAt N (i + 1) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [chAt_testBit, chAt_testBit]
  change (decide (k < 8) && (N >>> 8).testBit (8 * i + k)) = _
  rw [Nat.testBit_shiftRight, show 8 + (8 * i + k) = 8 * (i + 1) + k by omega]

theorem chAt_zero (N : Nat) : Nat.land N (nat_lit 255) = chAt N 0 := rfl

@[expose] noncomputable def pieceBytes (q : Nat × Nat) : List Nat := (List.range q.2).map (chAt q.1)

theorem decChunk_eq : ∀ (len N : Nat) (t : List Nat),
    decChunk len N t = (List.range len).map (chAt N) ++ t
  | 0, _, _ => rfl
  | len + 1, N, t => by
    change Nat.land N 255 :: decChunk len (Nat.shiftRight N 8) t = _
    rw [decChunk_eq len, chAt_zero,
      List.map_congr_left (fun i _ => chAt_shr8 N i), List.range_succ_eq_map, List.map_cons,
      List.map_map]
    rfl

theorem decChunkC_eq : ∀ (len N : Nat) (t : List Char),
    decChunkC len N t = ((List.range len).map (chAt N)).map Char.ofNat ++ t
  | 0, _, _ => rfl
  | len + 1, N, t => by
    change Char.ofNat (Nat.land N 255) :: decChunkC len (Nat.shiftRight N 8) t = _
    rw [decChunkC_eq len, chAt_zero,
      List.map_congr_left (fun i _ => chAt_shr8 N i), List.range_succ_eq_map]
    simp [Function.comp_def]

theorem bytesOf_eq : ∀ L : List (Nat × Nat), bytesOf L = L.flatMap pieceBytes
  | [] => rfl
  | (N, len) :: L => by
    change decChunk len N (bytesOf L) = _
    rw [decChunk_eq, bytesOf_eq L, List.flatMap_cons]
    rfl

theorem charsOf_eq : ∀ L : List (Nat × Nat), charsOf L = (bytesOf L).map Char.ofNat
  | [] => rfl
  | (N, len) :: L => by
    change decChunkC len N (charsOf L) = (decChunk len N (bytesOf L)).map Char.ofNat
    rw [decChunkC_eq, decChunk_eq, charsOf_eq L, List.map_append]

@[expose] noncomputable def piecesOK (CH : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => andB (Nat.beq (Nat.shiftRight q.1 (Nat.mul (nat_lit 8) q.2)) (nat_lit 0)) ih) CH

theorem piecesOK_mem : ∀ {L : List (Nat × Nat)}, piecesOK L = true → ∀ q ∈ L, q.1 < 2 ^ (8 * q.2)
  | [], _, q, hq => absurd hq (by simp)
  | x :: L, h, q, hq => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hq with rfl | hq
    · have e := Nat.eq_of_beq_eq_true h1
      change q.1 >>> (8 * q.2) = 0 at e
      rw [Nat.shiftRight_eq_div_pow] at e
      rcases Nat.lt_or_ge q.1 (2 ^ (8 * q.2)) with hl | hl
      · exact hl
      · exact absurd e (Nat.pos_iff_ne_zero.1 (Nat.div_pos hl (Nat.two_pow_pos _)))
    · exact piecesOK_mem h2 q hq

theorem piecesOK_neg : piecesOK [(256, 1)] = false := by decide +kernel

theorem dropP_eq : ∀ (L : List (Nat × Nat)) (k : Nat), dropP L k = L.drop k
  | [], k => by cases k <;> rfl
  | _ :: _, 0 => rfl
  | _ :: L, k + 1 => by
    change dropP L k = _
    rw [dropP_eq L k]
    rfl

theorem forceP_eq (v : Nat) (x : Nat × Nat) : forceP v x = x := by
  unfold forceP
  cases Nat.beq v 0 <;> rfl

@[expose] noncomputable def joinR (L : List (Nat × Nat)) : Nat → Nat × Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat → Nat × Nat) (fun _ acc => acc)
    (fun q _ ih n acc => Bool.rec (motive := fun _ => Nat × Nat) acc
      (forceP (Nat.lor acc.1 (Nat.shiftLeft q.1 (Nat.mul (nat_lit 8) acc.2)))
        (ih (Nat.sub n (nat_lit 1))
          (Nat.lor acc.1 (Nat.shiftLeft q.1 (Nat.mul (nat_lit 8) acc.2)), Nat.add acc.2 q.2)))
      (Nat.blt (nat_lit 0) n)) L

theorem joinP_eq (CH : List (Nat × Nat)) (s n : Nat) : joinP CH s n = joinR (CH.drop s) n (0, 0) := by
  unfold joinP
  rw [dropP_eq]
  rfl

theorem or_lt_pow {A B a b : Nat} (hA : A < 2 ^ (8 * a)) (hB : B < 2 ^ (8 * b)) :
    A ||| (B <<< (8 * a)) < 2 ^ (8 * (a + b)) := by
  apply Nat.or_lt_two_pow
  · exact lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (by omega))
  · rw [Nat.shiftLeft_eq, show 8 * (a + b) = 8 * b + 8 * a by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hB (Nat.two_pow_pos _)

theorem joinR_bytes : ∀ (L : List (Nat × Nat)), (∀ q ∈ L, q.1 < 2 ^ (8 * q.2)) →
    ∀ (n A a : Nat), A < 2 ^ (8 * a) →
      (joinR L n (A, a)).1 < 2 ^ (8 * (joinR L n (A, a)).2) ∧
      pieceBytes (joinR L n (A, a)) = pieceBytes (A, a) ++ (L.take n).flatMap pieceBytes
  | [], _, n, A, a, hA => by
    refine ⟨hA, ?_⟩
    change pieceBytes (A, a) = pieceBytes (A, a) ++ ([].take n).flatMap pieceBytes
    simp
  | q :: L, hL, 0, A, a, hA => by
    refine ⟨hA, ?_⟩
    change pieceBytes (A, a) = pieceBytes (A, a) ++ ((q :: L).take 0).flatMap pieceBytes
    simp
  | q :: L, hL, n + 1, A, a, hA => by
    have hq := hL q (by simp)
    have e : joinR (q :: L) (n + 1) (A, a) =
        joinR L n (A ||| (q.1 <<< (8 * a)), a + q.2) := by
      change forceP _ _ = _
      rw [forceP_eq]
      rfl
    have hA' := or_lt_pow hA hq
    obtain ⟨h1, h2⟩ := joinR_bytes L (fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')) n _ _ hA'
    rw [e]
    refine ⟨h1, ?_⟩
    rw [h2, List.take_succ_cons, List.flatMap_cons, ← List.append_assoc]
    congr 1
    unfold pieceBytes
    simp only
    rw [List.range_add, List.map_append, List.map_map]
    congr 1
    · exact List.map_congr_left (fun i hi => by
        rw [chAt_lor hA, ite_eq_left (List.mem_range.1 hi)])
    · exact List.map_congr_left (fun i _ => by
        rw [Function.comp_apply, chAt_lor hA, ite_eq_right (by omega), Nat.add_sub_cancel_left])

theorem lineOf_bytes {CH : List (Nat × Nat)} (hc : piecesOK CH = true) (S : List Nat) (i : Nat) :
    pieceBytes (lineOf CH S i) =
      ((CH.drop (lget S i)).take (lget S (i + 1) - lget S i)).flatMap pieceBytes := by
  rw [show lineOf CH S i = joinR (CH.drop (lget S i)) (lget S (i + 1) - lget S i) (0, 0) by
    unfold lineOf
    rw [joinP_eq]
    rfl]
  rw [(joinR_bytes (CH.drop (lget S i)) (fun q hq => piecesOK_mem hc q
    (List.mem_of_mem_drop hq)) (lget S (i + 1) - lget S i) 0 0 (by decide)).2]
  simp [pieceBytes]

@[expose] noncomputable def pieceV (q : Nat × Nat) : Bool :=
  andB (Nat.ble (nat_lit 1) q.2) (andB (Nat.ble q.2 (nat_lit 256))
    (andB (noNL q.1 (Nat.sub q.2 (nat_lit 1)))
      (Bool.rec (motive := fun _ => Bool) (Nat.beq q.2 (nat_lit 256)) true
        (Nat.beq (chAt q.1 (Nat.sub q.2 (nat_lit 1))) (nat_lit 10)))))

@[expose] noncomputable def linesR (S : List Nat) (CH : List (Nat × Nat)) : Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun k p => (k, p))
    (fun q _ ih k p => Bool.rec (motive := fun _ => Nat × Nat) (nat_lit 100000, nat_lit 0)
      (Bool.rec (motive := fun _ => Nat × Nat) (ih k (Nat.succ p))
        (Bool.rec (motive := fun _ => Nat × Nat) (nat_lit 100000, nat_lit 0)
          (ih (Nat.succ k) (Nat.succ p))
          (Nat.beq (lget S (Nat.succ k)) (Nat.succ p)))
        (Nat.beq (chAt q.1 (Nat.sub q.2 (nat_lit 1))) (nat_lit 10)))
      (pieceV q)) CH

theorem noNL_sound {N : Nat} : ∀ {m : Nat}, noNL N m = true → ∀ k < m, chAt N k ≠ 10
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | m + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact noNL_sound h1 k hk
    · intro e
      rw [e] at h2
      exact absurd h2 (by decide)

theorem pieceV_noNL {q : Nat × Nat} (hv : pieceV q = true)
    (hn : Nat.beq (chAt q.1 (q.2 - 1)) 10 = false) : 10 ∉ pieceBytes q := by
  obtain ⟨h1, h⟩ := andB_true hv
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨h3, -⟩ := andB_true h
  have h1' := Nat.le_of_ble_eq_true h1
  intro hm
  obtain ⟨k, hk, e⟩ := List.mem_map.1 hm
  have hk' := List.mem_range.1 hk
  rcases Nat.lt_or_ge k (q.2 - 1) with hlt | hge
  · exact noNL_sound h3 k hlt e
  · have : k = q.2 - 1 := by omega
    rw [← this, e] at hn
    exact absurd hn (by decide)

theorem linesR_runs (S : List Nat) : ∀ (L : List (Nat × Nat)) (k p K : Nat), K ≠ 100000 →
    (linesR S L k p).1 = K → k ≤ K ∧
      (K = k → ∀ q ∈ L, 10 ∉ pieceBytes q) ∧
      (k < K → ∃ c, c < L.length ∧ lget S (k + 1) = p + c + 1 ∧
        (linesR S (L.drop (c + 1)) (k + 1) (p + c + 1)).1 = K ∧
        ∀ q ∈ L.take c, 10 ∉ pieceBytes q)
  | [], k, p, K, _, h => by
    change k = K at h
    subst h
    exact ⟨le_rfl, fun _ q hq => absurd hq (by simp), fun h => absurd h (lt_irrefl _)⟩
  | q :: L, k, p, K, hK, h => by
    change (Bool.rec (motive := fun _ => Nat × Nat) (100000, 0)
      (Bool.rec (motive := fun _ => Nat × Nat) (linesR S L k (Nat.succ p))
        (Bool.rec (motive := fun _ => Nat × Nat) (100000, 0)
          (linesR S L (Nat.succ k) (Nat.succ p))
          (Nat.beq (lget S (Nat.succ k)) (Nat.succ p)))
        (Nat.beq (chAt q.1 (Nat.sub q.2 1)) 10))
      (pieceV q)).1 = K at h
    cases hv : pieceV q
    · rw [hv] at h
      exact absurd h.symm hK
    rw [hv] at h
    cases hn : Nat.beq (chAt q.1 (Nat.sub q.2 1)) 10
    · rw [hn] at h
      obtain ⟨h1, h2, h3⟩ := linesR_runs S L k (p + 1) K hK h
      refine ⟨h1, fun hk q' hq' => ?_, fun hk => ?_⟩
      · rcases List.mem_cons.1 hq' with rfl | hq'
        · exact pieceV_noNL hv hn
        · exact h2 hk q' hq'
      · obtain ⟨c, hc, e1, e2, e3⟩ := h3 hk
        refine ⟨c + 1, by simp; omega, by rw [e1]; omega, ?_, fun q' hq' => ?_⟩
        · rw [List.drop_succ_cons, show p + (c + 1) + 1 = p + 1 + c + 1 by omega]
          exact e2
        · rw [List.take_succ_cons] at hq'
          rcases List.mem_cons.1 hq' with rfl | hq'
          · exact pieceV_noNL hv hn
          · exact e3 q' hq'
    · rw [hn] at h
      cases hs : Nat.beq (lget S (Nat.succ k)) (Nat.succ p)
      · rw [hs] at h
        exact absurd h.symm hK
      rw [hs] at h
      have h1 := (linesR_runs S L (k + 1) (p + 1) K hK h).1
      refine ⟨by omega, fun hk => absurd hk (by omega),
        fun _ => ⟨0, by simp, ?_, ?_, fun q' hq' => ?_⟩⟩
      · simpa using Nat.eq_of_beq_eq_true hs
      · exact h
      · simp at hq'

theorem linesAt_runs {CH : List (Nat × Nat)} {S : List Nat} (hS : linesAt CH S = true)
    (hn : lenL S = 49) :
    lget S 0 = 0 ∧ (∀ k < 48, lget S k < lget S (k + 1) ∧ lget S (k + 1) ≤ CH.length) ∧
      ∀ q ∈ CH.drop (lget S 48), 10 ∉ pieceBytes q := by
  obtain ⟨h0, h1⟩ := andB_true hS
  have h0' : lget S 0 = 0 := Nat.eq_of_beq_eq_true h0
  obtain ⟨h2, -⟩ := andB_true h1
  have h48 : (linesR S CH 0 0).1 = 48 := by
    have := Nat.eq_of_beq_eq_true h2
    rw [hn] at this
    exact this
  have P : ∀ k ≤ 48, (linesR S (CH.drop (lget S k)) k (lget S k)).1 = 48 ∧
      lget S k ≤ CH.length ∧ ∀ k' < k, lget S k' < lget S (k' + 1) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨by rw [h0']; exact h48, by rw [h0']; omega,
        fun k' hk' => absurd hk' (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨e1, e2, e3⟩ := ih (by omega)
      obtain ⟨-, -, h3⟩ := linesR_runs S _ k (lget S k) 48 (by decide) e1
      obtain ⟨c, hc, f1, f2, -⟩ := h3 (by omega)
      rw [List.length_drop] at hc
      rw [List.drop_drop] at f2
      refine ⟨?_, by omega, fun k' hk' => ?_⟩
      · rw [f1]
        rw [show lget S k + (c + 1) = lget S k + c + 1 by omega] at f2
        exact f2
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
        · exact e3 k' hk'
        · omega
  obtain ⟨e1, -, -⟩ := P 48 le_rfl
  refine ⟨h0', fun k hk => ⟨(P 48 le_rfl).2.2 k hk, (P (k + 1) (by omega)).2.1⟩, ?_⟩
  obtain ⟨-, h3, -⟩ := linesR_runs S _ 48 (lget S 48) 48 (by decide) e1
  exact h3 rfl

open CFSG.Monster.B.Native (b64Val numOfCode)

structure DS where
  gens : Array (Array (Array (Nat × Int)))
  rows : Array (Array (Nat × Int))
  row : Array (Nat × Int)
  acc : Nat
  cnt : Nat

@[expose] def stepD (st : DS) (c : UInt8) : DS :=
  if c == 10 then ⟨st.gens.push st.rows, #[], st.row, st.acc, st.cnt⟩
  else if st.cnt + 1 == 3 then
    if (st.acc * 64 + b64Val c) / 65536 == 1 then
      ⟨st.gens, st.rows.push (st.row.push ((st.acc * 64 + b64Val c) % 8192,
          numOfCode ((st.acc * 64 + b64Val c) / 8192 % 8))), #[], 0, 0⟩
    else
      ⟨st.gens, st.rows, st.row.push ((st.acc * 64 + b64Val c) % 8192,
          numOfCode ((st.acc * 64 + b64Val c) / 8192 % 8)), 0, 0⟩
  else ⟨st.gens, st.rows, st.row, st.acc * 64 + b64Val c, st.cnt + 1⟩

@[expose] def entStep (rr : Array (Array (Nat × Int)) × Array (Nat × Int)) (v : Nat) :
    Array (Array (Nat × Int)) × Array (Nat × Int) :=
  if v / 65536 = 1 then (rr.1.push (rr.2.push (v % 8192, numOfCode (v / 8192 % 8))), #[])
  else (rr.1, rr.2.push (v % 8192, numOfCode (v / 8192 % 8)))

@[expose] noncomputable def lineRows (p : Nat × Nat) : Array (Array (Nat × Int)) :=
  (((List.range (p.2 / 3)).map (entV p.1)).foldl entStep (#[], #[])).1

theorem dig_facts : ∀ c < 256, isDig c = true →
    (UInt8.ofNat c == 10) = false ∧ c < 128 ∧ b64Val (UInt8.ofNat c) = b64v c ∧ b64v c < 64 := by
  decide +kernel

theorem entV_facts {N i : Nat} (h : entV N i < 262144) :
    isDig (chAt N (3 * i)) = true ∧ isDig (chAt N (3 * i + 1)) = true ∧
      isDig (chAt N (3 * i + 2)) = true ∧
      entV N i = b64v (chAt N (3 * i)) * 4096 + b64v (chAt N (3 * i + 1)) * 64 +
        b64v (chAt N (3 * i + 2)) := by
  have e : entV N i = Bool.rec (motive := fun _ => Nat) 262144
      (b64v (chAt N (3 * i)) * 4096 + b64v (chAt N (3 * i + 1)) * 64 + b64v (chAt N (3 * i + 2)))
      (andB (isDig (chAt N (3 * i))) (andB (isDig (chAt N (3 * i + 1)))
        (isDig (chAt N (3 * i + 2))))) := rfl
  rw [e] at h ⊢
  cases hA : isDig (chAt N (3 * i))
  · rw [hA] at h
    exact absurd h (Nat.lt_irrefl _)
  cases hB : isDig (chAt N (3 * i + 1))
  · rw [hA, hB] at h
    exact absurd h (Nat.lt_irrefl _)
  cases hC : isDig (chAt N (3 * i + 2))
  · rw [hA, hB, hC] at h
    exact absurd h (Nat.lt_irrefl _)
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem step3 (G : Array (Array (Array (Nat × Int)))) (R : Array (Array (Nat × Int)))
    (r : Array (Nat × Int)) {a b c : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (hda : isDig a = true) (hdb : isDig b = true) (hdc : isDig c = true) :
    [UInt8.ofNat a, UInt8.ofNat b, UInt8.ofNat c].foldl stepD ⟨G, R, r, 0, 0⟩ =
      ⟨G, (entStep (R, r) (b64v a * 4096 + b64v b * 64 + b64v c)).1,
        (entStep (R, r) (b64v a * 4096 + b64v b * 64 + b64v c)).2, 0, 0⟩ := by
  obtain ⟨na, -, va, -⟩ := dig_facts a ha hda
  obtain ⟨nb, -, vb, -⟩ := dig_facts b hb hdb
  obtain ⟨nc, -, vc, -⟩ := dig_facts c hc hdc
  have s1 : stepD ⟨G, R, r, 0, 0⟩ (UInt8.ofNat a) = ⟨G, R, r, b64v a, 1⟩ := by
    simp [stepD, na, va]
  have s2 : stepD ⟨G, R, r, b64v a, 1⟩ (UInt8.ofNat b) = ⟨G, R, r, b64v a * 64 + b64v b, 2⟩ := by
    simp [stepD, nb, vb]
  have hv : (b64v a * 64 + b64v b) * 64 + b64Val (UInt8.ofNat c) =
      b64v a * 4096 + b64v b * 64 + b64v c := by
    rw [vc]
    omega
  have s3 : stepD ⟨G, R, r, b64v a * 64 + b64v b, 2⟩ (UInt8.ofNat c) =
      ⟨G, (entStep (R, r) (b64v a * 4096 + b64v b * 64 + b64v c)).1,
        (entStep (R, r) (b64v a * 4096 + b64v b * 64 + b64v c)).2, 0, 0⟩ := by
    unfold stepD
    rw [ite_eq_right (show ¬ ((UInt8.ofNat c == 10) = true) by rw [nc]; decide),
      ite_eq_left (show ((2 : Nat) + 1 == 3) = true by decide)]
    simp only [hv]
    unfold entStep
    by_cases hl : (b64v a * 4096 + b64v b * 64 + b64v c) / 65536 = 1 <;> simp [hl]
  rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil, s1, s2, s3]

theorem stepEntries (N : Nat) (G : Array (Array (Array (Nat × Int)))) : ∀ (e : Nat)
    (R : Array (Array (Nat × Int))) (r : Array (Nat × Int)), (∀ i < e, entV N i < 262144) →
    (((List.range (3 * e)).map (chAt N)).map UInt8.ofNat).foldl stepD ⟨G, R, r, 0, 0⟩ =
      ⟨G, (((List.range e).map (entV N)).foldl entStep (R, r)).1,
        (((List.range e).map (entV N)).foldl entStep (R, r)).2, 0, 0⟩
  | 0, R, r, _ => rfl
  | e + 1, R, r, h => by
    rw [show 3 * (e + 1) = 3 * e + 3 by omega, List.range_add, List.map_append, List.map_append,
      List.foldl_append, stepEntries N G e R r (fun i hi => h i (by omega))]
    obtain ⟨d1, d2, d3, ev⟩ := entV_facts (h e (by omega))
    have e3 : (((List.range 3).map (3 * e + ·)).map (chAt N)).map UInt8.ofNat =
        [UInt8.ofNat (chAt N (3 * e)), UInt8.ofNat (chAt N (3 * e + 1)),
          UInt8.ofNat (chAt N (3 * e + 2))] := rfl
    rw [e3, step3 G _ _ (chAt_lt N _) (chAt_lt N _) (chAt_lt N _) d1 d2 d3, ← ev,
      List.range_succ, List.map_append, List.foldl_append]
    rfl

theorem entStep_last {vs : List Nat} {v : Nat} (hv : v / 65536 = 1)
    (rr : Array (Array (Nat × Int)) × Array (Nat × Int)) :
    ((vs ++ [v]).foldl entStep rr).2 = #[] := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold entStep
  rw [ite_eq_left hv]

theorem lineOK_facts {p : Nat × Nat} (h : lineOK p = true) :
    0 < p.2 / 3 ∧ 3 * (p.2 / 3) + 1 = p.2 ∧ chAt p.1 (3 * (p.2 / 3)) = 10 ∧
      entV p.1 (p.2 / 3 - 1) / 65536 = 1 ∧ ∀ i < p.2 / 3, entV p.1 i < 262144 := by
  have e : lineOK p = andB (Nat.blt 0 (p.2 / 3)) (andB (Nat.beq (3 * (p.2 / 3) + 1) p.2)
      (andB (Nat.beq (chAt p.1 (3 * (p.2 / 3))) 10)
        (andB (Nat.beq (entV p.1 (p.2 / 3 - 1) / 65536) 1)
          (Nat.rec (motive := fun _ => Bool) true
            (fun i ih => andB ih (Nat.blt (entV p.1 i) 262144)) (p.2 / 3))))) := rfl
  rw [e] at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h⟩ := andB_true h
  obtain ⟨h4, h5⟩ := andB_true h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, fun i hi => Nat.le_of_ble_eq_true
      (@recAnd_sound (fun i => Nat.blt (entV p.1 i) 262144) _ h5 i hi)⟩

theorem lineOK_bytes {p : Nat × Nat} (h : lineOK p = true) : ∀ b ∈ pieceBytes p, b < 128 := by
  obtain ⟨-, h2, h3, -, h5⟩ := lineOK_facts h
  intro b hb
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hb
  have hk' := List.mem_range.1 hk
  rcases Nat.lt_or_ge k (3 * (p.2 / 3)) with hlt | hge
  · obtain ⟨d1, d2, d3, -⟩ := entV_facts (h5 (k / 3) (by omega))
    have hk3 : k = 3 * (k / 3) ∨ k = 3 * (k / 3) + 1 ∨ k = 3 * (k / 3) + 2 := by omega
    rcases hk3 with e | e | e
    · rw [e]
      exact (dig_facts _ (chAt_lt _ _) d1).2.1
    · rw [e]
      exact (dig_facts _ (chAt_lt _ _) d2).2.1
    · rw [e]
      exact (dig_facts _ (chAt_lt _ _) d3).2.1
  · rw [show k = 3 * (p.2 / 3) by omega, h3]
    decide

theorem line_step {p : Nat × Nat} (h : lineOK p = true) (G : Array (Array (Array (Nat × Int)))) :
    ((pieceBytes p).map UInt8.ofNat).foldl stepD ⟨G, #[], #[], 0, 0⟩ =
      ⟨G.push (lineRows p), #[], #[], 0, 0⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := lineOK_facts h
  have hr : (((List.range (p.2 / 3)).map (entV p.1)).foldl entStep (#[], #[])).2 = #[] := by
    have e : List.range (p.2 / 3) = List.range (p.2 / 3 - 1) ++ [p.2 / 3 - 1] := by
      rw [← List.range_succ, show Nat.succ (p.2 / 3 - 1) = p.2 / 3 by omega]
    rw [e, List.map_append, List.map_cons, List.map_nil]
    exact entStep_last h4 _
  unfold pieceBytes
  rw [← h2, List.range_succ, List.map_append, List.map_append, List.foldl_append,
    stepEntries p.1 G _ _ _ h5]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, h3, hr]
  simp [stepD, lineRows]

theorem foldl_gens : ∀ (L : List UInt8) (st : DS), (∀ c ∈ L, c ≠ 10) →
    (L.foldl stepD st).gens = st.gens
  | [], _, _ => rfl
  | c :: L, st, h => by
    rw [List.foldl_cons, foldl_gens L _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    have hc : (c == 10) = false := by
      have := h c (by simp)
      simpa using this
    unfold stepD
    rw [ite_eq_right (show ¬ ((c == 10) = true) by rw [hc]; decide)]
    split
    · split <;> rfl
    · rfl

@[expose] def DS.tup (st : DS) : Array (Array (Array (Nat × Int))) × Array (Array (Nat × Int)) ×
    Array (Nat × Int) × Nat × Nat := (st.gens, st.rows, st.row, st.acc, st.cnt)

@[expose] def DS.ofTup (s : Array (Array (Array (Nat × Int))) × Array (Array (Nat × Int)) ×
    Array (Nat × Int) × Nat × Nat) : DS := ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2⟩

theorem forIn_yield_foldl {σ : Type} (F : Nat → σ → Id (ForInStep σ)) (G : σ → Nat → σ)
    (hF : ∀ i s, F i s = ForInStep.yield (G s i)) :
    ∀ (l : List Nat) (s : σ), forIn l s F = (l.foldl G s : σ) := by
  have e : F = fun i s => pure (ForInStep.yield (G s i)) := funext fun i => funext fun s => hF i s
  subst e
  intro l s
  exact List.forIn_pure_yield_eq_foldl (m := Id) (fun i s => G s i) s

theorem foldl_tup (b : ByteArray) : ∀ (l : List Nat) (st : DS),
    l.foldl (fun s i => (stepD (DS.ofTup s) (b.get! i)).tup) st.tup =
      ((l.map b.get!).foldl stepD st).tup
  | [], _ => rfl
  | i :: l, st => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ← foldl_tup b l]
    rfl

theorem range_get! (b : ByteArray) : (List.range' 0 b.size).map b.get! = b.data.toList := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range', Array.getElem_toList]
    obtain ⟨d⟩ := b
    have hi : i < d.size := by simpa using h2
    change d[0 + 1 * i]! = d[i]
    rw [show 0 + 1 * i = i by omega]
    exact getElem!_pos d i hi

theorem decodeRows_eq (s : String) :
    CFSG.Monster.B.Native.decodeRows s =
      (s.toUTF8.data.toList.foldl stepD ⟨#[], #[], #[], 0, 0⟩).gens := by
  unfold CFSG.Monster.B.Native.decodeRows
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  rw [forIn_yield_foldl _ (fun st i => (stepD (DS.ofTup st) (s.toUTF8.get! i)).tup) ?h]
  · change (List.foldl _ (DS.tup ⟨#[], #[], #[], 0, 0⟩) _).1 = _
    rw [foldl_tup, show (Std.Legacy.Range.size [:s.toUTF8.size]) = s.toUTF8.size by simp,
      range_get!]
    rfl
  · intro i st
    obtain ⟨g, r, w, a, c⟩ := st
    simp only [DS.ofTup, DS.tup, stepD]
    by_cases h1 : (s.toUTF8.get! i == 10) = true <;> by_cases h2 : (c + 1 == 3) = true <;>
      by_cases h3 : ((a * 64 + CFSG.Monster.B.Native.b64Val (s.toUTF8.get! i)) / 65536 == 1) = true <;>
      simp only [h1, h2, h3, ↓reduceIte] <;> rfl

@[expose] def encB (b : Nat) : List UInt8 :=
  if b < 128 then [UInt8.ofNat b] else [UInt8.ofNat (b / 64 % 32 + 192), UInt8.ofNat (b % 64 + 128)]

theorem utf8_ofNat : ∀ b < 256, String.utf8EncodeChar (Char.ofNat b) = encB b := by
  decide +kernel

theorem encB_ne : ∀ b < 256, b ≠ 10 → ∀ x ∈ encB b, x ≠ 10 := by
  decide +kernel

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp),
      flatMap_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem text_bytes (CH : List (Nat × Nat)) :
    (String.ofList (charsOf CH)).toUTF8.data.toList = (bytesOf CH).flatMap encB := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode,
    List.toList_data_toByteArray, charsOf_eq, List.flatMap_map]
  apply flatMap_congr'
  intro b hb
  rw [bytesOf_eq] at hb
  obtain ⟨q, -, hq⟩ := List.mem_flatMap.1 hb
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hq
  exact utf8_ofNat _ (chAt_lt _ _)

theorem flatMap_encB {L : List Nat} (h : ∀ b ∈ L, b < 128) : L.flatMap encB = L.map UInt8.ofNat := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    rw [List.flatMap_cons, List.map_cons, ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]
    unfold encB
    rw [ite_eq_left (h b (by simp))]
    rfl

theorem decode_text {CH : List (Nat × Nat)} {S : List Nat} (hc : piecesOK CH = true)
    (hS : linesAt CH S = true) (hn : lenL S = 49) (hl : ∀ i < 48, lineOK (lineOf CH S i) = true) :
    (((String.ofList (charsOf CH)).toUTF8.data.toList).foldl stepD ⟨#[], #[], #[], 0, 0⟩).gens =
      ((List.range 48).map (fun i => lineRows (lineOf CH S i))).toArray := by
  obtain ⟨h0, hrun, htail⟩ := linesAt_runs hS hn
  have hsplit : ∀ k ≤ 48, (CH.take (lget S k)).flatMap pieceBytes =
      (List.range k).flatMap (fun i => pieceBytes (lineOf CH S i)) := by
    intro k
    induction k with
    | zero => intro _; rw [h0]; rfl
    | succ k ih =>
      intro hk
      obtain ⟨hlt, -⟩ := hrun k (by omega)
      rw [show lget S (k + 1) = lget S k + (lget S (k + 1) - lget S k) by omega, List.take_add,
        List.flatMap_append, ih (by omega), ← lineOf_bytes hc, List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
  have hlines : ∀ k ≤ 48, (((CH.take (lget S k)).flatMap pieceBytes).map UInt8.ofNat).foldl stepD
      ⟨#[], #[], #[], 0, 0⟩ = ⟨((List.range k).map (fun i => lineRows (lineOf CH S i))).toArray,
        #[], #[], 0, 0⟩ := by
    intro k
    induction k with
    | zero => intro _; rw [h0]; rfl
    | succ k ih =>
      intro hk
      obtain ⟨hlt, -⟩ := hrun k (by omega)
      rw [show lget S (k + 1) = lget S k + (lget S (k + 1) - lget S k) by omega, List.take_add,
        List.flatMap_append, List.map_append, List.foldl_append, ih (by omega), ← lineOf_bytes hc,
        line_step (hl k (by omega)), List.range_succ, List.map_append, List.push_toArray]
      rfl
  have hb : bytesOf CH = (CH.take (lget S 48)).flatMap pieceBytes ++
      (CH.drop (lget S 48)).flatMap pieceBytes := by
    rw [bytesOf_eq, ← List.flatMap_append, List.take_append_drop]
  rw [text_bytes, hb, List.flatMap_append, List.foldl_append]
  have hasc : ∀ b ∈ (CH.take (lget S 48)).flatMap pieceBytes, b < 128 := by
    rw [hsplit 48 le_rfl]
    intro b hb
    obtain ⟨i, hi, hb⟩ := List.mem_flatMap.1 hb
    exact lineOK_bytes (hl i (List.mem_range.1 hi)) b hb
  rw [flatMap_encB hasc, hlines 48 le_rfl, foldl_gens]
  intro x hx
  obtain ⟨b, hb, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨q, hq, hbq⟩ := List.mem_flatMap.1 hb
  refine encB_ne b ?_ ?_ x hx
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hbq
    exact chAt_lt _ _
  · intro e
    exact htail q hq (e ▸ hbq)

theorem getElem!_map_range {α : Type} [Inhabited α] (f : Nat → α) {n t : Nat} (h : t < n) :
    ((List.range n).map f)[t]! = f t := by
  rw [getElem!_pos ((List.range n).map f) t (by simp [h])]
  simp

theorem tfld_eq (T k : Nat) :
    Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 16) k)) (nat_lit 65535) = fld T k := by
  rw [land65535, fld_zero, fld]
  change T >>> (16 * k) % 65536 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem entStep_mono : ∀ (vs : List Nat) (R : Array (Array (Nat × Int))),
    (∀ v ∈ vs, v / 65536 = 1) →
    (vs.foldl entStep (R, #[])).1.toList =
      R.toList ++ vs.map (fun v => #[(v % 8192, numOfCode (v / 8192 % 8))])
  | [], R, _ => by simp
  | v :: vs, R, h => by
    rw [List.foldl_cons]
    have e : entStep (R, #[]) v = (R.push #[(v % 8192, numOfCode (v / 8192 % 8))], #[]) := by
      unfold entStep
      rw [ite_eq_left (h v (by simp))]
      rfl
    rw [e, entStep_mono vs _ (fun v' hv' => h v' (List.mem_cons_of_mem _ hv')), Array.toList_push,
      List.map_cons, List.append_assoc]
    rfl

theorem mono_rows {p : Nat × Nat} {T : Nat} (h : monoOK p T = true) {t : Nat} (ht : t < 4371) :
    (lineRows p)[t]! = #[(fld T t % 8192, numOfCode (fld T t / 8192))] := by
  unfold monoOK at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨-, h3⟩ := andB_true h
  have hk : ∀ k < 4371, entV p.1 k / 65536 = 1 ∧ entV p.1 k % 8192 = fld T k % 8192 ∧
      entV p.1 k / 8192 % 8 = fld T k / 8192 := by
    intro k hk
    have := @recAnd_sound (fun k => (fun v f => andB (Nat.beq (Nat.div v (nat_lit 65536)) (nat_lit 1))
          (andB (Nat.beq (Nat.mod v (nat_lit 8192)) (Nat.mod f (nat_lit 8192)))
            (Nat.beq (Nat.mod (Nat.div v (nat_lit 8192)) (nat_lit 8))
              (Nat.div f (nat_lit 8192)))))
        (entV p.1 k) (Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 16) k)) (nat_lit 65535)))
      (nat_lit 4371) h3 k hk
    simp only at this
    obtain ⟨a, b⟩ := andB_true this
    obtain ⟨b, c⟩ := andB_true b
    rw [tfld_eq] at b c
    exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c⟩
  have hp : p.2 / 3 = 4371 := by
    rw [Nat.eq_of_beq_eq_true h1]
  unfold lineRows
  rw [← Array.getElem!_toList, entStep_mono _ _ (fun v hv => by
      rw [hp] at hv
      obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hv
      exact (hk k (List.mem_range.1 hk')).1), hp, List.map_map]
  simp only [List.nil_append]
  rw [getElem!_map_range _ ht, Function.comp_apply, (hk t ht).2.1, (hk t ht).2.2]

@[expose] noncomputable def sstep (SG : List (List Nat)) (st : Nat × Nat) (v : Nat) : Nat × Nat :=
  (fun j c l => (fun f =>
      Bool.rec (motive := fun _ => Nat × Nat) (Nat.lor st.1 (nat_lit 8192), nat_lit 0)
        (Bool.rec (motive := fun _ => Nat × Nat) (st.1, f)
          (Bool.rec (motive := fun _ => Nat × Nat) (Nat.lor st.1 (nat_lit 8192), nat_lit 0)
            (Nat.succ st.1, nat_lit 0) (Nat.beq f (recOf SG st.1)))
          (Nat.beq l (nat_lit 1)))
        (andB (Nat.blt v (nat_lit 262144)) (andB (Nat.ble c (nat_lit 5))
          (Nat.beq (Nat.land (Nat.shiftRight st.2 (Nat.mul (nat_lit 16) j)) (nat_lit 65535))
            (nat_lit 0)))))
      (Nat.lor st.2 (Nat.shiftLeft (numCode c) (Nat.mul (nat_lit 16) j))))
    (Nat.mod v (nat_lit 8192)) (Nat.mod (Nat.div v (nat_lit 8192)) (nat_lit 8))
    (Nat.div v (nat_lit 65536))

theorem sparseRun_eq (SG : List (List Nat)) (N : Nat) : ∀ (n i : Nat) (st : Nat × Nat),
    sparseRun SG N i n st = ((List.range' i n).map (entV N)).foldl (sstep SG) st
  | 0, _, _ => rfl
  | n + 1, i, st => by
    change sparseRun SG N (i + 1) n (sstep SG st (entV N i)) = _
    rw [sparseRun_eq SG N n (i + 1), List.range'_succ]
    rfl

@[expose] noncomputable def chunkR (SG : List (List Nat)) (Ps : List Nat) :
    Nat → Nat × Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat → Nat × Nat) (fun _ st => st)
    (fun N _ ih m st => (fun c => (fun st' => forceP st'.1 (ih (Nat.sub m c) st'))
        (sparseRun SG N 0 c st))
      (Nat.min m (nat_lit 64))) Ps

theorem chunkR_eq (SG : List (List Nat)) : ∀ (Ps : List Nat) (g : Nat → Nat) (m : Nat)
    (st : Nat × Nat), (∀ k < Ps.length, ∀ i < 64, entV (Ps.getD k 0) i = g (64 * k + i)) →
    m ≤ 64 * Ps.length → chunkR SG Ps m st = ((List.range m).map g).foldl (sstep SG) st
  | [], g, m, st, _, hm => by
    rw [show m = 0 by simpa using hm]
    rfl
  | N :: Ps, g, m, st, hg, hm => by
    change forceP _ (chunkR SG Ps (m - min m 64) (sparseRun SG N 0 (min m 64) st)) = _
    rw [forceP_eq, sparseRun_eq, ← List.range_eq_range']
    have h0 : (List.range (min m 64)).map (entV N) = (List.range (min m 64)).map g :=
      List.map_congr_left (fun i hi => by
        have := hg 0 (by simp) i (by have := List.mem_range.1 hi; omega)
        simpa using this)
    rw [h0, chunkR_eq SG Ps (fun x => g (64 + x)) _ _ (fun k hk i hi => by
        have := hg (k + 1) (by simp; omega) i hi
        rw [List.getD_cons_succ] at this
        rw [this]
        congr 1
        omega) (by simp at hm; omega), ← List.foldl_append]
    congr 1
    by_cases hm64 : m ≤ 64
    · rw [Nat.min_eq_left hm64, Nat.sub_self]
      simp
    · rw [Nat.min_eq_right (by omega), show m = 64 + (m - 64) by omega, List.range_add,
        List.map_append, List.map_map, Nat.add_sub_cancel_left]
      rfl

theorem appN_eq : ∀ (L₁ L₂ : List Nat), appN L₁ L₂ = L₁ ++ L₂
  | [], _ => rfl
  | x :: L, L₂ => by
    change x :: appN L L₂ = _
    rw [appN_eq L L₂]
    rfl

theorem chAt_land_ones {N h j : Nat} (hj : j < h) :
    chAt (Nat.land N (ones (Nat.mul 8 h))) j = chAt N j := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [chAt_testBit, chAt_testBit]
  have e : ones (Nat.mul 8 h) = 2 ^ (8 * h) - 1 := by
    unfold ones
    rw [shl1]
    rfl
  change (decide (k < 8) && (N &&& ones (Nat.mul 8 h)).testBit (8 * j + k)) = _
  rw [e, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hk : k < 8
  · simp [hk, show 8 * j + k < 8 * h by omega]
  · simp [hk]

theorem chAt_shr {N h j : Nat} : chAt (Nat.shiftRight N (Nat.mul 8 h)) j = chAt N (h + j) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [chAt_testBit, chAt_testBit]
  change (decide (k < 8) && (N >>> (8 * h)).testBit (8 * j + k)) = _
  rw [Nat.testBit_shiftRight, show 8 * h + (8 * j + k) = 8 * (h + j) + k by omega]

theorem splitN_chars (k : Nat) : ∀ (d N : Nat), (splitN k d N).length = 2 ^ d ∧
    ∀ m < 2 ^ d, ∀ i < k, chAt ((splitN k d N).getD m 0) i = chAt N (k * m + i)
  | 0, N => ⟨rfl, fun m hm i _ => by
      rw [show m = 0 by simpa using hm]
      change chAt N i = chAt N (k * 0 + i)
      rw [Nat.mul_zero, Nat.zero_add]⟩
  | d + 1, N => by
    change (appN (splitN k d (Nat.land N (ones (Nat.mul 8 (Nat.mul k (Nat.shiftLeft 1 d))))))
      (splitN k d (Nat.shiftRight N (Nat.mul 8 (Nat.mul k (Nat.shiftLeft 1 d)))))).length = _ ∧
      ∀ m < 2 ^ (d + 1), ∀ i < k, chAt ((appN (splitN k d (Nat.land N (ones (Nat.mul 8
        (Nat.mul k (Nat.shiftLeft 1 d)))))) (splitN k d (Nat.shiftRight N (Nat.mul 8
          (Nat.mul k (Nat.shiftLeft 1 d)))))).getD m 0) i = chAt N (k * m + i)
    rw [appN_eq, shl1]
    obtain ⟨l1, c1⟩ := splitN_chars k d (Nat.land N (ones (Nat.mul 8 (Nat.mul k (2 ^ d)))))
    obtain ⟨l2, c2⟩ := splitN_chars k d (Nat.shiftRight N (Nat.mul 8 (Nat.mul k (2 ^ d))))
    refine ⟨by rw [List.length_append, l1, l2, Nat.pow_succ]; omega, fun m hm i hi => ?_⟩
    by_cases hm' : m < 2 ^ d
    · rw [getD_app_left _ _ (by rw [l1]; exact hm'), c1 m hm' i hi]
      apply chAt_land_ones
      have : k * (m + 1) ≤ k * 2 ^ d := Nat.mul_le_mul_left _ hm'
      change k * m + i < k * 2 ^ d
      rw [Nat.mul_succ] at this
      omega
    · rw [getD_app_right _ _ (by rw [l1]; omega), l1, c2 (m - 2 ^ d) (by rw [Nat.pow_succ] at hm; omega) i hi,
        chAt_shr]
      congr 1
      change k * 2 ^ d + (k * (m - 2 ^ d) + i) = k * m + i
      rw [← Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)]

@[expose] noncomputable def entF (a b c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 262144)
    (Nat.add (Nat.add (Nat.mul (b64v a) (nat_lit 4096)) (Nat.mul (b64v b) (nat_lit 64))) (b64v c))
    (andB (isDig a) (andB (isDig b) (isDig c)))

theorem entV_eq (N i : Nat) :
    entV N i = entF (chAt N (3 * i)) (chAt N (3 * i + 1)) (chAt N (3 * i + 2)) := rfl

theorem split_entV (N : Nat) : ∀ k < (splitN 192 12 N).length, ∀ i < 64,
    entV ((splitN 192 12 N).getD k 0) i = entV N (64 * k + i) := by
  obtain ⟨hl, hc⟩ := splitN_chars 192 12 N
  intro k hk i hi
  rw [hl] at hk
  rw [entV_eq, entV_eq, hc k hk _ (by omega), hc k hk _ (by omega), hc k hk _ (by omega)]
  congr 1 <;> congr 1 <;> omega

@[expose] def gF (x : Nat) : ℤ := if 1024 ≤ x then (x : ℤ) - 2048 else (x : ℤ)

@[expose] def sumAt (r : Array (Nat × Int)) (u : Nat) : ℤ :=
  r.foldl (fun s e => if e.1 = u then s + e.2 else s) 0

theorem sumAt_push (r : Array (Nat × Int)) (x : Nat × Int) (u : Nat) :
    sumAt (r.push x) u = sumAt r u + if x.1 = u then x.2 else 0 := by
  unfold sumAt
  rw [Array.foldl_push]
  split <;> simp

theorem getElem!_push {α : Type} [Inhabited α] (R : Array α) (x : α) (t : Nat) :
    (R.push x)[t]! = if t < R.size then R[t]! else if t = R.size then x else default := by
  by_cases h1 : t < R.size
  · rw [ite_eq_left h1, getElem!_pos (R.push x) t (by simp; omega), getElem!_pos R t h1,
      Array.getElem_push_lt h1]
  · by_cases h2 : t = R.size
    · subst h2
      rw [ite_eq_right h1, ite_eq_left rfl, getElem!_pos (R.push x) _ (by simp), Array.getElem_push_eq]
    · rw [ite_eq_right h1, ite_eq_right h2, getElem!_neg (R.push x) t (by simp; omega)]

theorem numCode_facts : ∀ c ≤ 5, gF (numCode c) = numOfCode c ∧ 0 < numCode c ∧
    numCode c < 2048 := by
  decide

theorem brec_cases {α : Type} (P : α → Prop) (a b : α) (c : Bool) (ha : P a) (hb : P b) :
    P (Bool.rec (motive := fun _ => α) a b c) := by
  cases c
  · exact ha
  · exact hb

theorem sstep_fail {SG : List (List Nat)} : ∀ (vs : List Nat) (st : Nat × Nat),
    st.1 ≤ (vs.foldl (sstep SG) st).1 ∧ (8192 ≤ st.1 → 8192 ≤ (vs.foldl (sstep SG) st).1)
  | [], st => ⟨le_rfl, id⟩
  | v :: vs, st => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := sstep_fail (SG := SG) vs (sstep SG st v)
    have hs : (sstep SG st v).1 = st.1 ||| 8192 ∨ (sstep SG st v).1 = st.1 ∨
        (sstep SG st v).1 = st.1 + 1 := by
      unfold sstep
      dsimp only
      let P := fun x : Nat × Nat => x.1 = st.1 ||| 8192 ∨ x.1 = st.1 ∨ x.1 = st.1 + 1
      exact brec_cases P _ _ _ (Or.inl rfl) (brec_cases P _ _ _ (Or.inr (Or.inl rfl))
          (brec_cases P _ _ _ (Or.inl rfl) (Or.inr (Or.inr rfl))))
    have l1 : st.1 ≤ st.1 ||| 8192 := Nat.left_le_or
    have l2 : 8192 ≤ st.1 ||| 8192 := Nat.right_le_or
    refine ⟨?_, fun h => ?_⟩
    · rcases hs with a | a | a <;> omega
    · rcases hs with a | a | a <;> apply h2 <;> omega

theorem sparse_rows {SG : List (List Nat)} : ∀ (vs : List Nat) (k F : Nat)
    (R : Array (Array (Nat × Int))) (r : Array (Nat × Int)),
    R.size = k → (∀ u, sumAt r u = gF (fld F u)) →
    (∀ t < k, ∀ u, sumAt (R[t]!) u = gF (fld (recOf SG t) u)) →
    (vs.foldl (sstep SG) (k, F)).1 = 4371 →
    ∀ t < 4371, ∀ u, sumAt ((vs.foldl entStep (R, r)).1[t]!) u = gF (fld (recOf SG t) u)
  | [], k, F, R, r, hR, _, hrows, hfin => by
    change k = 4371 at hfin
    subst hfin
    exact hrows
  | v :: vs, k, F, R, r, hR, hinv, hrows, hfin => by
    rw [List.foldl_cons] at hfin ⊢
    have hor : 8192 ≤ k ||| 8192 := Nat.right_le_or
    have hfail : ∀ x, 8192 ≤ x → (vs.foldl (sstep SG) (x, 0)).1 ≠ 4371 := fun x hx h => by
      have := (sstep_fail (SG := SG) vs (x, 0)).2 hx
      omega
    have e : sstep SG (k, F) v = Bool.rec (motive := fun _ => Nat × Nat) (Nat.lor k 8192, 0)
        (Bool.rec (motive := fun _ => Nat × Nat)
          (k, Nat.lor F (Nat.shiftLeft (numCode (v / 8192 % 8)) (Nat.mul 16 (v % 8192))))
          (Bool.rec (motive := fun _ => Nat × Nat) (Nat.lor k 8192, 0) (Nat.succ k, 0)
            (Nat.beq (Nat.lor F (Nat.shiftLeft (numCode (v / 8192 % 8)) (Nat.mul 16 (v % 8192))))
              (recOf SG k)))
          (Nat.beq (v / 65536) 1))
        (andB (Nat.blt v 262144) (andB (Nat.ble (v / 8192 % 8) 5)
          (Nat.beq (Nat.land (Nat.shiftRight F (Nat.mul 16 (v % 8192))) 65535) 0))) := rfl
    rw [e] at hfin
    cases hcond : andB (Nat.blt v 262144) (andB (Nat.ble (v / 8192 % 8) 5)
        (Nat.beq (Nat.land (Nat.shiftRight F (Nat.mul 16 (v % 8192))) 65535) 0))
    · rw [hcond] at hfin
      exact absurd hfin (hfail _ hor)
    rw [hcond] at hfin
    obtain ⟨-, hcond'⟩ := andB_true hcond
    obtain ⟨hc5, hfree⟩ := andB_true hcond'
    have hc5' : v / 8192 % 8 ≤ 5 := Nat.le_of_ble_eq_true hc5
    have hfree' : fld F (v % 8192) = 0 := by
      rw [← tfld_eq]
      exact Nat.eq_of_beq_eq_true hfree
    obtain ⟨hg, -, hlt⟩ := numCode_facts _ hc5'
    have hfu : ∀ u, fld (Nat.lor F (Nat.shiftLeft (numCode (v / 8192 % 8)) (Nat.mul 16 (v % 8192))))
        u = if u = v % 8192 then numCode (v / 8192 % 8) else fld F u := fun u => by
      change fld (F ||| (numCode (v / 8192 % 8) <<< (16 * (v % 8192)))) u = _
      rw [fld_lor, fld_shl16, fld_small (c := numCode (v / 8192 % 8)) (by omega)]
      by_cases h1 : u < v % 8192
      · simp [h1, show u ≠ v % 8192 by omega]
      · by_cases h2 : u = v % 8192
        · subst h2
          simp [hfree']
        · simp [h1, h2, show u - v % 8192 ≠ 0 by omega]
    have hinv' : ∀ u, sumAt (r.push (v % 8192, numOfCode (v / 8192 % 8))) u =
        gF (fld (Nat.lor F (Nat.shiftLeft (numCode (v / 8192 % 8)) (Nat.mul 16 (v % 8192)))) u) :=
      fun u => by
        rw [sumAt_push, hinv, hfu]
        by_cases hu : u = v % 8192
        · rw [ite_eq_left hu, ite_eq_left hu.symm, hu, hfree', hg]
          simp [gF]
        · rw [ite_eq_right hu, ite_eq_right (Ne.symm hu), add_zero]
    cases hl : Nat.beq (v / 65536) 1
    · rw [hl] at hfin
      have hent : entStep (R, r) v = (R, r.push (v % 8192, numOfCode (v / 8192 % 8))) := by
        unfold entStep
        rw [ite_eq_right (fun h => by rw [h] at hl; exact absurd hl (by decide))]
      rw [hent]
      exact sparse_rows vs k _ R _ hR hinv' hrows hfin
    · rw [hl] at hfin
      cases hrec : Nat.beq (Nat.lor F (Nat.shiftLeft (numCode (v / 8192 % 8)) (Nat.mul 16 (v % 8192))))
          (recOf SG k)
      · rw [hrec] at hfin
        exact absurd hfin (hfail _ hor)
      rw [hrec] at hfin
      have hent : entStep (R, r) v =
          (R.push (r.push (v % 8192, numOfCode (v / 8192 % 8))), #[]) := by
        unfold entStep
        rw [ite_eq_left (Nat.eq_of_beq_eq_true hl)]
      rw [hent]
      refine sparse_rows vs (k + 1) 0 _ #[] (by simp [hR]) (fun u => by simp [sumAt, gF, fld])
        (fun t ht u => ?_) hfin
      rw [getElem!_push]
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · rw [ite_eq_left (by omega)]
        exact hrows t ht u
      · rw [ite_eq_right (by omega), ite_eq_left hR.symm, hinv', Nat.eq_of_beq_eq_true hrec]

end CFSG.KC.BM.Pkt

end
