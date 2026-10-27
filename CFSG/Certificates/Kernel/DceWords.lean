module

public import CFSG.Certificates.Kernel.Th.Words
public import CFSG.Certificates.Kernel.DceLoops
public import CFSG.Certificates.Kernel.CosetBoundsLemmas
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.DceWord

open CFSG.Certificates.KB.Sound CFSG.Certificates.DceLoop

variable {G : Type*} [Group G]

@[expose] noncomputable def wv (f : ℕ → G) (W n : ℕ) : G :=
  ((List.range n).map fun i => f (byteG W i)).prod

@[expose] noncomputable def lvE (f : ℕ → G) (c : ℕ) : G := if c = 255 then 1 else f c

theorem byteG_eq (W i : ℕ) : byteG W i = CFSG.Certificates.KB.byte W i := by
  rw [byte_eq']
  unfold byteG
  change (W >>> (8 * i)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem wLet_eq (W i : ℕ) : CFSG.KC.Th.wLet W i = CFSG.Certificates.KB.byte W i := byteG_eq W i

theorem wv_eq (f : ℕ → G) (W n : ℕ) : wv f W n = lv f (bytes W n) := by
  unfold wv lv bytes
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by simp [byteG_eq]

theorem wv_succ (f : ℕ → G) (W n : ℕ) : wv f W (n + 1) = wv f W n * f (byteG W n) := by
  unfold wv
  rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

theorem wv_split (f : ℕ → G) (W o m : ℕ) :
    wv f W (o + m) = wv f W o * ((List.range m).map fun k => f (byteG W (o + k))).prod := by
  unfold wv
  rw [List.range_add, List.map_append, List.prod_append, List.map_map]
  rfl

theorem pkb_bytes_mod (W : ℕ) : ∀ n, pkb 256 (bytes W n) = W % 256 ^ n
  | 0 => by simp [bytes, pkb, Nat.mod_one]
  | n + 1 => by
    rw [bytes_succ, pkb_append, pkb_bytes_mod W n, bytes_length, pkb_cons, pkb_nil, byte_eq',
      Nat.mod_pow_succ]
    ring

theorem pkb_bytes {W n : ℕ} (h : W < 256 ^ n) : pkb 256 (bytes W n) = W := by
  rw [pkb_bytes_mod, Nat.mod_eq_of_lt h]

theorem bytes_lt_of_mem {l : List ℕ} {W n : ℕ} (h : l = bytes W n) : ∀ d ∈ l, d < 256 := by
  subst h
  exact bytes_lt W n

theorem rot_eq (r n s : ℕ) : CFSG.KC.Th.rot r n s = CFSG.Certificates.KB.rot r n s := by
  unfold CFSG.KC.Th.rot CFSG.Certificates.KB.rot
  have h1 : Nat.shiftLeft s (nat_lit 3) = Nat.mul (nat_lit 8) s := by
    change s <<< 3 = 8 * s
    rw [Nat.shiftLeft_eq]
    ring
  have h2 : Nat.shiftLeft (Nat.sub n s) (nat_lit 3) = Nat.mul (nat_lit 8) (Nat.sub n s) := by
    change (n - s) <<< 3 = 8 * (n - s)
    rw [Nat.shiftLeft_eq]
    ring
  rw [h1, h2]

theorem bytes_rot {r n : ℕ} (hr : r < 256 ^ n) (s : ℕ) :
    bytes (CFSG.KC.Th.rot r n s) n = (bytes r n).drop s ++ (bytes r n).take s := by
  have hl := bytes_length r n
  have h256 := bytes_lt r n
  rw [rot_eq]
  have e0 : CFSG.Certificates.KB.rot r n s =
      pkb 256 ((bytes r n).drop s ++ (bytes r n).take s) := by
    have := rot_pkb (bytes r n) h256 s
    rwa [pkb_bytes hr, hl] at this
  rw [e0]
  have e := bytes_pkb ((bytes r n).drop s ++ (bytes r n).take s) (fun d hd => by
    rcases List.mem_append.1 hd with h | h
    · exact h256 d (List.mem_of_mem_drop h)
    · exact h256 d (List.mem_of_mem_take h))
  have hl2 : ((bytes r n).drop s ++ (bytes r n).take s).length = n := by
    rw [List.length_append, List.length_drop, List.length_take, hl]
    omega
  rw [hl2] at e
  exact e

theorem isRot_spec {r n w : ℕ} (h : CFSG.KC.Th.isRot r n w = true) :
    ∃ s < n, CFSG.KC.Th.rot r n s = w := by
  have key : ∀ k, Nat.rec (motive := fun _ => Bool) false
      (fun s acc => CFSG.KC.Th.orB acc (Nat.beq (CFSG.KC.Th.rot r n s) w)) k = true →
      ∃ s < k, CFSG.KC.Th.rot r n s = w := by
    intro k
    induction k with
    | zero => exact fun h => absurd h Bool.false_ne_true
    | succ k ih =>
      intro h
      change CFSG.KC.Th.orB _ _ = true at h
      unfold CFSG.KC.Th.orB at h
      rw [bor_iff] at h
      rcases h with h | h
      · obtain ⟨s, hs, e⟩ := ih h
        exact ⟨s, by omega, e⟩
      · exact ⟨k, by omega, Nat.eq_of_beq_eq_true h⟩
  exact key n h

theorem wv_rot (f : ℕ → G) {r n : ℕ} (hr : r < 256 ^ n) (h1 : wv f r n = 1) (s : ℕ) :
    wv f (CFSG.KC.Th.rot r n s) n = 1 := by
  rw [wv_eq] at h1 ⊢
  rw [bytes_rot hr]
  exact lv_rotate f _ s h1

theorem lor_mul (v b m : ℕ) (hv : v < 256 ^ m) :
    Nat.lor v (Nat.shiftLeft b (Nat.mul (nat_lit 8) m)) = v + 256 ^ m * b := by
  change v ||| b <<< (8 * m) = _
  rw [← two_pow_eight_mul] at hv ⊢
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hv, Nat.shiftLeft_eq]
  ring

theorem strip_spec (w : ℕ) : ∀ n, CFSG.KC.Th.strip w n =
    (pkb 256 ((bytes w n).filter (· ≠ 255)), ((bytes w n).filter (· ≠ 255)).length)
  | 0 => rfl
  | n + 1 => by
    change Prod.rec (motive := fun _ => ℕ × ℕ) (fun v m =>
      Bool.rec (Prod.mk (Nat.lor v (Nat.shiftLeft (CFSG.KC.Th.wLet w n) (Nat.mul (nat_lit 8) m)))
        (Nat.succ m)) (Prod.mk v m) (Nat.beq (CFSG.KC.Th.wLet w n) (nat_lit 255)))
      (CFSG.KC.Th.strip w n) = _
    rw [strip_spec w n, bytes_succ, List.filter_append, wLet_eq]
    cases h : Nat.beq (CFSG.Certificates.KB.byte w n) 255
    · have hne : CFSG.Certificates.KB.byte w n ≠ 255 := Nat.ne_of_beq_eq_false h
      have hf : [CFSG.Certificates.KB.byte w n].filter (· ≠ 255) = [CFSG.Certificates.KB.byte w n] := by
        simp [hne]
      rw [hf]
      have hlt := pkb_lt (B := 256) (l := (bytes w n).filter (· ≠ 255))
        (fun d hd => bytes_lt w n d (List.mem_of_mem_filter hd))
      change (Nat.lor _ _, _) = _
      rw [lor_mul _ _ _ hlt, pkb_append, pkb_cons, pkb_nil, List.length_append]
      simp
    · have heq : CFSG.Certificates.KB.byte w n = 255 := Nat.eq_of_beq_eq_true h
      have hf : [CFSG.Certificates.KB.byte w n].filter (· ≠ 255) = [] := by simp [heq]
      rw [hf, List.append_nil]

theorem thAnd_iff {a b : Bool} : CFSG.KC.Th.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem freeRed_stack (f : ℕ → G) (inv w N : ℕ)
    (hinv : ∀ q < N, CFSG.Certificates.KB.byte w q ≠ 255 →
      f (CFSG.Certificates.KB.byte inv (CFSG.Certificates.KB.byte w q)) =
        (f (CFSG.Certificates.KB.byte w q))⁻¹) :
    ∀ n ≤ N, ∃ st : List ℕ, CFSG.KC.Th.freeRed inv w n = pkb 256 (st.map (· + 1)) ∧
      (∀ d ∈ st, d < 255) ∧ lv (lvE f) (bytes w n) = lv f st.reverse := by
  intro n hn
  induction n with
  | zero => exact ⟨[], rfl, by simp, rfl⟩
  | succ n ih =>
    obtain ⟨st, hst, hlt, hv⟩ := ih (by omega)
    have hnN : n < N := by omega
    change ∃ st : List ℕ, Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ)
        (Nat.add (Nat.mul (CFSG.KC.Th.freeRed inv w n) (nat_lit 256)) (Nat.succ (CFSG.KC.Th.wLet w n)))
        (Nat.shiftRight (CFSG.KC.Th.freeRed inv w n) (nat_lit 8))
        (CFSG.KC.Th.andB (Nat.blt (nat_lit 0) (CFSG.KC.Th.freeRed inv w n))
          (Nat.beq (Nat.land (CFSG.KC.Th.freeRed inv w n) (nat_lit 255))
            (Nat.succ (CFSG.KC.Th.lInv inv (CFSG.KC.Th.wLet w n))))))
      (CFSG.KC.Th.freeRed inv w n) (Nat.beq (CFSG.KC.Th.wLet w n) (nat_lit 255)) =
        pkb 256 (st.map (· + 1)) ∧ (∀ d ∈ st, d < 255) ∧ lv (lvE f) (bytes w (n + 1)) = lv f st.reverse
    have hli : CFSG.KC.Th.lInv inv (CFSG.KC.Th.wLet w n) =
        CFSG.Certificates.KB.byte inv (CFSG.Certificates.KB.byte w n) := by
      unfold CFSG.KC.Th.lInv
      rw [wLet_eq, wLet_eq]
    rw [hli, wLet_eq]
    set c := CFSG.Certificates.KB.byte w n with hcdef
    have hc256 : c < 256 := byte_lt w n
    cases hb : Nat.beq c 255
    · have hne : c ≠ 255 := Nat.ne_of_beq_eq_false hb
      have hlv : lv (lvE f) (bytes w (n + 1)) = lv (lvE f) (bytes w n) * f c := by
        rw [bytes_succ, lv_append, lv_singleton, lvE, ite_eq_right hne]
      dsimp only
      cases hcnd : CFSG.KC.Th.andB (Nat.blt (nat_lit 0) (CFSG.KC.Th.freeRed inv w n))
          (Nat.beq (Nat.land (CFSG.KC.Th.freeRed inv w n) (nat_lit 255))
            (Nat.succ (CFSG.Certificates.KB.byte inv c)))
      · refine ⟨c :: st, ?_, ?_, ?_⟩
        · change CFSG.KC.Th.freeRed inv w n * 256 + (c + 1) = _
          rw [hst, List.map_cons, pkb_cons]
          ring
        · intro d hd
          rcases List.mem_cons.1 hd with rfl | hd
          · omega
          · exact hlt d hd
        · rw [hlv, hv, List.reverse_cons, lv_append, lv_singleton]
      · obtain ⟨h1, h2⟩ := thAnd_iff.1 hcnd
        have h1' : 0 < CFSG.KC.Th.freeRed inv w n := Nat.blt_eq.mp h1
        have h2' : CFSG.KC.Th.freeRed inv w n % 256 = CFSG.Certificates.KB.byte inv c + 1 := by
          have := Nat.eq_of_beq_eq_true h2
          change CFSG.KC.Th.freeRed inv w n &&& (2 ^ 8 - 1) = _ at this
          rwa [Nat.and_two_pow_sub_one_eq_mod] at this
        cases st with
        | nil =>
          rw [hst] at h1'
          simp [pkb] at h1'
        | cons h t =>
          have hh : h < 255 := hlt h (by simp)
          rw [hst, List.map_cons, pkb_cons, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (by omega)] at h2'
          refine ⟨t, ?_, fun d hd => hlt d (by simp [hd]), ?_⟩
          · change CFSG.KC.Th.freeRed inv w n >>> 8 = _
            rw [Nat.shiftRight_eq_div_pow, hst, List.map_cons, pkb_cons]
            omega
          · have hh' : h = CFSG.Certificates.KB.byte inv c := by omega
            rw [hlv, hv, List.reverse_cons, lv_append, lv_singleton, hh', hinv n hnN hne, mul_assoc,
              inv_mul_cancel, mul_one]
    · have heq : c = 255 := Nat.eq_of_beq_eq_true hb
      dsimp only
      refine ⟨st, hst, hlt, ?_⟩
      rw [bytes_succ, lv_append, lv_singleton, lvE, ite_eq_left heq, mul_one, hv]

theorem chkWord_sound (f : ℕ → G) {inv w n r m : ℕ} (hr : r < 256 ^ m) (hr1 : wv f r m = 1)
    (hinv : ∀ q < n, byteG w q ≠ 255 → f (byteG inv (byteG w q)) = (f (byteG w q))⁻¹)
    (h : CFSG.KC.Th.chkWord inv w n r m = true) : wv (lvE f) w n = 1 := by
  unfold CFSG.KC.Th.chkWord CFSG.KC.Th.orB at h
  rw [bor_iff] at h
  rcases h with h | h
  · unfold CFSG.KC.Th.freeTriv at h
    obtain ⟨st, hst, -, hv⟩ := freeRed_stack f inv w n (fun q hq hne => by
      rw [← byteG_eq, ← byteG_eq] at *
      exact hinv q hq hne) n le_rfl
    rw [Nat.eq_of_beq_eq_true h] at hst
    have := pkb_eq_zero (B := 256) (l := st.map (· + 1)) (by simp) hst.symm
    rw [List.map_eq_nil_iff] at this
    rw [wv_eq, hv, this]
    rfl
  · unfold CFSG.KC.Th.isRelRot at h
    rw [strip_spec] at h
    change CFSG.KC.Th.andB _ _ = true at h
    obtain ⟨h1, h2⟩ := thAnd_iff.1 h
    obtain ⟨s, -, hs⟩ := isRot_spec h2
    set l := (bytes w n).filter (· ≠ 255)
    have hm : l.length = m := Nat.eq_of_beq_eq_true h1
    have hl256 : ∀ d ∈ l, d < 256 := fun d hd => bytes_lt w n d (List.mem_of_mem_filter hd)
    have e1 : bytes (pkb 256 l) m = l := by
      rw [← hm]
      exact bytes_pkb l hl256
    have hrot := wv_rot f hr hr1 s
    rw [hs, wv_eq, e1] at hrot
    rw [wv_eq, ← lv_filter (lvE f) 255 (by simp [lvE])]
    rw [← hrot]
    unfold lv
    congr 1
    refine List.map_congr_left fun d hd => ?_
    have : d ≠ 255 := by simpa using (List.mem_filter.1 hd).2
    simp [lvE, this]

@[expose] noncomputable def wiRec (inv w n k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (CFSG.KC.Th.lInv inv (CFSG.KC.Th.wLet w i))
      (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub n i) (nat_lit 1))))) k

theorem lInv_lt (inv c : ℕ) : CFSG.KC.Th.lInv inv c < 256 := by
  unfold CFSG.KC.Th.lInv
  rw [wLet_eq]
  exact byte_lt inv c

theorem lor_disj (X c e : ℕ) (hc : c < 256) :
    256 ^ (e + 1) * X ||| c <<< (8 * e) = 256 ^ e * (c + 256 * X) := by
  have e1 : 256 ^ (e + 1) * X = (X <<< 8) <<< (8 * e) := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, two_pow_eight_mul]
    ring
  have hc' : c < 2 ^ 8 := by norm_num; omega
  rw [e1, ← Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add_eq_or_of_lt hc', Nat.shiftLeft_eq,
    Nat.shiftLeft_eq, two_pow_eight_mul]
  ring

theorem wiRec_eq (inv w n : ℕ) : ∀ k ≤ n, wiRec inv w n k =
    256 ^ (n - k) * pkb 256 ((bytes w k).reverse.map (CFSG.KC.Th.lInv inv))
  | 0, _ => by simp [wiRec, bytes, pkb]
  | k + 1, hk => by
    change Nat.lor (wiRec inv w n k) (Nat.shiftLeft (CFSG.KC.Th.lInv inv (CFSG.KC.Th.wLet w k))
      (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub n k) (nat_lit 1)))) = _
    rw [wiRec_eq inv w n k (by omega), bytes_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, pkb_cons, wLet_eq]
    have e1 : n - k = (n - (k + 1)) + 1 := by omega
    change 256 ^ (n - k) * _ ||| _ <<< (8 * (n - k - 1)) = _
    rw [show n - k - 1 = n - (k + 1) by omega, e1]
    exact lor_disj _ _ _ (lInv_lt _ _)

theorem wInv_eq (inv w n : ℕ) :
    CFSG.KC.Th.wInv inv w n = pkb 256 ((bytes w n).reverse.map (CFSG.KC.Th.lInv inv)) := by
  have := wiRec_eq inv w n n le_rfl
  rw [Nat.sub_self, pow_zero, one_mul] at this
  exact this

theorem wCat_eq (a na b : ℕ) (ha : a < 256 ^ na) : CFSG.KC.Th.wCat a na b = a + 256 ^ na * b :=
  lor_mul a b na ha

theorem lInv_eq (inv c : ℕ) : CFSG.KC.Th.lInv inv c = byteG inv c := by
  unfold CFSG.KC.Th.lInv
  rw [wLet_eq, byteG_eq]

theorem bytes_of_pkb {l : List ℕ} (h : ∀ d ∈ l, d < 256) {n : ℕ} (hn : l.length = n) :
    bytes (pkb 256 l) n = l := by
  rw [← hn]
  exact bytes_pkb l h

theorem wInv_lt (inv w n : ℕ) : CFSG.KC.Th.wInv inv w n < 256 ^ n := by
  rw [wInv_eq]
  have := pkb_lt (B := 256) (l := (bytes w n).reverse.map (CFSG.KC.Th.lInv inv)) (fun d hd => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hd
    exact lInv_lt inv c)
  simpa [bytes_length] using this

theorem wv_wInv (f : ℕ → G) (inv w n : ℕ)
    (hinv : ∀ q < n, f (byteG inv (byteG w q)) = (f (byteG w q))⁻¹) :
    wv f (CFSG.KC.Th.wInv inv w n) n = (wv f w n)⁻¹ := by
  have hl : ∀ c ∈ bytes w n, f (CFSG.KC.Th.lInv inv c) = (f c)⁻¹ := by
    intro c hc
    obtain ⟨q, hq, rfl⟩ := mem_bytes.1 hc
    rw [lInv_eq, ← byteG_eq]
    exact hinv q hq
  have h256 : ∀ d ∈ (bytes w n).reverse.map (CFSG.KC.Th.lInv inv), d < 256 := by
    intro d hd
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hd
    exact lInv_lt inv c
  have hlen : ((bytes w n).reverse.map (CFSG.KC.Th.lInv inv)).length = n := by
    simp [bytes_length]
  rw [wInv_eq, wv_eq, wv_eq, bytes_of_pkb h256 hlen]
  unfold lv
  rw [List.prod_inv_reverse]
  simp only [List.map_map, List.map_reverse]
  congr 2
  refine List.map_congr_left fun c hc => ?_
  simp only [Function.comp_apply]
  exact hl c hc

theorem wv_wCat (f : ℕ → G) {a na b nb : ℕ} (ha : a < 256 ^ na) (hb : b < 256 ^ nb) :
    wv f (CFSG.KC.Th.wCat a na b) (na + nb) = wv f a na * wv f b nb := by
  have e : a + 256 ^ na * b = pkb 256 (bytes a na ++ bytes b nb) := by
    rw [pkb_append, bytes_length, pkb_bytes ha, pkb_bytes hb]
  have h256 : ∀ d ∈ bytes a na ++ bytes b nb, d < 256 := fun d hd => by
    rcases List.mem_append.1 hd with h | h
    · exact bytes_lt a na d h
    · exact bytes_lt b nb d h
  rw [wCat_eq a na b ha, wv_eq, e, bytes_of_pkb h256 (by simp [bytes_length]), lv_append, wv_eq,
    wv_eq]

end CFSG.Certificates.DceWord

end
