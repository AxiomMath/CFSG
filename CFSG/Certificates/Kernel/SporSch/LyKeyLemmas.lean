module

public import Certificates.Data.Kernel.SporSch.LyKey
public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CFSG.KS.SporSch.LyK

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.SporSch.LyM
open CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native

@[expose] def redV (ech : Array (Array Nat)) (lead : Array Nat) (v : Array Nat) : Array Nat :=
  (List.range ech.size).foldl (fun b a => if (b[lead[a]!]! != 0) = true then
    Array.ofFn (n := 7) fun k => (b[k.val]! + (5 - b[lead[a]!]!) * (ech[a]!)[k.val]!) % 5 else b) v

@[expose] def firstNZ (v : Array Nat) : Nat :=
  (List.range 7).foldl (fun b a => if (b == 7 && v[a]! != 0) = true then a else b) 7

@[expose] def pvStep (ds : Array ByteArray) (s : Array (Array Nat) × Array Nat × Array Nat)
    (i : Nat) : Array (Array Nat) × Array Nat × Array Nat :=
  if s.2.2.size < 7 then
    if firstNZ (redV s.1 s.2.1 (Array.ofFn (n := 7) fun k => (ds[k.val]!.get! i).toNat)) < 7 then
      (s.1.push ((redV s.1 s.2.1 (Array.ofFn (n := 7) fun k => (ds[k.val]!.get! i).toNat)).map
          fun x => x * inv5 ((redV s.1 s.2.1 (Array.ofFn (n := 7) fun k =>
            (ds[k.val]!.get! i).toNat))[firstNZ (redV s.1 s.2.1 (Array.ofFn (n := 7) fun k =>
              (ds[k.val]!.get! i).toNat))]!) % 5),
        s.2.1.push (firstNZ (redV s.1 s.2.1 (Array.ofFn (n := 7) fun k => (ds[k.val]!.get! i).toNat))),
        s.2.2.push i)
    else s
  else s

@[expose] def pivotsF (ds : Array ByteArray) : Array Nat :=
  ((List.range 111).foldl (pvStep ds) (#[], #[], #[])).2.2

theorem forIn_yield_done {α β : Type} (l : List α) (c : β → Prop) [DecidablePred c]
    (g : α → β → β) (init : β) :
    forIn (m := Id) l init (fun a s => if c s then pure (ForInStep.yield (g a s))
      else pure (ForInStep.done s)) = pure (l.foldl (fun s a => if c s then g a s else s) init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, List.foldl_cons]
    by_cases h : c init
    · simp only [ite_eq_left h]
      exact ih _
    · simp only [ite_eq_right h]
      clear ih
      induction l with
      | nil => rfl
      | cons b l ih2 =>
        rw [List.foldl_cons, ite_eq_right h]
        exact ih2

theorem pivots_eq (ds : Array ByteArray) : pivots ds = pivotsF ds := by
  unfold pivots
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yieldL,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  have h1 : ∀ a b : Nat, [a:b].size = b - a := fun a b => by simp [Std.Legacy.Range.size]
  simp only [h1, Nat.sub_zero, ← List.range_eq_range']
  rw [forIn_yield_done]
  simp only [pure_bind]
  unfold pivotsF
  change (List.foldl _ (#[], #[], #[]) (List.range 111)).2.2 = _
  congr 2

@[expose] def hB (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => c 0 + 256 * hB (fun l => c (l + 1)) n

theorem hB_lt {c : Nat → Nat} : ∀ {n}, (∀ l < n, c l < 256) → hB c n < 256 ^ n := by
  intro n
  induction n generalizing c with
  | zero => intro _; simp [hB]
  | succ n ih =>
    intro h
    have h1 := ih (c := fun l => c (l + 1)) fun l hl => h (l + 1) (by omega)
    have h0 := h 0 (by omega)
    simp only [hB, pow_succ]
    nlinarith

theorem hB_digit {c : Nat → Nat} : ∀ {n l}, (∀ l < n, c l < 256) → l < n →
    hB c n / 256 ^ l % 256 = c l := by
  intro n
  induction n generalizing c with
  | zero => intro l _ hl; omega
  | succ n ih =>
    intro l h hl
    have h0 := h 0 (by omega)
    simp only [hB]
    rcases l with _ | l
    · simp only [pow_zero, Nat.div_one]
      omega
    · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num),
        Nat.div_eq_of_lt h0, Nat.zero_add]
      exact ih (c := fun l => c (l + 1)) (fun l hl => h (l + 1) (by omega)) (by omega)

theorem hB_of : ∀ {n x : Nat}, x < 256 ^ n → hB (fun l => x / 256 ^ l % 256) n = x := by
  intro n
  induction n with
  | zero => intro x hx; simp at hx; simp [hB, hx]
  | succ n ih =>
    intro x hx
    simp only [hB]
    have e : (fun l => x / 256 ^ (l + 1) % 256) = (fun l => x / 256 / 256 ^ l % 256) := by
      funext l
      rw [pow_succ', Nat.div_div_eq_div_mul]
    rw [e, ih (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hx; exact hx)]
    simp only [pow_zero, Nat.div_one]
    omega

theorem hB_add (c e : Nat → Nat) : ∀ n, hB c n + hB e n = hB (fun l => c l + e l) n := by
  intro n
  induction n generalizing c e with
  | zero => rfl
  | succ n ih =>
    simp only [hB]
    rw [← ih]
    ring

theorem hB_mul (k : Nat) (c : Nat → Nat) : ∀ n, k * hB c n = hB (fun l => k * c l) n := by
  intro n
  induction n generalizing c with
  | zero => simp [hB]
  | succ n ih =>
    simp only [hB]
    rw [← ih]
    ring

theorem byteOf_eq (w : UInt64) {l : Nat} (hl : l < 8) : byteOf w l = w.toNat / 256 ^ l % 256 := by
  unfold byteOf
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have e1 : (UInt64.ofNat (8 * l)).toNat % 64 = 8 * l := by
    rw [UInt64.toNat_ofNat']
    omega
  have e2 : (0xFF : UInt64).toNat = 2 ^ 8 - 1 := rfl
  rw [e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem hB_congr {c e : Nat → Nat} : ∀ {n}, (∀ l < n, c l = e l) → hB c n = hB e n := by
  intro n
  induction n generalizing c e with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [hB]
    rw [h 0 (by omega), ih (c := fun l => c (l + 1)) (e := fun l => e (l + 1))
      (fun l hl => h (l + 1) (by omega))]

theorem toNat_hB (w : UInt64) : w.toNat = hB (fun l => byteOf w l) 8 := by
  have h : w.toNat < 256 ^ 8 := by
    have := w.toNat_lt
    simpa using this
  calc w.toNat = hB (fun l => w.toNat / 256 ^ l % 256) 8 := (hB_of h).symm
    _ = hB (fun l => byteOf w l) 8 := hB_congr fun l hl => (byteOf_eq w hl).symm

theorem byteOf_lt (w : UInt64) (l : Nat) : byteOf w l < 256 := by
  unfold byteOf
  rw [UInt64.toNat_and]
  have e2 : (0xFF : UInt64).toNat = 2 ^ 8 - 1 := rfl
  rw [e2, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem byteOf_hB {w : UInt64} {c : Nat → Nat} (hc : ∀ l < 8, c l < 256)
    (hw : w.toNat = hB c 8) : ∀ l < 8, byteOf w l = c l := by
  intro l hl
  rw [byteOf_eq w hl, hw, hB_digit hc hl]

theorem byte_add {x y : UInt64} (h : ∀ l < 8, byteOf x l + byteOf y l < 256) :
    ∀ l < 8, byteOf (x + y) l = byteOf x l + byteOf y l := by
  refine byteOf_hB h ?_
  rw [UInt64.toNat_add, toNat_hB x, toNat_hB y, hB_add]
  exact Nat.mod_eq_of_lt (by have := hB_lt h; simpa using this)

theorem byte_mul {c x : UInt64} (h : ∀ l < 8, c.toNat * byteOf x l < 256) :
    ∀ l < 8, byteOf (c * x) l = c.toNat * byteOf x l := by
  refine byteOf_hB h ?_
  rw [UInt64.toNat_mul, toNat_hB x, hB_mul]
  exact Nat.mod_eq_of_lt (by have := hB_lt h; simpa using this)

theorem byte_pack {f : Nat → Nat} (h : ∀ l < 8, f l < 256) :
    ∀ l < 8, byteOf (packWord f) l = f l := by
  refine byteOf_hB h ?_
  have e : hB f 8 = f 0 + 256 * (f 1 + 256 * (f 2 + 256 * (f 3 + 256 * (f 4 + 256 * (f 5 +
      256 * (f 6 + 256 * f 7)))))) := by simp [hB]
  unfold packWord
  rw [UInt64.toNat_ofNat', e]
  exact Nat.mod_eq_of_lt (by have := hB_lt h; rw [e] at this; simpa using this)

theorem byte_zero (l : Nat) : byteOf 0 l = 0 := by
  unfold byteOf
  simp

theorem lane_eq (a : W14) (i : Nat) : a.lane i = byteOf (a.word (i / 8)) (i % 8) := rfl

theorem word_add (a b : W14) {q : Nat} (hq : q < 14) : (a.add b).word q = a.word q + b.word q := by
  interval_cases q <;> rfl

theorem word_smul (c : UInt64) (a : W14) {q : Nat} (hq : q < 14) :
    (W14.smul c a).word q = c * a.word q := by
  interval_cases q <;> rfl

theorem word_red (a : W14) {q : Nat} (hq : q < 14) : a.red.word q = redWord (a.word q) := by
  interval_cases q <;> rfl

theorem word_zero {q : Nat} : W14.zero.word q = 0 := by
  unfold W14.zero W14.word
  split <;> rfl

theorem lane_lt (a : W14) (i : Nat) : a.lane i < 256 := byteOf_lt _ _

theorem divmod8 {i : Nat} (hi : i < 112) : i / 8 < 14 ∧ i % 8 < 8 := ⟨by omega, Nat.mod_lt _ (by omega)⟩

theorem lane_add {a b : W14} (h : ∀ i < 112, a.lane i + b.lane i < 256) :
    ∀ i < 112, (a.add b).lane i = a.lane i + b.lane i := by
  intro i hi
  obtain ⟨hq, hl⟩ := divmod8 hi
  rw [lane_eq, word_add a b hq, lane_eq, lane_eq]
  refine byte_add (fun l hl' => ?_) _ hl
  have := h (8 * (i / 8) + l) (by omega)
  rw [lane_eq, lane_eq] at this
  have e1 : (8 * (i / 8) + l) / 8 = i / 8 := by omega
  have e2 : (8 * (i / 8) + l) % 8 = l := by omega
  rw [e1, e2] at this
  exact this

theorem lane_smul {c : UInt64} {a : W14} (h : ∀ i < 112, c.toNat * a.lane i < 256) :
    ∀ i < 112, (W14.smul c a).lane i = c.toNat * a.lane i := by
  intro i hi
  obtain ⟨hq, hl⟩ := divmod8 hi
  rw [lane_eq, word_smul c a hq, lane_eq]
  refine byte_mul (fun l hl' => ?_) _ hl
  have := h (8 * (i / 8) + l) (by omega)
  rw [lane_eq] at this
  have e1 : (8 * (i / 8) + l) / 8 = i / 8 := by omega
  have e2 : (8 * (i / 8) + l) % 8 = l := by omega
  rw [e1, e2] at this
  exact this

theorem lane_red (a : W14) : ∀ i < 112, a.red.lane i = a.lane i % 5 := by
  intro i hi
  obtain ⟨hq, hl⟩ := divmod8 hi
  rw [lane_eq, word_red a hq, lane_eq]
  unfold redWord
  exact byte_pack (fun l _ => by have := Nat.mod_lt (byteOf (a.word (i / 8)) l) (by norm_num : 0 < 5); omega) _ hl

theorem lane_zero (i : Nat) : W14.zero.lane i = 0 := by
  rw [lane_eq, word_zero, byte_zero]

theorem lane_packW {f : Nat → Nat} (h : ∀ i < 112, f i < 256) :
    ∀ i < 112, (packW f).lane i = f i := by
  intro i hi
  rw [lane_eq]
  have hl : i % 8 < 8 := Nat.mod_lt _ (by omega)
  have key : ∀ q < 14, ∀ l < 8, byteOf ((packW f).word q) l = f (8 * q + l) := by
    intro q hq l hl
    interval_cases q <;>
      exact byte_pack (f := fun l => f (_ + l)) (fun l hl => h _ (by omega)) l hl
  rw [key (i / 8) (by omega) (i % 8) hl]
  congr 1
  omega

@[expose] def vecA (a : Array Nat) : Fin 7 → ZMod 5 := fun k => ((a[k.val]! : Nat) : ZMod 5)

@[expose] def Sp (n : Nat) (E : Nat → Fin 7 → ZMod 5) : Submodule (ZMod 5) (Fin 7 → ZMod 5) :=
  Submodule.span (ZMod 5) (Set.range fun e : Fin n => E e.val)

theorem mem_Sp {n e : Nat} {E : Nat → Fin 7 → ZMod 5} (he : e < n) : E e ∈ Sp n E :=
  Submodule.subset_span ⟨⟨e, he⟩, rfl⟩

theorem Sp_mono {n n' : Nat} {E E' : Nat → Fin 7 → ZMod 5} (h : ∀ e < n, E e ∈ Sp n' E') :
    Sp n E ≤ Sp n' E' := by
  unfold Sp
  rw [Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  exact h e.val e.isLt

@[expose] def EchOK (n : Nat) (ech : Array (Array Nat)) (lead : Array Nat) : Prop :=
  ∀ e < n, (ech[e]!).size = 7 ∧ (∀ k < 7, (ech[e]!)[k]! < 5) ∧ lead[e]! < 7 ∧
    (ech[e]!)[lead[e]!]! = 1 ∧ ∀ e' < e, (ech[e]!)[lead[e']!]! = 0

theorem cast_red (a f b : Nat) (hf : f ≤ 5) :
    (((a + (5 - f) * b) % 5 : Nat) : ZMod 5) = (a : ZMod 5) - (f : ZMod 5) * (b : ZMod 5) := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hf]
  have h5 : ((5 : Nat) : ZMod 5) = 0 := rfl
  rw [h5]
  ring

theorem vecA_ofFn (g : Fin 7 → Nat) : vecA (Array.ofFn g) = fun k => ((g k : Nat) : ZMod 5) := by
  funext k
  unfold vecA
  rw [ofFn_get! _ k.isLt]

theorem nat_of_cast_zero {x : Nat} (hx : x < 5) (h : ((x : Nat) : ZMod 5) = 0) : x = 0 := by
  have := eq_of_cast hx (by norm_num : 0 < 5) (by rw [h, Nat.cast_zero])
  exact this

theorem redV_spec {n : Nat} {ech : Array (Array Nat)} {lead : Array Nat} (hn : ech.size = n)
    (hE : EchOK n ech lead) {v0 : Array Nat} (hv0 : v0.size = 7) (hv0' : ∀ k < 7, v0[k]! < 5) :
    (redV ech lead v0).size = 7 ∧ (∀ k < 7, (redV ech lead v0)[k]! < 5) ∧
      vecA v0 - vecA (redV ech lead v0) ∈ Sp n (fun e => vecA (ech[e]!)) ∧
      ∀ e < n, (redV ech lead v0)[lead[e]!]! = 0 := by
  unfold redV
  rw [hn]
  suffices h : ∀ j ≤ n, ((List.range j).foldl (fun b a => if (b[lead[a]!]! != 0) = true then
      Array.ofFn (n := 7) fun k => (b[k.val]! + (5 - b[lead[a]!]!) * (ech[a]!)[k.val]!) % 5
      else b) v0).size = 7 ∧
      (∀ k < 7, ((List.range j).foldl (fun b a => if (b[lead[a]!]! != 0) = true then
      Array.ofFn (n := 7) fun k => (b[k.val]! + (5 - b[lead[a]!]!) * (ech[a]!)[k.val]!) % 5
      else b) v0)[k]! < 5) ∧
      vecA v0 - vecA ((List.range j).foldl (fun b a => if (b[lead[a]!]! != 0) = true then
      Array.ofFn (n := 7) fun k => (b[k.val]! + (5 - b[lead[a]!]!) * (ech[a]!)[k.val]!) % 5
      else b) v0) ∈ Sp n (fun e => vecA (ech[e]!)) ∧
      ∀ e < j, ((List.range j).foldl (fun b a => if (b[lead[a]!]! != 0) = true then
      Array.ofFn (n := 7) fun k => (b[k.val]! + (5 - b[lead[a]!]!) * (ech[a]!)[k.val]!) % 5
      else b) v0)[lead[e]!]! = 0 from h n le_rfl
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨hv0, hv0', ?_, fun e he => absurd he (Nat.not_lt_zero e)⟩
    simp only [List.range_zero, List.foldl_nil, sub_self]
    exact Submodule.zero_mem _
  | succ j ih =>
    intro hj
    obtain ⟨s1, s2, s3, s4⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range j).foldl _ v0 = v at s1 s2 s3 s4
    obtain ⟨_, eb, hl, h1, h0⟩ := hE j (by omega)
    have hf : v[lead[j]!]! < 5 := s2 _ hl
    by_cases hc : (v[lead[j]!]! != 0) = true
    · rw [ite_eq_left hc]
      refine ⟨by simp, fun k hk => ?_, ?_, fun e he => ?_⟩
      · rw [ofFn_get! _ hk]
        exact Nat.mod_lt _ (by norm_num)
      · have e1 : vecA (Array.ofFn (n := 7) fun k =>
            (v[k.val]! + (5 - v[lead[j]!]!) * (ech[j]!)[k.val]!) % 5) =
            vecA v - ((v[lead[j]!]! : Nat) : ZMod 5) • vecA (ech[j]!) := by
          rw [vecA_ofFn]
          funext k
          rw [cast_red _ _ _ (by omega)]
          rfl
        rw [e1, sub_sub_eq_add_sub, add_sub_right_comm]
        exact Submodule.add_mem _ s3 (Submodule.smul_mem _ _ (mem_Sp (by omega)))
      · rw [ofFn_get! _ (hE e (by omega)).2.2.1]
        dsimp only
        by_cases hej : e = j
        · subst hej
          rw [h1]
          omega
        · rw [s4 e (by omega), h0 e (by omega)]
          simp
    · rw [ite_eq_right hc]
      refine ⟨s1, s2, s3, fun e he => ?_⟩
      by_cases hej : e = j
      · subst hej
        simpa using hc
      · exact s4 e (by omega)

theorem zero_of_red {n : Nat} {ech : Array (Array Nat)} {lead : Array Nat}
    (hE : EchOK n ech lead) {x : Fin 7 → ZMod 5} (hx : x ∈ Sp n (fun e => vecA (ech[e]!)))
    (hz : ∀ e (he : e < n), x ⟨lead[e]!, (hE e he).2.2.1⟩ = 0) : x = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  have hc0 : ∀ m, ∀ e : Fin n, e.val < m → c e = 0 := by
    intro m
    induction m with
    | zero => intro e he; omega
    | succ m ih =>
      intro e he
      by_cases hem : e.val < m
      · exact ih e hem
      · have hev : e.val = m := by omega
        have h := hz e.val e.isLt
        rw [← hc, Finset.sum_apply, Finset.sum_eq_single e] at h
        · simp only [Pi.smul_apply, smul_eq_mul, vecA] at h
          rw [(hE e.val e.isLt).2.2.2.1] at h
          simpa using h
        · intro b _ hbe
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases hb : b.val < e.val
          · rw [ih b (by omega), zero_mul]
          · have hb' : e.val < b.val := by
              have : b.val ≠ e.val := fun h' => hbe (Fin.ext h')
              omega
            unfold vecA
            rw [(hE b.val b.isLt).2.2.2.2 e.val hb', Nat.cast_zero, mul_zero]
        · intro h'
          exact absurd (Finset.mem_univ e) h'
  rw [← hc]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [hc0 (e.val + 1) e (by omega), zero_smul]

theorem row_not_mem {Rr Ri : Nat → Nat → ZMod 5}
    (hRi : ∀ a < 7, ∀ b < 7, ∑ l ∈ Finset.range 7, Rr a l * Ri l b = if a = b then 1 else 0)
    {n : Nat} (hn : n < 7) : (fun k : Fin 7 => Rr n k.val) ∉ Sp n (fun m k => Rr m k.val) := by
  intro h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  have hφ : ∀ a < 7, ∑ l : Fin 7, Rr a l.val * Ri l.val n = if a = n then 1 else 0 := by
    intro a ha
    rw [← hRi a ha n hn, Finset.sum_range (fun l => Rr a l * Ri l n)]
  have e1 := congrArg (fun v : Fin 7 → ZMod 5 => ∑ l : Fin 7, v l * Ri l.val n) hc
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul] at e1
  rw [Finset.sum_comm] at e1
  simp only [mul_assoc, ← Finset.mul_sum] at e1
  rw [hφ n hn, ite_eq_left rfl] at e1
  have e2 : ∀ m : Fin n, c m * ∑ l : Fin 7, Rr m.val l.val * Ri l.val n = 0 := by
    intro m
    rw [hφ m.val (by omega), ite_eq_right (by omega), mul_zero]
  rw [Finset.sum_eq_zero fun m _ => e2 m] at e1
  exact absurd e1 (by decide)

theorem firstNZ_fold (v : Array Nat) (l : List Nat) (b0 : Nat) (hl : ∀ k ∈ l, k < 7) :
    (l.foldl (fun b a => if (b == 7 && v[a]! != 0) = true then a else b) b0 = b0 ∧
        (b0 = 7 → ∀ k ∈ l, v[k]! = 0)) ∨
      (b0 = 7 ∧ l.foldl (fun b a => if (b == 7 && v[a]! != 0) = true then a else b) b0 ∈ l ∧
        v[l.foldl (fun b a => if (b == 7 && v[a]! != 0) = true then a else b) b0]! ≠ 0) := by
  induction l generalizing b0 with
  | nil => left; simp
  | cons x l ih =>
    have hl' : ∀ k ∈ l, k < 7 := fun k hk => hl k (List.mem_cons_of_mem x hk)
    rw [List.foldl_cons]
    by_cases hp : b0 = 7
    · by_cases ht : v[x]! ≠ 0
      · have e : (if (b0 == 7 && v[x]! != 0) = true then x else b0) = x := by simp [hp, ht]
        rw [e]
        have hx : x < 7 := hl x (by simp)
        rcases ih x hl' with ⟨h1, _⟩ | ⟨h1, _⟩
        · right
          rw [h1]
          exact ⟨hp, by simp, ht⟩
        · omega
      · have e : (if (b0 == 7 && v[x]! != 0) = true then x else b0) = b0 := by simp [ht]
        rw [e]
        rcases ih b0 hl' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · left
          refine ⟨h1, fun _ k hk => ?_⟩
          rcases List.mem_cons.1 hk with rfl | hk
          · simpa using ht
          · exact h2 hp k hk
        · right
          exact ⟨h1, List.mem_cons_of_mem x h2, h3⟩
    · have e : (if (b0 == 7 && v[x]! != 0) = true then x else b0) = b0 := by simp [hp]
      rw [e]
      rcases ih b0 hl' with ⟨h1, _⟩ | ⟨h1, _⟩
      · left
        exact ⟨h1, fun h => absurd h hp⟩
      · exact absurd h1 hp

theorem firstNZ_spec (v : Array Nat) :
    (firstNZ v < 7 ∧ v[firstNZ v]! ≠ 0) ∨ (firstNZ v = 7 ∧ ∀ k < 7, v[k]! = 0) := by
  unfold firstNZ
  rcases firstNZ_fold v (List.range 7) 7 (fun k hk => List.mem_range.1 hk) with
    ⟨h1, h2⟩ | ⟨_, h2, h3⟩
  · right
    exact ⟨h1, fun k hk => h2 rfl k (List.mem_range.2 hk)⟩
  · left
    exact ⟨List.mem_range.1 h2, h3⟩

theorem push_get {α : Type} [Inhabited α] (a : Array α) (x : α) (e : Nat) :
    (a.push x)[e]! = if e < a.size then a[e]! else if e = a.size then x else default := by
  by_cases h1 : e < a.size
  · rw [ite_eq_left h1, getElem!_pos (a.push x) e (by simp; omega), getElem!_pos a e h1,
      Array.getElem_push_lt h1]
  · rw [ite_eq_right h1]
    by_cases h2 : e = a.size
    · subst h2
      rw [ite_eq_left rfl, getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]
    · rw [ite_eq_right h2, getElem!_neg (a.push x) e (by simp; omega)]

theorem inv5_mul {x : Nat} (hx : x < 5) (h0 : x ≠ 0) : x * inv5 x % 5 = 1 := by
  unfold inv5
  interval_cases x <;> omega

section Pivots

variable {ds : Array ByteArray} {u Rr Ri : Nat → Nat → ZMod 5} {piv : Nat → Nat}

@[expose] def PInv (Rr : Nat → Nat → ZMod 5) (piv : Nat → Nat) (N : Nat)
    (s : Array (Array Nat) × Array Nat × Array Nat) : Prop :=
  ∃ n ≤ 7, (∀ l < n, piv l < N) ∧ (n < 7 → N ≤ piv n) ∧ s.1.size = n ∧ s.2.1.size = n ∧
    s.2.2.size = n ∧ (∀ l < n, s.2.2[l]! = piv l) ∧ EchOK n s.1 s.2.1 ∧
    Sp n (fun e => vecA (s.1[e]!)) = Sp n (fun m k => Rr m k.val)

theorem vecA_row (hds : ∀ i < 111, ∀ k < 7, (ds[k]!.get! i).toNat < 5 ∧
      (((ds[k]!.get! i).toNat : Nat) : ZMod 5) = ∑ m ∈ Finset.range 7, u i m * Rr m k)
    {N : Nat} (hN : N < 111) :
    vecA (Array.ofFn (n := 7) fun k => (ds[k.val]!.get! N).toNat) =
      ∑ m ∈ Finset.range 7, u N m • (fun k : Fin 7 => Rr m k.val) := by
  rw [vecA_ofFn]
  funext k
  rw [(hds N hN k.val k.isLt).2, Finset.sum_apply]
  rfl

theorem pv_step (hds : ∀ i < 111, ∀ k < 7, (ds[k]!.get! i).toNat < 5 ∧
      (((ds[k]!.get! i).toNat : Nat) : ZMod 5) = ∑ m ∈ Finset.range 7, u i m * Rr m k)
    (hz : ∀ m < 7, ∀ j < piv m, u j m = 0)
    (hδ : ∀ l < 7, ∀ m < 7, u (piv l) m = if l = m then 1 else 0)
    (hinc : ∀ a < 7, ∀ b < 7, a < b → piv a < piv b)
    (hRi : ∀ a < 7, ∀ b < 7, ∑ l ∈ Finset.range 7, Rr a l * Ri l b = if a = b then 1 else 0)
    {N : Nat} (hN : N < 111) {s : Array (Array Nat) × Array Nat × Array Nat}
    (hs : PInv Rr piv N s) : PInv Rr piv (N + 1) (pvStep ds s N) := by
  obtain ⟨n, hn7, hlt, hge, hs1, hs2, hs3, hpv, hE, hsp⟩ := hs
  unfold pvStep
  by_cases h7 : n = 7
  · subst h7
    rw [ite_eq_right (by omega)]
    exact ⟨7, le_rfl, fun l hl => by have := hlt l hl; omega, fun h => absurd h (by omega),
      hs1, hs2, hs3, hpv, hE, hsp⟩
  rw [ite_eq_left (by omega)]
  have hn : n < 7 := by omega
  have hNp : N ≤ piv n := hge hn
  set v0 := Array.ofFn (n := 7) fun k => (ds[k.val]!.get! N).toNat with hv0
  have hv0s : v0.size = 7 := by simp [hv0]
  have hv0b : ∀ k < 7, v0[k]! < 5 := fun k hk => by
    rw [hv0, ofFn_get! _ hk]
    exact (hds N hN k hk).1
  obtain ⟨r1, r2, r3, r4⟩ := redV_spec hs1 hE hv0s hv0b
  have hrow := vecA_row hds hN
  rw [← hv0] at hrow
  generalize redV s.1 s.2.1 v0 = v at r1 r2 r3 r4 ⊢
  have hmono : ∀ a < 7, ∀ b < 7, a ≤ b → piv a ≤ piv b := fun a ha b hb hab => by
    rcases Nat.eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact (hinc a ha b hb h).le
  have hvz : ∀ e (he : e < n), vecA v ⟨s.2.1[e]!, (hE e he).2.2.1⟩ = 0 := fun e he => by
    unfold vecA
    dsimp only
    rw [r4 e he, Nat.cast_zero]
  by_cases hNe : N < piv n
  ·
    have hmem : vecA v0 ∈ Sp n (fun m k => Rr m k.val) := by
      rw [hrow, ← Finset.sum_subset (fun x hx => Finset.mem_range.2
        (Nat.lt_of_lt_of_le (Finset.mem_range.1 hx) hn7))]
      · exact Submodule.sum_mem _ fun m hm =>
          Submodule.smul_mem _ _ (mem_Sp (Finset.mem_range.1 hm))
      · intro m hm hmn
        have hm7 := Finset.mem_range.1 hm
        have hmn' : n ≤ m := by
          by_contra h
          exact hmn (Finset.mem_range.2 (by omega))
        rw [hz m hm7 N (Nat.lt_of_lt_of_le hNe (hmono n hn m hm7 hmn')), zero_smul]
    have hvmem : vecA v ∈ Sp n (fun e => vecA (s.1[e]!)) := by
      have e1 : vecA v = vecA v0 - (vecA v0 - vecA v) := by abel
      rw [e1]
      exact Submodule.sub_mem _ (hsp ▸ hmem) r3
    have hv0' : vecA v = 0 := zero_of_red hE hvmem hvz
    have hall : ∀ k < 7, v[k]! = 0 := fun k hk =>
      nat_of_cast_zero (r2 k hk) (congrFun hv0' ⟨k, hk⟩)
    have hfz : firstNZ v = 7 := by
      rcases firstNZ_spec v with ⟨h1, h2⟩ | ⟨h1, _⟩
      · exact absurd (hall _ h1) h2
      · exact h1
    rw [ite_eq_right (by omega)]
    exact ⟨n, hn7, fun l hl => by have := hlt l hl; omega, fun _ => by omega, hs1, hs2, hs3,
      hpv, hE, hsp⟩
  · have hNeq : N = piv n := by omega
    have hrowN : vecA v0 = fun k : Fin 7 => Rr n k.val := by
      rw [hrow]
      funext k
      rw [Finset.sum_apply, hNeq]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl fun m hm => by rw [hδ n hn m (Finset.mem_range.1 hm)]]
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq (Finset.range 7) n, ite_eq_left (Finset.mem_range.2 hn)]
    have hvne : vecA v ≠ 0 := by
      intro h0
      apply row_not_mem hRi hn
      have e1 : (fun k : Fin 7 => Rr n k.val) = vecA v0 - vecA v := by rw [h0, sub_zero, hrowN]
      rw [e1, ← hsp]
      exact r3
    rcases firstNZ_spec v with ⟨hl7, hlnz⟩ | ⟨_, hall⟩
    swap
    · exact absurd (funext fun k => by unfold vecA; rw [hall k.val k.isLt]; rfl) hvne
    rw [ite_eq_left hl7]
    generalize firstNZ v = l at hl7 hlnz ⊢
    have hwk : ∀ k < 7, (v.map fun x => x * inv5 v[l]! % 5)[k]! = v[k]! * inv5 v[l]! % 5 :=
      fun k hk => by rw [get_mapR _ _ (by omega)]
    have hwsz : (v.map fun x => x * inv5 v[l]! % 5).size = 7 := by rw [Array.size_map, r1]
    generalize hiv : inv5 v[l]! = iv at hwk hwsz ⊢
    generalize hw : v.map (fun x => x * iv % 5) = w at hwk hwsz ⊢
    have hvl : v[l]! * iv % 5 = 1 := by
      rw [← hiv]
      exact inv5_mul (r2 l hl7) hlnz
    have hivc : ((v[l]! : Nat) : ZMod 5) * (iv : ZMod 5) = 1 := by
      have := congrArg (fun x : Nat => (x : ZMod 5)) hvl
      simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at this
      exact this
    have hvw : vecA w = (iv : ZMod 5) • vecA v := by
      funext k
      unfold vecA
      rw [hwk k.val k.isLt, ZMod.natCast_mod, Nat.cast_mul, Pi.smul_apply, smul_eq_mul, mul_comm]
    have hwv : vecA v = ((v[l]! : Nat) : ZMod 5) • vecA w := by
      rw [hvw, smul_smul, hivc, one_smul]
    have hE' : ∀ e < n, vecA ((s.1.push w)[e]!) = vecA (s.1[e]!) := fun e he => by
      rw [push_get, ite_eq_left (by omega)]
    have hEn : vecA ((s.1.push w)[n]!) = vecA w := by
      rw [push_get, ite_eq_right (by omega), ite_eq_left hs1.symm]
    refine ⟨n + 1, by omega, fun l' hl' => ?_, fun h => ?_, by simp [hs1], by simp [hs2],
      by simp [hs3], fun l' hl' => ?_, fun e he => ?_, ?_⟩
    · rcases Nat.lt_or_ge l' n with h | h
      · have := hlt l' h
        omega
      · have : l' = n := by omega
        subst this
        omega
    · have := hinc n hn (n + 1) h (by omega)
      omega
    · rw [push_get]
      rcases Nat.lt_or_ge l' n with h | h
      · rw [ite_eq_left (by omega), hpv l' h]
      · have hln : l' = n := by omega
        rw [ite_eq_right (by omega), ite_eq_left (by omega), hNeq, hln]
    · have hl1 : ∀ e' < n, (s.2.1.push l)[e']! = s.2.1[e']! := fun e' he' => by
        rw [push_get, ite_eq_left (by omega)]
      rcases Nat.lt_or_ge e n with h | h
      · obtain ⟨q1, q2, q3, q4, q5⟩ := hE e h
        rw [push_get, ite_eq_left (by omega), hl1 e h]
        exact ⟨q1, q2, q3, q4, fun e' he' => by rw [hl1 e' (by omega)]; exact q5 e' he'⟩
      · have hen : e = n := by omega
        subst hen
        have hln : (s.2.1.push l)[e]! = l := by rw [push_get, ite_eq_right (by omega), ite_eq_left hs2.symm]
        have hwn : (s.1.push w)[e]! = w := by rw [push_get, ite_eq_right (by omega), ite_eq_left hs1.symm]
        rw [hwn, hln]
        refine ⟨hwsz, ?_, hl7, ?_, ?_⟩
        · intro k hk
          rw [hwk k hk]
          exact Nat.mod_lt _ (by norm_num)
        · rw [hwk l hl7, hvl]
        · intro e' he'
          rw [hl1 e' he', hwk _ (hE e' he').2.2.1, r4 e' he', Nat.zero_mul]
    · have hsub : Sp n (fun e => vecA (s.1[e]!)) ≤ Sp (n + 1) (fun e => vecA ((s.1.push w)[e]!)) :=
        Sp_mono fun e he => by rw [← hE' e he]; exact mem_Sp (by omega)
      have hsubR : Sp n (fun m k => Rr m k.val) ≤ Sp (n + 1) (fun m k => Rr m k.val) :=
        Sp_mono fun e he => mem_Sp (by omega)
      have r3' : vecA v0 - vecA v ∈ Sp n (fun m k => Rr m k.val) := by
        rw [← hsp]
        exact r3
      apply le_antisymm
      · refine Sp_mono fun e he => ?_
        rcases Nat.lt_or_ge e n with h | h
        · rw [hE' e h]
          have h' : vecA (s.1[e]!) ∈ Sp n (fun m k => Rr m k.val) := by
            rw [← hsp]
            exact mem_Sp (E := fun e => vecA (s.1[e]!)) h
          exact hsubR h'
        · have hen : e = n := by omega
          subst hen
          rw [hEn, hvw]
          refine Submodule.smul_mem _ _ ?_
          have e1 : vecA v = (fun k : Fin 7 => Rr e k.val) - (vecA v0 - vecA v) := by
            rw [← hrowN]
            abel
          rw [e1]
          exact Submodule.sub_mem _ (mem_Sp (E := fun m k => Rr m k.val) (by omega)) (hsubR r3')
      · refine Sp_mono fun m hm => ?_
        rcases Nat.lt_or_ge m n with h | h
        · have h' : (fun k : Fin 7 => Rr m k.val) ∈ Sp n (fun e => vecA (s.1[e]!)) := by
            rw [hsp]
            exact mem_Sp (E := fun m k => Rr m k.val) h
          exact hsub h'
        · have hmn : m = n := by omega
          subst hmn
          have e1 : (fun k : Fin 7 => Rr m k.val) = ((v[l]! : Nat) : ZMod 5) •
              vecA ((s.1.push w)[m]!) + (vecA v0 - vecA v) := by
            rw [hEn, ← hwv, ← hrowN]
            abel
          rw [e1]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _
            (mem_Sp (E := fun e => vecA ((s.1.push w)[e]!)) (by omega))) (hsub r3)

theorem pivotsF_spec (hds : ∀ i < 111, ∀ k < 7, (ds[k]!.get! i).toNat < 5 ∧
      (((ds[k]!.get! i).toNat : Nat) : ZMod 5) = ∑ m ∈ Finset.range 7, u i m * Rr m k)
    (hz : ∀ m < 7, ∀ j < piv m, u j m = 0)
    (hδ : ∀ l < 7, ∀ m < 7, u (piv l) m = if l = m then 1 else 0)
    (hinc : ∀ a < 7, ∀ b < 7, a < b → piv a < piv b) (h6 : piv 6 < 111)
    (hRi : ∀ a < 7, ∀ b < 7, ∑ l ∈ Finset.range 7, Rr a l * Ri l b = if a = b then 1 else 0) :
    (pivotsF ds).size = 7 ∧ ∀ l < 7, (pivotsF ds)[l]! = piv l := by
  have hall : ∀ N ≤ 111, PInv Rr piv N ((List.range N).foldl (pvStep ds) (#[], #[], #[])) := by
    intro N
    induction N with
    | zero =>
      intro _
      refine ⟨0, by omega, fun l hl => absurd hl (Nat.not_lt_zero l), fun _ => Nat.zero_le _,
        rfl, rfl, rfl, fun l hl => absurd hl (Nat.not_lt_zero l),
        fun e he => absurd he (Nat.not_lt_zero e), ?_⟩
      unfold Sp
      rw [Set.range_eq_empty, Set.range_eq_empty]
    | succ N ih =>
      intro hN
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact pv_step hds hz hδ hinc hRi (by omega) (ih (by omega))
  obtain ⟨n, hn7, -, hge, -, -, hs3, hpv, -, -⟩ := hall 111 le_rfl
  have hn : n = 7 := by
    by_contra h
    have h1 := hge (by omega)
    have h2 : piv n ≤ piv 6 := by
      rcases Nat.lt_or_ge n 6 with h' | h'
      · exact (hinc n (by omega) 6 (by omega) h').le
      · have : n = 6 := by omega
        rw [this]
    omega
  subst hn
  exact ⟨hs3, hpv⟩

end Pivots

theorem foldBlk_eqL (b : Nat) (f : Nat → Nat → Nat) (len s : Nat) :
    foldBlk b f len s = (List.range len).foldr (fun l s => f (b + l) s) s := by
  induction len generalizing s with
  | zero => rfl
  | succ len ih =>
    have e : foldBlk b f (len + 1) s = foldBlk b f len (f (b + len) s) :=
      strictN_valL (f (b + len) s) (foldBlk b f len)
    rw [e, ih, List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]

theorem foldr_range_add (f : Nat → Nat → Nat) (t a b : Nat) :
    (List.range (a + b)).foldr f t = (List.range a).foldr f ((List.range b).foldr
      (fun l s => f (a + l) s) t) := by
  rw [List.range_add, List.foldr_append, List.foldr_map]

theorem foldN_eqL (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldN n f s = (List.range n).foldr f s := by
  have hsl : ∀ a, Nat.shiftLeft a 6 = 64 * a := fun a => by
    change a <<< 6 = _
    rw [Nat.shiftLeft_eq]
    ring
  have hG : ∀ q t, Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) q t =
      (List.range (64 * q)).foldr f t := by
    intro q
    induction q with
    | zero => intro t; rfl
    | succ q ih =>
      intro t
      have e : Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
          (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
          (q + 1) t = Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
          (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) q
          (foldBlk (Nat.shiftLeft q 6) f 64 t) := strictN_valL _ _
      rw [e, ih, foldBlk_eqL, hsl, Nat.mul_add, Nat.mul_one, foldr_range_add]
  have e : foldN n f s = Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
      (Nat.shiftRight n 6) (foldBlk (Nat.shiftLeft (Nat.shiftRight n 6) 6) f (Nat.land n 63) s) :=
    rfl
  have hsr : Nat.shiftRight n 6 = n / 64 := by
    change n >>> 6 = _
    rw [Nat.shiftRight_eq_div_pow]
  have hla : Nat.land n 63 = n % 64 := by
    rw [land_eq]
    have h63 : (63 : Nat) = 2 ^ 6 - 1 := rfl
    rw [h63, Nat.and_two_pow_sub_one_eq_mod]
  rw [e, hG, foldBlk_eqL, hsl, hsr, hla, ← foldr_range_add, Nat.div_add_mod]

@[expose] def placeF (val sh : Nat → Nat) (n : Nat) : Nat :=
  (List.range n).foldr (fun p acc => acc ||| val p <<< sh p) 0

theorem foldr_lor (val sh : Nat → Nat) (l : List Nat) (s : Nat) :
    l.foldr (fun p acc => acc ||| val p <<< sh p) s =
      l.foldr (fun p acc => acc ||| val p <<< sh p) 0 ||| s := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, Nat.lor_assoc, Nat.lor_comm s, ← Nat.lor_assoc]

theorem placeF_spec {d w S N : Nat} (hS : w * d ≤ S) {pl val sh : Nat → Nat}
    (hpl : ∀ p < N, pl p < d * d) (hinj : ∀ p < N, ∀ q < N, pl p = pl q → p = q)
    (hv : ∀ p < N, val p < 2 ^ w) (hsh : ∀ p < N, sh p = S * (pl p / d) + w * (pl p % d)) :
    ∀ n ≤ N, (∀ p < n, entL d w S (placeF val sh n) (pl p) = val p) ∧
      ∀ τ < d * d, (∀ p < n, pl p ≠ τ) → entL d w S (placeF val sh n) τ = 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun p hp => absurd hp (Nat.not_lt_zero p), fun τ _ _ => ?_⟩
    simp [placeF, entL]
  | succ n ih =>
    intro hn
    obtain ⟨i1, i2⟩ := ih (by omega)
    have e : placeF val sh (n + 1) = placeF val sh n ||| val n <<< (S * (pl n / d) +
        w * (pl n % d)) := by
      unfold placeF
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_lor,
        Nat.zero_or, hsh n (by omega)]
    rw [e]
    have hn' := hpl n (by omega)
    refine ⟨fun p hp => ?_, fun τ hτ hne => ?_⟩
    · rw [entL_put hS (hpl p (by omega)) hn' (hv n (by omega))]
      by_cases hpn : p = n
      · subst hpn
        rw [ite_eq_left rfl, i2 _ hn' (fun q hq h => by have := hinj q (by omega) p (by omega) h; omega),
          Nat.zero_or]
      · rw [ite_eq_right (fun h => hpn (hinj p (by omega) n (by omega) h)), i1 p (by omega)]
    · rw [entL_put hS hτ hn' (hv n (by omega)), ite_eq_right (fun h => hne n (by omega) h.symm)]
      exact i2 τ hτ fun p hp => hne p (by omega)

theorem upOfD_ent {w S D : Nat} (hS : S = 111 * w) (h5 : 5 ≤ 2 ^ w)
    (hD : ∀ p < 826, fld(D, 4 * p, 15) < 5) {i m : Nat} (hi : i < 111) (hm : m < 111) :
    upOfD w S D / 2 ^ (S * i + w * m) % 2 ^ w =
      if m < 7 then fld(D, 4 * (111 * m + i), 15) else 0 := by
  have hup : upOfD w S D = placeF (fun p => fld(D, 4 * p, 15))
      (fun p => S * (p % 111) + w * (p / 111)) 777 := by
    unfold upOfD placeF
    rw [foldN_eqL]
    rfl
  have hspec := placeF_spec (d := 111) (w := w) (S := S) (N := 777) (by omega)
    (pl := fun p => 111 * (p % 111) + p / 111) (val := fun p => fld(D, 4 * p, 15))
    (sh := fun p => S * (p % 111) + w * (p / 111))
    (fun p hp => by omega) (fun p hp q hq h => by omega)
    (fun p hp => Nat.lt_of_lt_of_le (hD p (by omega)) h5)
    (fun p hp => by
      have e1 : (111 * (p % 111) + p / 111) / 111 = p % 111 := by omega
      have e2 : (111 * (p % 111) + p / 111) % 111 = p / 111 := by omega
      simp only [e1, e2]) 777 le_rfl
  have hτ : 111 * i + m < 111 * 111 := by omega
  have ent : entL 111 w S (upOfD w S D) (111 * i + m) = upOfD w S D / 2 ^ (S * i + w * m) % 2 ^ w := by
    unfold entL
    have e1 : (111 * i + m) / 111 = i := by omega
    have e2 : (111 * i + m) % 111 = m := by omega
    rw [e1, e2]
  rw [← ent, hup]
  by_cases hm7 : m < 7
  · rw [ite_eq_left hm7]
    have := hspec.1 (111 * m + i) (by omega)
    have e3 : 111 * ((111 * m + i) % 111) + (111 * m + i) / 111 = 111 * i + m := by omega
    simp only [e3] at this
    exact this
  · rw [ite_eq_right hm7]
    refine hspec.2 _ hτ fun p hp h => ?_
    have h1 : p / 111 < 7 := by omega
    have h2 : p % 111 < 111 := Nat.mod_lt _ (by omega)
    have h3 := divmod_uniq (B := 111) (a := p / 111) (b := m) (i := p % 111) (j := i) (by omega)
      hm h
    omega

theorem lane7_ent {w S : Nat} {R : Array Nat} (hS : S = 111 * w) (h5 : 5 ≤ 2 ^ w)
    (hR : ∀ t < 49, R[t]! < 5) {a b : Nat} (ha : a < 111) (hb : b < 111) :
    lane7 w S R / 2 ^ (S * a + w * b) % 2 ^ w = if a < 7 ∧ b < 7 then R[7 * a + b]! else 0 := by
  have hup : lane7 w S R = placeF (fun t => R[t]!) (fun t => S * (t / 7) + w * (t % 7)) 49 := by
    unfold lane7 placeF
    rw [foldN_eqL]
    rfl
  have hspec := placeF_spec (d := 111) (w := w) (S := S) (N := 49) (by omega)
    (pl := fun t => 111 * (t / 7) + t % 7) (val := fun t => R[t]!)
    (sh := fun t => S * (t / 7) + w * (t % 7))
    (fun p hp => by omega) (fun p hp q hq h => by omega)
    (fun p hp => Nat.lt_of_lt_of_le (hR p hp) h5)
    (fun p hp => by
      have e1 : (111 * (p / 7) + p % 7) / 111 = p / 7 := by omega
      have e2 : (111 * (p / 7) + p % 7) % 111 = p % 7 := by omega
      simp only [e1, e2]) 49 le_rfl
  have hτ : 111 * a + b < 111 * 111 := by omega
  have ent : entL 111 w S (lane7 w S R) (111 * a + b) = lane7 w S R / 2 ^ (S * a + w * b) % 2 ^ w := by
    unfold entL
    have e1 : (111 * a + b) / 111 = a := by omega
    have e2 : (111 * a + b) % 111 = b := by omega
    rw [e1, e2]
  rw [← ent, hup]
  by_cases hab : a < 7 ∧ b < 7
  · rw [ite_eq_left hab]
    have := hspec.1 (7 * a + b) (by omega)
    have e3 : 111 * ((7 * a + b) / 7) + (7 * a + b) % 7 = 111 * a + b := by omega
    simp only [e3] at this
    exact this
  · rw [ite_eq_right hab]
    exact hspec.2 _ hτ fun p hp h => by omega

@[expose] def dF (D : Nat) (p : Nat) : Nat := if p < 826 then fld(D, 4 * p, 15) else 0

theorem code3_toNat (a b c : Nat) : (code3 a b c).toNat = a % 5 + 5 * (b % 5) + 25 * (c % 5) := by
  unfold code3
  rw [UInt8.toNat_ofNat']
  omega

theorem keyOfD_size (D : Nat) : (keyOfD D).size = 276 := by
  unfold keyOfD encodeDigits
  simp [ByteArray.size]

theorem keyOfD_get (D : Nat) {q : Nat} (hq : q < 276) :
    ((keyOfD D).get! q).toNat = dF D (3 * q) % 5 + 5 * (dF D (3 * q + 1) % 5) +
      25 * (dF D (3 * q + 2) % 5) := by
  unfold keyOfD encodeDigits
  rw [ByteArray.get!, ofFn_get! _ hq, code3_toNat]
  rfl

theorem keyDigit_keyOfD (D : Nat) {p : Nat} (hp : p < 828) :
    keyDigit (keyOfD D) p = dF D p % 5 := by
  unfold keyDigit
  rw [keyOfD_get D (by omega)]
  have h0 := Nat.mod_lt (dF D (3 * (p / 3))) (by norm_num : 0 < 5)
  have h1 := Nat.mod_lt (dF D (3 * (p / 3) + 1)) (by norm_num : 0 < 5)
  have h2 := Nat.mod_lt (dF D (3 * (p / 3) + 2)) (by norm_num : 0 < 5)
  have hr : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hp3 : p = 3 * (p / 3) + p % 3 := (Nat.div_add_mod p 3).symm
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
  · rw [h, pow_zero, Nat.div_one]
    have e : 3 * (p / 3) = p := by omega
    rw [e]
    omega
  · rw [h, pow_one]
    have e : 3 * (p / 3) + 1 = p := by omega
    rw [e]
    omega
  · rw [h]
    have e : 3 * (p / 3) + 2 = p := by omega
    rw [e]
    norm_num
    omega

theorem dF_lt {D : Nat} (hD : ∀ p < 826, fld(D, 4 * p, 15) < 5) (p : Nat) : dF D p < 5 := by
  unfold dF
  split
  · exact hD p ‹_›
  · norm_num

theorem keyDigit_keyOfD' {D : Nat} (hD : ∀ p < 826, fld(D, 4 * p, 15) < 5) {p : Nat}
    (hp : p < 828) : keyDigit (keyOfD D) p = dF D p := by
  rw [keyDigit_keyOfD D hp, Nat.mod_eq_of_lt (dF_lt hD p)]

theorem keyS_get (key : ByteArray) {t : Nat} (ht : t < 49) :
    (keyS key)[t]! = keyDigit key (777 + t) := by
  unfold keyS keyDigit
  rw [ofFn_get! _ ht]
  dsimp only
  have e1 : (777 + t) / 3 = 259 + t / 3 := by omega
  rw [e1]
  rcases (by omega : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2) with h | h | h
  · have e2 : (777 + t) % 3 = 0 := by omega
    rw [ite_eq_left h, e2, pow_zero, Nat.div_one]
  · have e2 : (777 + t) % 3 = 1 := by omega
    rw [ite_eq_right (by omega), ite_eq_left h, e2, pow_one]
  · have e2 : (777 + t) % 3 = 2 := by omega
    rw [ite_eq_right (by omega), ite_eq_right (by omega), e2]

theorem keyRows_get (key : ByteArray) {m j : Nat} (hm : m < 7) (hj : j < 112)
    (hk : keyDigit key (111 * m + j) < 256) :
    ((CFSG.Sporadic.Ly.Native.keyRows key)[m]!.get! j).toNat = keyDigit key (111 * m + j) := by
  unfold CFSG.Sporadic.Ly.Native.keyRows
  rw [ofFn_get! _ hm, ByteArray.get!, ofFn_get! _ hj, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt hk

theorem fold_lanes {B : Nat} (f : Nat → W14) : ∀ n, n * B < 256 →
    (∀ g < n, ∀ i < 112, (f g).lane i ≤ B) →
    ∀ i < 112, (Nat.fold n (fun g _ acc => acc.add (f g)) W14.zero).lane i =
      ∑ g ∈ Finset.range n, (f g).lane i := by
  intro n
  induction n with
  | zero => intro _ _ i _; rw [Nat.fold_zero, lane_zero]; rfl
  | succ n ih =>
    intro hnB hf i hi
    have ih' := ih (by nlinarith) (fun g hg => hf g (by omega))
    rw [Nat.fold_succ]
    have hsum : ∀ i < 112, ∑ g ∈ Finset.range n, (f g).lane i ≤ n * B := fun i hi => by
      calc ∑ g ∈ Finset.range n, (f g).lane i ≤ ∑ _g ∈ Finset.range n, B :=
            Finset.sum_le_sum fun g hg => hf g (by have := Finset.mem_range.1 hg; omega) i hi
        _ = n * B := by simp
    rw [lane_add (fun i hi => by
      rw [ih' i hi]
      have := hsum i hi
      have := hf n (by omega) i hi
      nlinarith) i hi, ih' i hi, Finset.sum_range_succ]

theorem pushRed_data (b : ByteArray) (w : UInt64) :
    (pushRed b w).data = b.data ++ Array.ofFn (n := 8) fun l => UInt8.ofNat (byteOf w l.val % 5) := by
  apply Array.ext'
  simp [pushRed, ByteArray.push, List.ofFn_succ]

theorem digits_data (a : W14) : ∀ n, (Nat.fold n (fun q _ b => pushRed b (a.word q))
    (ByteArray.emptyWithCapacity 112)).data =
    Array.ofFn (n := 8 * n) fun j => UInt8.ofNat (byteOf (a.word (j.val / 8)) (j.val % 8) % 5) := by
  intro n
  induction n with
  | zero =>
    rw [Nat.fold_zero]
    apply Array.ext
    · simp [ByteArray.emptyWithCapacity]
      rfl
    · intro j h1 h2
      simp at h2
  | succ n ih =>
    rw [Nat.fold_succ, pushRed_data, ih]
    apply Array.ext
    · simp
      omega
    · intro j h1 h2
      have hj : j < 8 * (n + 1) := by simpa using h2
      by_cases hj8 : j < 8 * n
      · rw [Array.getElem_append_left (by simpa using hj8), Array.getElem_ofFn,
          Array.getElem_ofFn]
      · rw [Array.getElem_append_right (by simp; omega), Array.getElem_ofFn,
          Array.getElem_ofFn]
        have e1 : j / 8 = n := by omega
        have e2 : j - (Array.ofFn (n := 8 * n) fun j =>
            UInt8.ofNat (byteOf (a.word (j.val / 8)) (j.val % 8) % 5)).size = j % 8 := by
          simp
          omega
        simp only [e1, e2]

theorem digits_spec (a : W14) : a.digits.size = 112 ∧
    ∀ i < 112, (a.digits.get! i).toNat = a.lane i % 5 := by
  have hd := digits_data a 14
  refine ⟨by rw [ByteArray.size]; unfold W14.digits; rw [hd]; simp, fun i hi => ?_⟩
  unfold W14.digits
  rw [ByteArray.get!]
  rw [hd, ofFn_get! _ hi, UInt8.toNat_ofNat', lane_eq]
  dsimp only
  have := Nat.mod_lt (byteOf (a.word (i / 8)) (i % 8)) (by norm_num : 0 < 5)
  omega

theorem allIn_iff {n : Nat} {p : Nat → Bool} :
    CFSG.Sporadic.Th.Native.allIn 0 n p = true ↔ ∀ k < n, p k = true := by
  unfold CFSG.Sporadic.Th.Native.allIn
  rw [Nat.sub_zero]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true, ih]
    simp only [Nat.zero_add]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_or_ge k n with h | h
      · exact h1 k h
      · have : k = n := by omega
        subst this
        exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

theorem allIn_congr {n : Nat} {p q : Nat → Bool} (h : ∀ k < n, p k = q k) :
    CFSG.Sporadic.Th.Native.allIn 0 n p = CFSG.Sporadic.Th.Native.allIn 0 n q := by
  apply Bool.eq_iff_iff.2
  rw [allIn_iff, allIn_iff]
  exact ⟨fun h1 k hk => (h k hk) ▸ h1 k hk, fun h1 k hk => (h k hk).symm ▸ h1 k hk⟩

theorem sum3 (f : Nat → ZMod 5) : ∀ n, ∑ j ∈ Finset.range (3 * n), f j =
    ∑ g ∈ Finset.range n, (f (3 * g) + f (3 * g + 1) + f (3 * g + 2)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem frTable_get (M : Array (Array Nat)) {g c : Nat} (hg : g < 37) (hc : c < 125) :
    (frTable M)[125 * g + c]! = frEntry M g c := by
  unfold frTable
  rw [ofFn_get! _ (by omega)]
  dsimp only
  have e1 : (125 * g + c) / 125 = g := by omega
  have e2 : (125 * g + c) % 125 = c := by omega
  rw [e1, e2]

theorem frEntry_lane (M : Array (Array Nat)) (g c : Nat) {i : Nat} (hi : i < 112) :
    (frEntry M g c).lane i = frSum M i g c % 5 :=
  lane_packW (fun i _ => by have := Nat.mod_lt (frSum M i g c) (by norm_num : 0 < 5); omega) i hi

theorem actYs_lane {D : Nat} (hD : ∀ p < 826, fld(D, 4 * p, 15) < 5) (M : Array (Array Nat))
    {r i : Nat} (hr : r < 7) (hi : i < 112) :
    (actYs (frTable M) (keyOfD D))[r]!.lane i < 5 ∧
      (((actYs (frTable M) (keyOfD D))[r]!.lane i : Nat) : ZMod 5) =
        ∑ j ∈ Finset.range 111, ((ent M i j : Nat) : ZMod 5) * ((dF D (111 * r + j) : Nat) : ZMod 5) := by
  have hy : (actYs (frTable M) (keyOfD D))[r]! = (rowProd (frTable M) (keyOfD D) r).red := by
    unfold actYs
    rw [ofFn_get! _ hr]
  rw [hy, lane_red _ i hi]
  refine ⟨Nat.mod_lt _ (by norm_num), ?_⟩
  rw [ZMod.natCast_mod]
  have hc : ∀ g < 37, ((keyOfD D).get! (37 * r + g)).toNat < 125 := fun g hg => by
    rw [keyOfD_get D (by omega)]
    have := Nat.mod_lt (dF D (3 * (37 * r + g))) (by norm_num : 0 < 5)
    have := Nat.mod_lt (dF D (3 * (37 * r + g) + 1)) (by norm_num : 0 < 5)
    have := Nat.mod_lt (dF D (3 * (37 * r + g) + 2)) (by norm_num : 0 < 5)
    omega
  have hf : ∀ g < 37, ∀ i < 112,
      ((frTable M)[125 * g + ((keyOfD D).get! (37 * r + g)).toNat]!).lane i ≤ 4 := by
    intro g hg i hi
    rw [frTable_get M hg (hc g hg), frEntry_lane M _ _ hi]
    have := Nat.mod_lt (frSum M i g ((keyOfD D).get! (37 * r + g)).toNat) (by norm_num : 0 < 5)
    omega
  have hrow := fold_lanes (B := 4) (fun g => (frTable M)[125 * g + ((keyOfD D).get! (37 * r + g)).toNat]!)
    37 (by norm_num) hf i hi
  unfold rowProd
  rw [hrow, Nat.cast_sum]
  have e3 : (111 : Nat) = 3 * 37 := rfl
  rw [e3, sum3]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  rw [frTable_get M hg' (hc g hg'), frEntry_lane M _ _ hi, ZMod.natCast_mod]
  unfold frSum
  rw [keyOfD_get D (by omega)]
  have h0 := dF_lt hD (3 * (37 * r + g))
  have h1 := dF_lt hD (3 * (37 * r + g) + 1)
  have h2 := dF_lt hD (3 * (37 * r + g) + 2)
  have q0 : (dF D (3 * (37 * r + g)) % 5 + 5 * (dF D (3 * (37 * r + g) + 1) % 5) +
      25 * (dF D (3 * (37 * r + g) + 2) % 5)) % 5 = dF D (111 * r + 3 * g) := by
    have e : 3 * (37 * r + g) = 111 * r + 3 * g := by ring
    rw [e] at h0 ⊢
    omega
  have q1 : (dF D (3 * (37 * r + g)) % 5 + 5 * (dF D (3 * (37 * r + g) + 1) % 5) +
      25 * (dF D (3 * (37 * r + g) + 2) % 5)) / 5 % 5 = dF D (111 * r + (3 * g + 1)) := by
    have e : 3 * (37 * r + g) + 1 = 111 * r + (3 * g + 1) := by ring
    rw [e] at h1 ⊢
    omega
  have q2 : (dF D (3 * (37 * r + g)) % 5 + 5 * (dF D (3 * (37 * r + g) + 1) % 5) +
      25 * (dF D (3 * (37 * r + g) + 2) % 5)) / 25 % 5 = dF D (111 * r + (3 * g + 2)) := by
    have e : 3 * (37 * r + g) + 2 = 111 * r + (3 * g + 2) := by ring
    rw [e] at h2 ⊢
    omega
  rw [q0, q1, q2]
  push_cast
  ring

open CFSG.KS.Ord in
theorem mat_ent {w S T L H CM RM ONE LV HV X D D' : Nat} {R : Array Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true)
    (hU : validM 5 (111 * S) L H (upOfD w S D) = true)
    (hU' : validM 5 (111 * S) L H (upOfD w S D') = true)
    (hR7 : validM 5 (111 * S) L H (lane7 w S R) = true)
    (hD : ∀ p < 826, fld(D, 4 * p, 15) < 5) (hD' : ∀ p < 826, fld(D', 4 * p, 15) < 5)
    (hRs : ∀ t < 49, R[t]! < 5)
    (hst : mulR 5 w S 111 T L H CM RM X (upOfD w S D) =
      mulR 5 w S 111 T L H CM RM (upOfD w S D') (lane7 w S R))
    {i r : Nat} (hi : i < 111) (hr : r < 7) :
    ∑ j ∈ Finset.range 111, ((ent (unpackL 111 w S X) i j : Nat) : ZMod 5) *
        ((dF D (111 * r + j) : Nat) : ZMod 5) =
      ∑ m ∈ Finset.range 7, ((dF D' (111 * m + i) : Nat) : ZMod 5) * ((R[7 * m + r]! : Nat) : ZMod 5) := by
  obtain ⟨-, hSw, -, hpw⟩ := cfacts hc
  have hS : S = 111 * w := hSw
  have cX := validM_canon hc hX
  have cU := validM_canon hc hU
  have cU' := validM_canon hc hU'
  have cL := validM_canon hc hR7
  have e1 := (mulR_sound hc cX cU).2
  have e2 := (mulR_sound hc cU' cL).2
  have hm : ordMat 5 111 w S X * ordMat 5 111 w S (upOfD w S D) =
      ordMat 5 111 w S (upOfD w S D') * ordMat 5 111 w S (lane7 w S R) := by
    rw [← e1, ← e2, hst]
  have h := congrFun (congrFun hm ⟨i, hi⟩) ⟨r, by omega⟩
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  simp only [ordMat_apply] at h
  calc ∑ j ∈ Finset.range 111, ((ent (unpackL 111 w S X) i j : Nat) : ZMod 5) *
        ((dF D (111 * r + j) : Nat) : ZMod 5)
      = ∑ j : Fin 111, ((X / 2 ^ (S * i + w * j.val) % 2 ^ w : Nat) : ZMod 5) *
          ((upOfD w S D / 2 ^ (S * j.val + w * r) % 2 ^ w : Nat) : ZMod 5) := by
        rw [Finset.sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold CFSG.Sporadic.Ly.Native.ent
        rw [ite_eq_left ⟨hi, j.isLt⟩, unpackL_get hi j.isLt, upOfD_ent hS hpw hD j.isLt (by omega),
          ite_eq_left hr]
        unfold dF
        rw [ite_eq_left (by omega)]
    _ = ∑ m : Fin 111, ((upOfD w S D' / 2 ^ (S * i + w * m.val) % 2 ^ w : Nat) : ZMod 5) *
          ((lane7 w S R / 2 ^ (S * m.val + w * r) % 2 ^ w : Nat) : ZMod 5) := h
    _ = ∑ m ∈ Finset.range 111, (((if m < 7 then fld(D', 4 * (111 * m + i), 15) else 0) : Nat) :
          ZMod 5) * (((if m < 7 ∧ r < 7 then R[7 * m + r]! else 0) : Nat) : ZMod 5) := by
        rw [Finset.sum_range]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [upOfD_ent hS hpw hD' hi m.isLt, lane7_ent hS hpw hRs m.isLt (by omega)]
    _ = ∑ m ∈ Finset.range 7, ((dF D' (111 * m + i) : Nat) : ZMod 5) *
          ((R[7 * m + r]! : Nat) : ZMod 5) := by
        rw [← Finset.sum_subset (s₁ := Finset.range 7) (fun x hx => Finset.mem_range.2
          (by have := Finset.mem_range.1 hx; omega))]
        · refine Finset.sum_congr rfl fun m hm => ?_
          have hm' := Finset.mem_range.1 hm
          rw [ite_eq_left hm', ite_eq_left ⟨hm', hr⟩]
          unfold dF
          rw [ite_eq_left (by omega)]
        · intro m _ hm
          have hm' : ¬ m < 7 := fun h' => hm (Finset.mem_range.2 h')
          rw [ite_eq_right hm']
          simp

theorem combine_spec (ys : Array W14) (Pinv : Array Nat)
    (hy : ∀ k < 7, ∀ i < 112, (ys[k]!).lane i < 5) {m : Nat} (hm : m < 7) :
    ((combine ys Pinv)[m]!).size = 112 ∧ ∀ i < 112, ((combine ys Pinv)[m]!.get! i).toNat =
      (∑ k ∈ Finset.range 7, (Pinv[7 * k + m]! % 5) * (ys[k]!).lane i) % 5 := by
  unfold combine
  rw [ofFn_get! _ hm]
  dsimp only
  obtain ⟨d1, d2⟩ := digits_spec (Nat.fold 7 (fun k _ acc =>
    acc.add (W14.smul (UInt64.ofNat (Pinv[7 * k + m]! % 5)) ys[k]!)) W14.zero)
  have hc : ∀ k, (UInt64.ofNat (Pinv[7 * k + m]! % 5)).toNat = Pinv[7 * k + m]! % 5 := fun k => by
    rw [UInt64.toNat_ofNat']
    have := Nat.mod_lt (Pinv[7 * k + m]!) (by norm_num : 0 < 5)
    omega
  have hsm : ∀ k < 7, ∀ i < 112, (W14.smul (UInt64.ofNat (Pinv[7 * k + m]! % 5)) ys[k]!).lane i =
      (Pinv[7 * k + m]! % 5) * (ys[k]!).lane i := fun k hk i hi => by
    rw [lane_smul (fun i hi => by
      rw [hc]
      have := Nat.mod_lt (Pinv[7 * k + m]!) (by norm_num : 0 < 5)
      have := hy k hk i hi
      nlinarith) i hi, hc]
  have hfl := fold_lanes (B := 16) (fun k => W14.smul (UInt64.ofNat (Pinv[7 * k + m]! % 5)) ys[k]!)
    7 (by norm_num) (fun k hk i hi => by
      rw [hsm k hk i hi]
      have := Nat.mod_lt (Pinv[7 * k + m]!) (by norm_num : 0 < 5)
      have := hy k hk i hi
      nlinarith)
  refine ⟨d1, fun i hi => ?_⟩
  rw [d2 i hi, hfl i hi]
  congr 1
  exact Finset.sum_congr rfl fun k hk => hsm k (Finset.mem_range.1 hk) i hi

theorem rref_iff {ds : Array ByteArray} {piv : Array Nat} :
    rrefOK ds piv = true ↔ piv.size = 7 ∧ ds.size = 7 ∧ (∀ m < 7, (ds[m]!).size = 112) ∧
      (∀ m < 7, piv[m]! < 111 ∧ (m + 1 = 7 ∨ piv[m]! < piv[m + 1]!)) ∧
      (∀ m < 7, ∀ l < 7, (ds[m]!.get! piv[l]!).toNat = if l = m then 1 else 0) ∧
      (∀ m < 7, ∀ j < piv[m]!, (ds[m]!.get! j).toNat = 0) := by
  unfold rrefOK
  simp only [Bool.and_eq_true, beq_iff_eq, allIn_iff, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    refine ⟨h1, h2, fun m hm => ?_, h4, fun m hm l hl => ?_, h6⟩
    · rw [Array.all_eq_true] at h3
      have := h3 m (by omega)
      rw [getElem!_pos ds m (by omega)]
      simpa using this
    · have := h5 m hm l hl
      by_cases hlm : l = m
      · simp [hlm] at this ⊢
        exact this
      · simp [hlm] at this ⊢
        exact this
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨⟨⟨⟨h1, h2⟩, ?_⟩, h4⟩, fun m hm l hl => ?_⟩, h6⟩
    · rw [Array.all_eq_true]
      intro m hm
      have := h3 m (by omega)
      rw [getElem!_pos ds m hm] at this
      simpa using this
    · have := h5 m hm l hl
      by_cases hlm : l = m
      · simp [hlm] at this ⊢
        exact this
      · simp [hlm] at this ⊢
        exact this

theorem arr_ext! {a b : Array Nat} (hs : a.size = b.size) (h : ∀ l < a.size, a[l]! = b[l]!) :
    a = b := by
  refine Array.ext hs fun l h1 h2 => ?_
  have := h l h1
  rwa [getElem!_pos a l h1, getElem!_pos b l h2] at this

theorem swap_sum (a b : Nat → ZMod 5) (c : Nat → Nat → ZMod 5) :
    ∑ k ∈ Finset.range 7, a k * ∑ m ∈ Finset.range 7, b m * c m k =
      ∑ m ∈ Finset.range 7, b m * ∑ k ∈ Finset.range 7, c m k * a k := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem encode_congr {F G : Nat → Nat} (h : ∀ p < 828, F p % 5 = G p % 5) :
    encodeDigits F = encodeDigits G := by
  unfold encodeDigits
  refine congrArg ByteArray.mk (congrArg Array.ofFn (funext fun q => ?_))
  unfold code3
  rw [h _ (by omega), h _ (by omega), h _ (by omega)]

theorem cast_ite01 (c : Prop) [Decidable c] :
    (((if c then 1 else 0 : Nat) : Nat) : ZMod 5) = if c then 1 else 0 := by
  split <;> simp

theorem actKey_mapL {w S T L H CM RM ONE LV HV X D D' : Nat} {R piv : Array Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true)
    (hU : validM 5 (111 * S) L H (upOfD w S D) = true)
    (hU' : validM 5 (111 * S) L H (upOfD w S D') = true)
    (hR7 : validM 5 (111 * S) L H (lane7 w S R) = true)
    (hD : ∀ p < 826, fld(D, 4 * p, 15) < 5) (hD' : ∀ p < 826, fld(D', 4 * p, 15) < 5)
    (hRs : R.size = 49 ∧ ∀ t < 49, R[t]! < 5)
    (hpiv : rrefOK (CFSG.Sporadic.Ly.Native.keyRows (keyOfD D')) piv = true)
    (hst : mulR 5 w S 111 T L H CM RM X (upOfD w S D) =
      mulR 5 w S 111 T L H CM RM (upOfD w S D') (lane7 w S R))
    (hR : mul7 R (inv7 R) = id7 ())
    (hS : congr7 R (keyS (keyOfD D)) = keyS (keyOfD D')) :
    actKey (frTable (unpackL 111 w S X)) (keyOfD D) = some (keyOfD D') := by
  have hY := fun r (hr : r < 7) i (hi : i < 112) =>
    actYs_lane hD (unpackL 111 w S X) (D := D) hr hi
  have hYM : ∀ r < 7, ∀ i < 111,
      ((((actYs (frTable (unpackL 111 w S X)) (keyOfD D))[r]!).lane i : Nat) : ZMod 5) =
        ∑ m ∈ Finset.range 7, ((dF D' (111 * m + i) : Nat) : ZMod 5) *
          ((R[7 * m + r]! : Nat) : ZMod 5) := fun r hr i hi => by
    rw [(hY r hr i (by omega)).2]
    exact mat_ent hc hX hU hU' hR7 hD hD' hRs.2 hst hi hr
  have hY0 : ∀ r < 7, ((actYs (frTable (unpackL 111 w S X)) (keyOfD D))[r]!).lane 111 = 0 :=
    fun r hr => by
      have h := hY r hr 111 (by norm_num)
      refine nat_of_cast_zero h.1 ?_
      rw [h.2]
      refine Finset.sum_eq_zero fun j _ => ?_
      unfold CFSG.Sporadic.Ly.Native.ent
      rw [ite_eq_right (by omega), Nat.cast_zero, zero_mul]
  obtain ⟨P0, -, -, P1, P2, P3⟩ := rref_iff.1 hpiv
  have kr : ∀ m < 7, ∀ j < 112,
      ((CFSG.Sporadic.Ly.Native.keyRows (keyOfD D'))[m]!.get! j).toNat = dF D' (111 * m + j) :=
    fun m hm j hj => by
      rw [keyRows_get _ hm hj (by rw [keyDigit_keyOfD' hD' (by omega)]; have := dF_lt hD' (111 * m + j); omega),
        keyDigit_keyOfD' hD' (by omega)]
  have hRi : ∀ a < 7, ∀ b < 7, ∑ l ∈ Finset.range 7, ((R[7 * a + l]! : Nat) : ZMod 5) *
      (((inv7 R)[7 * l + b]! : Nat) : ZMod 5) = if a = b then 1 else 0 := by
    intro a ha b hb
    have h := congrArg (fun A : Array Nat => A[7 * a + b]!) hR
    unfold mul7 id7 at h
    rw [ofFn_get! _ (by omega), ofFn_get! _ (by omega)] at h
    dsimp only at h
    have e1 : (7 * a + b) / 7 = a := by omega
    have e2 : (7 * a + b) % 7 = b := by omega
    rw [e1, e2, fold_sum] at h
    have h' := congrArg (fun x : Nat => (x : ZMod 5)) h
    simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul] at h'
    rw [h']
    by_cases hab : a = b
    · simp [hab]
    · simp [hab]
  have hysz : (actYs (frTable (unpackL 111 w S X)) (keyOfD D)).size = 7 := by simp [actYs]
  have hdsk : ∀ k < 7, ((actYs (frTable (unpackL 111 w S X)) (keyOfD D)).map W14.digits)[k]! =
      ((actYs (frTable (unpackL 111 w S X)) (keyOfD D))[k]!).digits := fun k hk => by
    rw [get_mapR _ _ (by omega)]
  have hinc : ∀ a < 7, ∀ b < 7, a < b → piv[a]! < piv[b]! := by
    intro a ha b hb hab
    induction b with
    | zero => omega
    | succ b ih =>
      have h1 := (P1 b (by omega)).2
      rcases h1 with h1 | h1
      · omega
      · rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hab) with h | h
        · rw [h]
          exact h1
        · exact Nat.lt_trans (ih (by omega) h) h1
  obtain ⟨hpS, hpE⟩ := pivotsF_spec (ds := (actYs (frTable (unpackL 111 w S X)) (keyOfD D)).map W14.digits)
    (u := fun i m => ((dF D' (111 * m + i) : Nat) : ZMod 5)) (Rr := fun m k => ((R[7 * m + k]! : Nat) : ZMod 5))
    (Ri := fun l b => (((inv7 R)[7 * l + b]! : Nat) : ZMod 5)) (piv := fun l => piv[l]!)
    (fun i hi k hk => by
      rw [hdsk k hk, (digits_spec _).2 i (by omega),
        Nat.mod_eq_of_lt (hY k hk i (by omega)).1]
      exact ⟨(hY k hk i (by omega)).1, hYM k hk i hi⟩)
    (fun m hm j hj => by
      have h := P3 m hm j hj
      rw [kr m hm j (by have := (P1 m hm).1; omega)] at h
      rw [h, Nat.cast_zero])
    (fun l hl m hm => by
      have h := P2 m hm l hl
      rw [kr m hm _ (by have := (P1 l hl).1; omega)] at h
      rw [h, cast_ite01])
    hinc (P1 6 (by norm_num)).1 hRi
  have hpv : pivots ((actYs (frTable (unpackL 111 w S X)) (keyOfD D)).map W14.digits) = piv := by
    rw [pivots_eq]
    exact arr_ext! (by rw [hpS, P0]) fun l hl => hpE l (by rw [hpS] at hl; exact hl)
  have hP : pivMat (actYs (frTable (unpackL 111 w S X)) (keyOfD D)) piv = R := by
    have hsz : (pivMat (actYs (frTable (unpackL 111 w S X)) (keyOfD D)) piv).size = 49 := by
      simp [pivMat]
    refine arr_ext! (by rw [hsz, hRs.1]) fun t ht' => ?_
    have ht : t < 49 := by rw [hsz] at ht'; exact ht'
    unfold pivMat
    rw [ofFn_get! _ ht]
    dsimp only
    refine eq_of_cast (Nat.mod_lt _ (by norm_num)) (hRs.2 t ht) ?_
    rw [ZMod.natCast_mod, hYM (t % 7) (Nat.mod_lt _ (by norm_num)) _ (P1 (t / 7) (by omega)).1]
    rw [Finset.sum_congr rfl fun m hm => by
      rw [← kr m (Finset.mem_range.1 hm) _ (by have := (P1 (t / 7) (by omega)).1; omega),
        P2 m (Finset.mem_range.1 hm) (t / 7) (by omega), cast_ite01]]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq (Finset.range 7) (t / 7), ite_eq_left (Finset.mem_range.2 (by omega)),
      Nat.div_add_mod]
  have hylt : ∀ k < 7, ∀ i < 112, ((actYs (frTable (unpackL 111 w S X)) (keyOfD D))[k]!).lane i < 5 :=
    fun k hk i hi => (hY k hk i hi).1
  have hus : ∀ m < 7, ∀ j < 111,
      ((combine (actYs (frTable (unpackL 111 w S X)) (keyOfD D)) (inv7 R))[m]!.get! j).toNat =
        dF D' (111 * m + j) := by
    intro m hm j hj
    rw [(combine_spec _ (inv7 R) hylt hm).2 j (by omega)]
    refine eq_of_cast (Nat.mod_lt _ (by norm_num)) (dF_lt hD' _) ?_
    rw [ZMod.natCast_mod, Nat.cast_sum]
    simp only [Nat.cast_mul, ZMod.natCast_mod]
    rw [Finset.sum_congr rfl fun k hk => by rw [hYM k (Finset.mem_range.1 hk) j hj]]
    rw [swap_sum]
    rw [Finset.sum_congr rfl fun m' hm' => by rw [hRi m' (Finset.mem_range.1 hm') m hm]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' (Finset.range 7) m, ite_eq_left (Finset.mem_range.2 hm)]
  have hrref : rrefOK (combine (actYs (frTable (unpackL 111 w S X)) (keyOfD D)) (inv7 R)) piv =
      true := by
    refine rref_iff.2 ⟨P0, by simp [combine], fun m hm => (combine_spec _ (inv7 R) hylt hm).1, P1,
      fun m hm l hl => ?_, fun m hm j hj => ?_⟩
    · rw [hus m hm _ (P1 l hl).1, ← kr m hm _ (by have := (P1 l hl).1; omega)]
      exact P2 m hm l hl
    · have hj' : j < 111 := Nat.lt_of_lt_of_le hj (P1 m hm).1.le
      rw [hus m hm j hj', ← kr m hm j (by omega)]
      exact P3 m hm j hj
  unfold actKey
  dsimp only
  rw [hpv]
  rw [hP]
  rw [ite_eq_left hrref]
  rw [hS]
  refine congrArg some ?_
  have hF : ∀ p < 828, keyFun (combine (actYs (frTable (unpackL 111 w S X)) (keyOfD D)) (inv7 R))
      (keyS (keyOfD D')) p % 5 = (if p < 826 then fld(D', 4 * p, 15) else 0) % 5 := by
    intro p hp
    unfold keyFun
    by_cases h1 : p < 777
    · rw [ite_eq_left h1, hus (p / 111) (by omega) (p % 111) (Nat.mod_lt _ (by norm_num))]
      have e : 111 * (p / 111) + p % 111 = p := Nat.div_add_mod p 111
      rw [e]
      rfl
    · rw [ite_eq_right h1]
      by_cases h2 : p < 826
      · rw [ite_eq_left h2, keyS_get _ (by omega), keyDigit_keyOfD D' (by omega)]
        have e : 777 + (p - 777) = p := by omega
        rw [e, Nat.mod_mod]
        rfl
      · rw [ite_eq_right h2, ite_eq_right h2]
  exact encode_congr hF

end CFSG.KS.SporSch.LyK

end
