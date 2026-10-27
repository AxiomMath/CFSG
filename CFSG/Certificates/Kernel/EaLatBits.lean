module

public import Certificates.Data.Kernel.EaLat
public import CFSG.Certificates.Kernel.EaLatSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.LocalQTPermSound
import CFSG.Certificates.Kernel.Spor.PK.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.LawfulXor.Basic
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.EaLat

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos

@[expose] noncomputable def recP (REC : ℕ → ℕ) (f : ℕ) : ℕ := fld (REC f) 0 65535

@[expose] noncomputable def recK (REC : ℕ → ℕ) (f : ℕ) : ℕ := fld (REC f) 16 255

@[expose] noncomputable def recSz (REC : ℕ → ℕ) (f : ℕ) : ℕ := fld (REC f) 24 255

@[expose] noncomputable def recCcM (REC : ℕ → ℕ) (f : ℕ) : ℕ := fld (REC f) 320 m256

@[expose] noncomputable def recEnt (REC : ℕ → ℕ) (f t : ℕ) : ℕ := fld (REC f >>> 576) (8 * t) 255

@[expose] noncomputable def prb (PR : ℕ → ℕ) (i j : ℕ) : ℕ := fld (PR i) (8 * j) 255

@[expose] noncomputable def recS (REC : ℕ → ℕ) (f : ℕ) : Finset ℕ := (Finset.range (recSz REC f)).image (recEnt REC f)

@[expose] noncomputable def recC (n : ℕ) (REC : ℕ → ℕ) (f : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun j => (recCcM REC f).testBit j

variable {G : Type*} [Group G] [DecidableEq G]

theorem bit_eq (m i : ℕ) : bit m i = m.testBit i := CFSG.KS.PK.hasBit_eq m i

section Facts

open CFSG.KC.LQT

theorem uniAt_facts {M : ℕ → ℕ → ℕ} {one n : ℕ} {V CM PR : ℕ → ℕ} {ncw : ℕ → ℕ → ℕ → Bool}
    {i : ℕ} (h : uniAt M one n V CM PR ncw i = true) :
    V i ≠ one ∧ M (V i) (V i) = one ∧ (CM i).testBit i = true ∧ (i + 1 < n → V i < V (i + 1)) ∧
      ∀ j < i, pairAt M n V CM PR ncw (V i) (CM i) (PR i) i j = true := by
  unfold uniAt at h
  rw [P.letB_eq, P.letB_eq, P.letB_eq] at h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  obtain ⟨ha, h1⟩ := P.andB_iff.1 h1
  obtain ⟨hb, h1⟩ := P.andB_iff.1 h1
  obtain ⟨hc, -⟩ := P.andB_iff.1 h1
  obtain ⟨he, hf⟩ := P.andB_iff.1 h2
  refine ⟨fun e => P.notB_iff.1 ha (P.beq_iff.2 e), P.beq_iff.1 hb, ?_,
    fun hs => P.blt_iff.1 (P.impB_iff.1 he (P.blt_iff.2 hs)), (P.allN_iff _ _).1 hf⟩
  rw [← bit_eq]
  exact hc

theorem pairAt_facts {M : ℕ → ℕ → ℕ} {n : ℕ} {V CM PR : ℕ → ℕ} {ncw : ℕ → ℕ → ℕ → Bool}
    {i j : ℕ} (h : pairAt M n V CM PR ncw (V i) (CM i) (PR i) i j = true) :
    prb PR i j = prb PR j i ∧
      ((CM i).testBit j = true → (CM j).testBit i = true ∧ prb PR i j < n ∧
        M (V i) (V j) = V (prb PR i j) ∧ M (V j) (V i) = V (prb PR i j)) ∧
      ((CM i).testBit j = false → (CM j).testBit i = false ∧
        ncw (V j) (V i) (prb PR i j) = true) := by
  unfold pairAt at h
  rw [P.letB_eq, P.letB_eq, P.letB_eq] at h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  refine ⟨P.beq_iff.1 h1, fun hb => ?_, fun hb => ?_⟩
  · rw [← bit_eq] at hb
    simp only [hb] at h2
    obtain ⟨c1, c2⟩ := P.andB_iff.1 h2
    obtain ⟨c3, c4⟩ := P.andB_iff.1 c2
    rw [P.letB_eq] at c4
    obtain ⟨c5, c6⟩ := P.andB_iff.1 c4
    rw [← bit_eq]
    exact ⟨c1, P.blt_iff.1 c3, P.beq_iff.1 c5, P.beq_iff.1 c6⟩
  · rw [← bit_eq] at hb
    simp only [hb] at h2
    obtain ⟨c1, c2⟩ := P.andB_iff.1 h2
    rw [← bit_eq]
    exact ⟨Bool.eq_false_iff.2 (P.notB_iff.1 c1), c2⟩

end Facts

theorem uni_of_checks {n : ℕ} (hn : n ≤ 255) {M : ℕ → ℕ → ℕ} {one : ℕ} {enc : G → ℕ}
    (henc : ClosEnc enc M one) (v : ℕ → G) {V CM PR : ℕ → ℕ} {ncw : ℕ → ℕ → ℕ → Bool}
    (hV : ∀ i < n, enc (v i) = V i) {W : ℕ}
    (hncw : ∀ x y : G, ∀ w < W, ncw (enc x) (enc y) w = true → x * y ≠ y * x)
    (hW : ∀ i < n, ∀ j < i, bit (CM i) j = false → prb PR i j < W)
    (hu : ∀ i < n, uniAt M one n V CM PR ncw i = true) :
    Uni n v (prb PR) ∧ ∀ i < n, ∀ j < n, ((CM i).testBit j ↔ v i * v j = v j * v i) := by
  have hA := fun i hi => uniAt_facts (hu i hi)
  have hP := fun i (hi : i < n) j (hj : j < i) => pairAt_facts ((hA i hi).2.2.2.2 j hj)
  have hmono : ∀ a b, a < b → b < n → V a < V b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
      · exact (ih h (by omega)).trans ((hA b (by omega)).2.2.2.1 hb)
      · exact (hA a (by omega)).2.2.2.1 hb
  have hcode : ∀ {x y : G}, enc x = enc y → x = y := fun e => henc.inj e
  have hcomm : ∀ i < n, ∀ j < i, ((CM i).testBit j = true ↔ v i * v j = v j * v i) ∧
      (CM j).testBit i = (CM i).testBit j := by
    intro i hi j hj
    obtain ⟨-, ht, hf⟩ := hP i hi j hj
    cases hb : (CM i).testBit j
    · obtain ⟨c1, c2⟩ := hf hb
      have hw := hW i hi j hj (by rw [bit_eq]; exact hb)
      rw [← hV j (by omega), ← hV i hi] at c2
      refine ⟨⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h.symm (hncw _ _ _ hw c2)⟩, c1⟩
    · obtain ⟨c1, -, c3, c4⟩ := ht hb
      refine ⟨⟨fun _ => hcode ?_, fun _ => rfl⟩, c1⟩
      rw [henc.enc_mul, henc.enc_mul, hV i hi, hV j (by omega), c3, c4]
  have hbit : ∀ i < n, ∀ j < n, ((CM i).testBit j = true ↔ v i * v j = v j * v i) := by
    intro i hi j hj
    rcases Nat.lt_trichotomy j i with h | rfl | h
    · exact (hcomm i hi j h).1
    · exact ⟨fun _ => rfl, fun _ => (hA _ hi).2.2.1⟩
    · rw [(hcomm j hj i h).2, (hcomm j hj i h).1]
      exact ⟨Eq.symm, Eq.symm⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hbit⟩
  · intro a ha b hb e
    have e' : V a = V b := by rw [← hV a ha, ← hV b hb, e]
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd e' (hmono a b h hb).ne
    · exact h
    · exact absurd e' (hmono b a h ha).ne'
  · intro i hi e
    exact (hA i hi).1 (by rw [← hV i hi, e, henc.enc_one])
  · intro i hi
    apply hcode
    rw [henc.enc_mul, henc.enc_one, hV i hi]
    exact (hA i hi).2.1
  · intro i hi j hj hij hc
    rcases Nat.lt_or_gt_of_ne hij with h | h
    ·
      obtain ⟨hs, ht, -⟩ := hP j hj i h
      have hb : (CM j).testBit i = true := (hcomm j hj i h).1.2 hc.symm
      obtain ⟨-, c2, c3, -⟩ := ht hb
      refine ⟨hs ▸ c2, hcode ?_⟩
      rw [← hs, hV _ c2, ← c3, ← hV i hi, ← hV j hj, ← henc.enc_mul, hc]
    · obtain ⟨-, ht, -⟩ := hP i hi j h
      obtain ⟨-, c2, c3, -⟩ := ht ((hcomm i hi j h).1.2 hc)
      refine ⟨c2, hcode ?_⟩
      rw [hV _ c2, ← c3, ← hV i hi, ← hV j hj, ← henc.enc_mul]

section RecFacts

open CFSG.KC.LQT

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by
  cases y <;> rfl

theorem testBit_fld255 (x o b : ℕ) :
    (fld x o 255).testBit b = (decide (b < 8) && x.testBit (o + b)) := by
  have e : (255 : ℕ) = 2 ^ 8 - 1 := rfl
  unfold fld
  change ((x >>> o) &&& 255).testBit b = _
  rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem fld255_lt (x o : ℕ) : fld x o 255 < 256 := by
  unfold fld
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem testBit_ge_of_lt {y b : ℕ} (hy : y < 256) (hb : 8 ≤ b) : y.testBit b = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (by
    calc 256 = 2 ^ 8 := rfl
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hb))

theorem fld255_eq {x o y : ℕ} (hy : y < 256) (h : ∀ b < 8, x.testBit (o + b) = y.testBit b) :
    fld x o 255 = y := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld255]
  by_cases hb : b < 8
  · simp [hb, h b hb]
  · have e := testBit_ge_of_lt hy (b := b) (by omega)
    simp [hb, e]

theorem testBit_shl_byte {y : ℕ} (hy : y < 256) (m t : ℕ) {b : ℕ} (hb : b < 8) :
    (y <<< (8 * m)).testBit (8 * t + b) = (decide (t = m) && y.testBit b) := by
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy t m with h | rfl | h
  · have h1 : ¬ 8 * t + b ≥ 8 * m := by omega
    simp [h1, Nat.ne_of_lt h]
  · simp [show 8 * t + b - 8 * t = b by omega]
  · rw [testBit_ge_of_lt hy (by omega)]
    simp [Nat.ne_of_gt h]

theorem shl_lt {y : ℕ} (hy : y < 256) {m j : ℕ} (hm : 8 * m + 8 ≤ j) : y <<< (8 * m) < 2 ^ j := by
  rw [Nat.shiftLeft_eq]
  calc y * 2 ^ (8 * m) < 2 ^ 8 * 2 ^ (8 * m) := Nat.mul_lt_mul_of_pos_right hy (Nat.two_pow_pos _)
    _ = 2 ^ (8 * m + 8) := by rw [← Nat.pow_add, Nat.add_comm]
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hm

theorem rec_or_testBit (acc : ℕ) (s : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (hs : ∀ t x, s t x = x ||| g t)
    (i : ℕ) : ∀ m, (Nat.rec (motive := fun _ => ℕ) acc s m).testBit i = true ↔
      acc.testBit i = true ∨ ∃ t < m, (g t).testBit i = true := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    change (s m (Nat.rec (motive := fun _ => ℕ) acc s m)).testBit i = true ↔ _
    rw [hs, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro ((h | ⟨t, ht, h⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨t, by omega, h⟩
      · exact Or.inr ⟨m, by omega, h⟩
    · rintro (h | ⟨t, ht, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · exact Or.inl (Or.inr ⟨t, ht, h⟩)
        · exact Or.inr h

theorem prodW_testBit (prk elp szp acc i : ℕ) :
    (prodW prk elp szp acc).testBit i = true ↔ acc.testBit i = true ∨ ∃ t < szp,
      ((fld prk (8 * fld elp (8 * t) 255) 255 <<< (8 * (szp + 1 + t))) |||
        (1 <<< (512 + fld prk (8 * fld elp (8 * t) 255) 255))).testBit i = true :=
  rec_or_testBit acc _ _ (fun t x => by simp only [letN_eq] <;> rfl) i szp

theorem covW_testBit (NF : ℕ) (REC : ℕ → ℕ) (mk sz ch nc i : ℕ) :
    (covW NF REC mk sz ch nc).testBit i = true ↔ (0 : ℕ).testBit i = true ∨ ∃ t < nc,
      (Bool.rec (motive := fun _ => ℕ) (1 <<< 256) (fld (REC (fld ch (16 * t) 65535)) 64 m256)
        (andB (Nat.blt (fld ch (16 * t) 65535) NF)
          (andB (Nat.beq (mk &&& fld (REC (fld ch (16 * t) 65535)) 64 m256) mk)
            (Nat.beq (fld (REC (fld ch (16 * t) 65535)) 24 255) (sz + sz + 1))))).testBit i = true :=
  rec_or_testBit 0 _ _ (fun t x => by simp only [letN_eq] <;> rfl) i nc

theorem ea_add_eq_xor : ∀ x y : ℕ, x &&& y = 0 → x + y = x ^^^ y := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro y h
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have h2 : x / 2 &&& y / 2 = 0 := by rw [← Nat.and_div_two, h]
      have hm : x % 2 &&& y % 2 = 0 := by
        have := congrArg (· % 2 ^ 1) h
        simp only [Nat.and_mod_two_pow, Nat.zero_mod] at this
        simpa using this
      have e1 := ih (x / 2) (Nat.div_lt_self hx (by norm_num)) (y / 2) h2
      have ex : x ^^^ y = 2 * ((x ^^^ y) / 2) + (x ^^^ y) % 2 := (Nat.div_add_mod _ 2).symm
      have hxm : (x ^^^ y) % 2 = x % 2 + y % 2 := by
        have e2 := Nat.xor_mod_two_pow (a := x) (b := y) (n := 1)
        simp only [pow_one] at e2
        rw [e2]
        rcases Nat.mod_two_eq_zero_or_one x with a | a <;>
          rcases Nat.mod_two_eq_zero_or_one y with b | b <;> rw [a, b] at hm ⊢
        · rfl
        · rfl
        · rfl
        · exact absurd hm (by decide)
      rw [ex, Nat.xor_div_two, ← e1, hxm]
      omega

theorem ea_testBit_sub_and (m K i : ℕ) :
    (m - (m &&& K)).testBit i = (m.testBit i && !K.testBit i) := by
  have hd : (m ^^^ (m &&& K)) &&& (m &&& K) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    cases m.testBit j <;> cases K.testBit j <;> rfl
  have hs := ea_add_eq_xor _ _ hd
  have hx : (m ^^^ (m &&& K)) ^^^ (m &&& K) = m := by
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hx] at hs
  have e : m - (m &&& K) = m ^^^ (m &&& K) := by omega
  rw [e, Nat.testBit_xor, Nat.testBit_and]
  cases m.testBit i <;> cases K.testBit i <;> rfl

theorem baseOK_facts {n : ℕ} {REC : ℕ → ℕ} (h : baseOK n REC = true) :
    recSz REC 0 = 0 ∧ fld (REC 0) 64 m256 = 0 ∧ recCcM REC 0 = (1 <<< n) - 1 ∧
      REC 0 >>> 576 = 0 := by
  unfold baseOK at h
  rw [P.letB_eq] at h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  obtain ⟨h2, h3⟩ := P.andB_iff.1 h2
  obtain ⟨h3, h4⟩ := P.andB_iff.1 h3
  refine ⟨fld255_eq (by norm_num) fun b hb => ?_, P.beq_iff.1 h2, P.beq_iff.1 h3, P.beq_iff.1 h4⟩
  have e : (REC 0 >>> 0) &&& (2 ^ 32 - 1) = 0 := P.beq_iff.1 h1
  have e2 := congrArg (fun x => x.testBit (24 + b)) e
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Nat.zero_testBit, Nat.zero_add] at e2
  rw [Nat.zero_testBit]
  simpa [show 24 + b < 32 by omega] using e2

theorem genAt_facts {n : ℕ} {REC CM PR : ℕ → ℕ} {f : ℕ} (h : genAt n REC CM PR f = true) :
    recP REC f < f ∧ recK REC f < n ∧ recSz REC f < 64 ∧
    recSz REC f = recSz REC (recP REC f) + recSz REC (recP REC f) + 1 ∧
    REC f >>> 576 < 1 <<< (8 * recSz REC f) ∧
    (fld (REC (recP REC f)) 64 m256).testBit (recK REC f) = false ∧
    (recCcM REC (recP REC f)).testBit (recK REC f) = true ∧
    recCcM REC f = recCcM REC (recP REC f) &&& CM (recK REC f) ∧
    prodW (PR (recK REC f)) (REC (recP REC f) >>> 576) (recSz REC (recP REC f))
      ((REC (recP REC f) >>> 576 ||| recK REC f <<< (8 * recSz REC (recP REC f))) |||
        (fld (REC (recP REC f)) 64 m256 ||| 1 <<< recK REC f) <<< 512) =
      REC f >>> 576 ||| fld (REC f) 64 m256 <<< 512 := by
  unfold genAt at h
  simp only [P.letB_eq] at h
  obtain ⟨h1, h2⟩ := P.andB_iff.1 h
  obtain ⟨hp, h1⟩ := P.andB_iff.1 h1
  obtain ⟨hk, h1⟩ := P.andB_iff.1 h1
  obtain ⟨hsz, h1⟩ := P.andB_iff.1 h1
  obtain ⟨hsz2, hel⟩ := P.andB_iff.1 h1
  obtain ⟨h3, hpw⟩ := P.andB_iff.1 h2
  obtain ⟨hm, h3⟩ := P.andB_iff.1 h3
  obtain ⟨hc, hcc⟩ := P.andB_iff.1 h3
  refine ⟨P.blt_iff.1 hp, P.blt_iff.1 hk, P.blt_iff.1 hsz, P.beq_iff.1 hsz2, P.blt_iff.1 hel, ?_,
    ?_, P.beq_iff.1 hcc, P.beq_iff.1 hpw⟩
  · rw [← bit_eq]
    exact Bool.eq_false_iff.2 (P.notB_iff.1 hm)
  · rw [← bit_eq]
    exact hc

theorem covAt_facts {NF : ℕ} {REC CH : ℕ → ℕ} {f : ℕ} (h : covAt NF REC CH f = true) :
    ∀ i < 256, (recCcM REC f).testBit i = true → (fld (REC f) 64 m256).testBit i = false →
      ∃ c < NF, fld (REC f) 64 m256 &&& fld (REC c) 64 m256 = fld (REC f) 64 m256 ∧
        recSz REC c = recSz REC f + recSz REC f + 1 ∧ (fld (REC c) 64 m256).testBit i = true := by
  intro i hi hcc hmk
  unfold covAt at h
  simp only [P.letB_eq] at h
  obtain ⟨-, h2⟩ := P.andB_iff.1 h
  have hI := P.beq_iff.1 h2
  have hIi : (recCcM REC f - (recCcM REC f &&& fld (REC f) 64 m256)).testBit i = true := by
    rw [ea_testBit_sub_and, hcc, hmk]
    rfl
  have hacc := congrArg (fun x => x.testBit i) hI
  change ((recCcM REC f - (recCcM REC f &&& fld (REC f) 64 m256)) &&&
    covW NF REC (fld (REC f) 64 m256) (recSz REC f) (CH f) (fld (REC f) 32 255)).testBit i =
    (recCcM REC f - (recCcM REC f &&& fld (REC f) 64 m256)).testBit i at hacc
  rw [Nat.testBit_and, hIi, Bool.true_and, covW_testBit] at hacc
  obtain h0 | ⟨t, -, hg⟩ := hacc
  · simp at h0
  · cases hcond : andB (Nat.blt (fld (CH f) (16 * t) 65535) NF)
        (andB (Nat.beq (fld (REC f) 64 m256 &&& fld (REC (fld (CH f) (16 * t) 65535)) 64 m256)
          (fld (REC f) 64 m256))
          (Nat.beq (fld (REC (fld (CH f) (16 * t) 65535)) 24 255) (recSz REC f + recSz REC f + 1)))
    · rw [hcond] at hg
      change (1 <<< 256 : ℕ).testBit i = true at hg
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hg
      exact absurd (of_decide_eq_true hg) (by omega)
    · rw [hcond] at hg
      obtain ⟨c1, c2⟩ := P.andB_iff.1 hcond
      obtain ⟨c2, c3⟩ := P.andB_iff.1 c2
      exact ⟨_, P.blt_iff.1 c1, P.beq_iff.1 c2, P.beq_iff.1 c3, hg⟩

theorem gen_split {el mk elp mkp k szp sz : ℕ} (c : ℕ → ℕ) (hc : ∀ s, c s < 256) (hk : k < 256)
    (hszp : sz = szp + szp + 1) (hsz : sz < 64) (hel : el < 2 ^ (8 * sz))
    (help : elp < 2 ^ (8 * szp))
    (h : ∀ i, (el ||| mk <<< 512).testBit i = true ↔
      ((elp ||| k <<< (8 * szp)) ||| (mkp ||| 1 <<< k) <<< 512).testBit i = true ∨
        ∃ t < szp, ((c t <<< (8 * (szp + 1 + t))) ||| (1 <<< (512 + c t))).testBit i = true) :
    (∀ t < sz, fld el (8 * t) 255 =
      if t < szp then fld elp (8 * t) 255 else if t = szp then k else c (t - szp - 1)) ∧
    (∀ x, mk.testBit x = true ↔ mkp.testBit x = true ∨ x = k ∨ ∃ s < szp, c s = x) := by
  have hlow : ∀ i < 504, (el.testBit i = true ↔ elp.testBit i = true ∨
      (k <<< (8 * szp)).testBit i = true ∨
      ∃ t < szp, (c t <<< (8 * (szp + 1 + t))).testBit i = true) := by
    intro i hi
    have e := h i
    have hm1 : (mk <<< 512).testBit i = false := by
      rw [Nat.testBit_shiftLeft, decide_eq_false (show ¬ i ≥ 512 by omega), Bool.false_and]
    have hm2 : ((mkp ||| 1 <<< k) <<< 512).testBit i = false := by
      rw [Nat.testBit_shiftLeft, decide_eq_false (show ¬ i ≥ 512 by omega), Bool.false_and]
    have hm3 : ∀ t, (1 <<< (512 + c t)).testBit i = false := fun t => by
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
      exact decide_eq_false (by omega)
    simp only [Nat.testBit_or, hm1, hm2, hm3, Bool.or_false, Bool.or_eq_true, or_assoc] at e
    exact e
  have hhigh : ∀ x, (mk.testBit x = true ↔ mkp.testBit x = true ∨ x = k ∨
      ∃ s < szp, c s = x) := by
    intro x
    have e := h (512 + x)
    have h1 : el.testBit (512 + x) = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hel
      (Nat.pow_le_pow_right (by omega) (by omega)))
    have h2 : elp.testBit (512 + x) = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le help
      (Nat.pow_le_pow_right (by omega) (by omega)))
    have h3 : (k <<< (8 * szp)).testBit (512 + x) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (shl_lt hk (j := 8 * szp + 8) le_rfl)
        (Nat.pow_le_pow_right (by omega) (by omega)))
    have h4 : ∀ t < szp, (c t <<< (8 * (szp + 1 + t))).testBit (512 + x) = false := fun t ht =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (shl_lt (hc t) (j := 8 * (szp + 1 + t) + 8) le_rfl)
        (Nat.pow_le_pow_right (by omega) (by omega)))
    have hL : (el ||| mk <<< 512).testBit (512 + x) = mk.testBit x := by
      rw [Nat.testBit_or, h1, Bool.false_or, Nat.testBit_shiftLeft, Nat.add_sub_cancel_left]
      simp
    have hA : ((elp ||| k <<< (8 * szp)) ||| (mkp ||| 1 <<< k) <<< 512).testBit (512 + x) =
        (mkp.testBit x || decide (k = x)) := by
      rw [Nat.testBit_or, Nat.testBit_or, h2, h3, Bool.false_or, Bool.false_or,
        Nat.testBit_shiftLeft, Nat.add_sub_cancel_left, Nat.testBit_or, Nat.one_shiftLeft,
        Nat.testBit_two_pow]
      simp
    have hT : ∀ t < szp, ((c t <<< (8 * (szp + 1 + t))) ||| (1 <<< (512 + c t))).testBit (512 + x) =
        decide (c t = x) := by
      intro t ht
      rw [Nat.testBit_or, h4 t ht, Bool.false_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp
    rw [hL, hA] at e
    rw [e]
    constructor
    · rintro (e1 | ⟨t, ht, e1⟩)
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at e1
        rcases e1 with e1 | e1
        · exact Or.inl e1
        · exact Or.inr (Or.inl e1.symm)
      · rw [hT t ht] at e1
        exact Or.inr (Or.inr ⟨t, ht, of_decide_eq_true e1⟩)
    · rintro (e1 | rfl | ⟨t, ht, rfl⟩)
      · left
        simp [e1]
      · left
        simp
      · right
        refine ⟨t, ht, ?_⟩
        rw [hT t ht]
        simp
  refine ⟨fun t ht => ?_, hhigh⟩
  have hb8 : ∀ b < 8, 8 * t + b < 504 := fun b hb => by omega
  split_ifs with h1 h2
  · refine fld255_eq (fld255_lt _ _) fun b hb => Bool.eq_iff_iff.2 ?_
    rw [hlow _ (hb8 b hb), testBit_fld255, testBit_shl_byte hk _ _ hb]
    simp only [show decide (b < 8) = true from decide_eq_true hb, Bool.true_and,
      show ¬ t = szp by omega, decide_false, Bool.false_and, Bool.false_eq_true, false_or]
    constructor
    · rintro (e | ⟨s, hs, e⟩)
      · exact e
      · rw [testBit_shl_byte (hc s) _ _ hb] at e
        simp [show ¬ t = szp + 1 + s by omega] at e
    · exact Or.inl
  · subst h2
    refine fld255_eq hk fun b hb => Bool.eq_iff_iff.2 ?_
    rw [hlow _ (hb8 b hb), testBit_shl_byte hk _ _ hb, Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le help (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp only [decide_true, Bool.true_and, Bool.false_eq_true, false_or]
    constructor
    · rintro (e | ⟨s, hs, e⟩)
      · exact e
      · rw [testBit_shl_byte (hc s) _ _ hb] at e
        simp [show ¬ t = t + 1 + s by omega] at e
    · exact Or.inl
  · refine fld255_eq (hc _) fun b hb => Bool.eq_iff_iff.2 ?_
    rw [hlow _ (hb8 b hb), testBit_shl_byte hk _ _ hb, Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le help (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp only [show ¬ t = szp from h2, decide_false, Bool.false_and, Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨s, hs, e⟩
      rw [testBit_shl_byte (hc s) _ _ hb] at e
      simp only [Bool.and_eq_true, decide_eq_true_eq] at e
      obtain ⟨e1, e2⟩ := e
      rw [show t - szp - 1 = s by omega]
      exact e2
    · intro e
      refine ⟨t - szp - 1, by omega, ?_⟩
      rw [show 8 * (szp + 1 + (t - szp - 1)) = 8 * t by omega]
      rw [Nat.testBit_shiftLeft]
      simp only [ge_iff_le, Nat.le_add_right, decide_true, Bool.true_and, Nat.add_sub_cancel_left]
      exact e

end RecFacts

theorem recs_of_checks {n NF : ℕ} (hn : n ≤ 255) (v : ℕ → G) {REC CM PR CH : ℕ → ℕ}
    (hcm : ∀ i < n, ∀ j < n, ((CM i).testBit j ↔ v i * v j = v j * v i))
    (hb : baseOK n REC = true) (hg : ∀ f, 0 < f → f < NF → genAt n REC CM PR f = true)
    (hc : ∀ f < NF, covAt NF REC CH f = true) :
    Recs n NF v (prb PR) (recS REC) (recC n REC) (recP REC) (recK REC) (recSz REC) := by
  obtain ⟨hsz0, hmk0, hcc0, hel0⟩ := baseOK_facts hb
  have hS0 : recS REC 0 = ∅ := by
    unfold recS
    rw [hsz0, Finset.range_zero, Finset.image_empty]
  have hSf : ∀ f, 0 < f → f < NF → REC (recP REC f) >>> 576 < 2 ^ (8 * recSz REC (recP REC f)) →
      recS REC f = insert (recK REC f) (recS REC (recP REC f) ∪
        (recS REC (recP REC f)).image (prb PR (recK REC f))) ∧
      ∀ x, ((fld (REC f) 64 m256).testBit x = true ↔
        (fld (REC (recP REC f)) 64 m256).testBit x = true ∨ x = recK REC f ∨
          ∃ s < recSz REC (recP REC f), prb PR (recK REC f) (recEnt REC (recP REC f) s) = x) := by
    intro f hf0 hf help
    obtain ⟨-, hk, hsz, hsz2, hel, -, -, -, heq⟩ := genAt_facts (hg f hf0 hf)
    obtain ⟨hbytes, hmask⟩ := gen_split (el := REC f >>> 576) (mk := fld (REC f) 64 m256)
      (elp := REC (recP REC f) >>> 576) (mkp := fld (REC (recP REC f)) 64 m256) (k := recK REC f)
      (szp := recSz REC (recP REC f)) (sz := recSz REC f)
      (fun s => prb PR (recK REC f) (recEnt REC (recP REC f) s)) (fun s => fld255_lt _ _)
      (by omega) hsz2 hsz (by rw [← Nat.one_shiftLeft]; exact hel) help
      (fun i => by rw [← heq]; exact prodW_testBit _ _ _ _ _)
    refine ⟨?_, hmask⟩
    ext x
    simp only [recS, Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have e : recEnt REC f t = _ := hbytes t ht
      rw [e]
      split_ifs with h1 h2
      · exact Or.inr (Or.inl ⟨t, h1, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨_, ⟨t - recSz REC (recP REC f) - 1, by omega, rfl⟩, rfl⟩)
    · rintro (rfl | ⟨t, ht, rfl⟩ | ⟨_, ⟨s, hs, rfl⟩, rfl⟩)
      · refine ⟨recSz REC (recP REC f), by omega, ?_⟩
        have e : recEnt REC f _ = _ := hbytes _ (show recSz REC (recP REC f) < recSz REC f by omega)
        rw [e, if_neg (Nat.lt_irrefl _), if_pos rfl]
      · refine ⟨t, by omega, ?_⟩
        have e : recEnt REC f t = _ := hbytes t (by omega)
        rw [e, if_pos ht]
        rfl
      · refine ⟨recSz REC (recP REC f) + 1 + s, by omega, ?_⟩
        have e : recEnt REC f _ = _ := hbytes _
          (show recSz REC (recP REC f) + 1 + s < recSz REC f by omega)
        rw [e, if_neg (by omega), if_neg (by omega),
          show recSz REC (recP REC f) + 1 + s - recSz REC (recP REC f) - 1 = s by omega]
  have hinv : ∀ f < NF, (∀ x, (fld (REC f) 64 m256).testBit x = true ↔ x ∈ recS REC f) ∧
      REC f >>> 576 < 2 ^ (8 * recSz REC f) := by
    intro f
    induction f using Nat.strong_induction_on with
    | _ f ih =>
      intro hf
      rcases Nat.eq_zero_or_pos f with rfl | hf0
      · refine ⟨fun x => ?_, by rw [hel0, hsz0]; exact Nat.one_pos⟩
        rw [hmk0, hS0, Nat.zero_testBit]
        simp
      · obtain ⟨hp, -, -, -, hel, -, -, -, -⟩ := genAt_facts (hg f hf0 hf)
        obtain ⟨ihm, ihel⟩ := ih _ hp (hp.trans hf)
        obtain ⟨hS, hmask⟩ := hSf f hf0 hf ihel
        refine ⟨fun x => ?_, by rw [← Nat.one_shiftLeft]; exact hel⟩
        rw [hmask x, ihm x, hS]
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        constructor
        · rintro (h | rfl | ⟨s, hs, rfl⟩)
          · exact Or.inr (Or.inl h)
          · exact Or.inl rfl
          · refine Or.inr (Or.inr ⟨_, ?_, rfl⟩)
            exact Finset.mem_image.2 ⟨s, Finset.mem_range.2 hs, rfl⟩
        · rintro (rfl | h | ⟨a, ha, rfl⟩)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl h
          · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ha
            exact Or.inr (Or.inr ⟨s, Finset.mem_range.1 hs, rfl⟩)
  refine ⟨hS0, ?_, hsz0, fun f hf0 hf => (genAt_facts (hg f hf0 hf)).1,
    fun f hf0 hf => (genAt_facts (hg f hf0 hf)).2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    ext j
    simp only [recC, Finset.mem_filter, Finset.mem_range, hcc0, Nat.one_shiftLeft,
      Nat.testBit_two_pow_sub_one, decide_eq_true_eq, and_self_iff]
  ·
    intro f hf0 hf hm
    obtain ⟨hp, -, -, -, -, hmk, -⟩ := genAt_facts (hg f hf0 hf)
    have := ((hinv _ (hp.trans hf)).1 _).2 hm
    rw [hmk] at this
    exact Bool.false_ne_true this
  ·
    intro f hf0 hf
    obtain ⟨-, hk, -, -, -, -, hcc, -⟩ := genAt_facts (hg f hf0 hf)
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hcc⟩
  ·
    intro f hf0 hf
    obtain ⟨hp, -⟩ := genAt_facts (hg f hf0 hf)
    exact (hSf f hf0 hf (hinv _ (hp.trans hf)).2).1
  ·
    intro f hf0 hf
    obtain ⟨-, hk, -, -, -, -, -, hcc, -⟩ := genAt_facts (hg f hf0 hf)
    ext j
    simp only [recC, Finset.mem_filter, Finset.mem_range, hcc, Nat.testBit_and, Bool.and_eq_true]
    constructor
    · rintro ⟨hj, h1, h2⟩
      exact ⟨⟨hj, h1⟩, ((hcm _ hk j hj).1 h2).symm⟩
    · rintro ⟨⟨hj, h1⟩, h2⟩
      exact ⟨hj, h1, (hcm _ hk j hj).2 h2.symm⟩
  ·
    intro f hf0 hf
    obtain ⟨-, -, -, hsz2, -⟩ := genAt_facts (hg f hf0 hf)
    omega
  ·
    intro f hf i hi hiS
    obtain ⟨hin, hic⟩ := Finset.mem_filter.1 hi
    have hmk : (fld (REC f) 64 m256).testBit i = false :=
      Bool.eq_false_iff.2 fun h => hiS (((hinv f hf).1 i).1 h)
    obtain ⟨c, hcN, hsub, hsz, hci⟩ :=
      covAt_facts (hc f hf) i (by have := Finset.mem_range.1 hin; omega) hic hmk
    refine ⟨c, hcN, fun x hx => ?_, by omega, ((hinv c hcN).1 i).1 hci⟩
    have h1 := ((hinv f hf).1 x).2 hx
    have h2 := congrArg (fun y => y.testBit x) hsub
    simp only [Nat.testBit_and, h1, Bool.true_and] at h2
    exact ((hinv c hcN).1 x).1 h2

end CFSG.KC.EaLat

end
