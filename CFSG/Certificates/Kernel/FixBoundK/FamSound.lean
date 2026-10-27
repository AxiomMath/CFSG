module

public import Certificates.Data.Kernel.FixBoundK.Fam
public import Aesop.BuiltinRules
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set

public section

namespace CFSG.KC.FixBoundK

@[expose] def famL (ch : List (Nat × List Mem)) (i : Nat) : List Nat :=
  ch.flatMap fun c => if c.1 = i then c.2.map (·.1) else []

@[expose] def Cover (piv : Nat) : List Nat → Nat → Prop
  | [], acc => acc = piv
  | z :: zs, acc => (∃ e, z &&& piv = 2 ^ e) ∧ (z &&& piv) &&& acc = 0 ∧
      Cover piv zs (acc ||| (z &&& piv))

inductive XSpan : List Nat → Nat → Prop
  | nil : XSpan [] 0
  | skip {z₀ : Nat} {zs : List Nat} {z : Nat} : XSpan zs z → XSpan (z₀ :: zs) z
  | take {z₀ : Nat} {zs : List Nat} {z : Nat} : XSpan zs z → XSpan (z₀ :: zs) (z₀ ^^^ z)

theorem famS_bAnd {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem famS_withN {α : Type} (y : Nat) (k : Nat → α) : withN y k = k y := by
  cases y <;> rfl

theorem famS_withN_true {y : Nat} {k : Nat → Bool} (h : withN y k = true) : k y = true := by
  rwa [famS_withN] at h

theorem famS_lenS {α : Type} (l : List α) : lenS l = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem famS_getD_lt {l : List Nat} {N : Nat} (hl : ∀ b ∈ l, b < N) (hN : 0 < N) (u : Nat) :
    l.getD u 0 < N := by
  rw [List.getD_eq_getElem?_getD]
  cases e : l[u]? with
  | none => exact hN
  | some b => exact hl b (List.mem_of_getElem? e)

theorem famS_packS_bit {w : Nat} : ∀ (bs : List Nat), (∀ b ∈ bs, b < 2 ^ w) → ∀ (j₀ q k : Nat),
    k < w → (packS bs w j₀).testBit (w * q + k) =
      if j₀ ≤ q then (bs.getD (q - j₀) 0).testBit k else false
  | [], _, j₀, q, k, _ => by
    change (0 : Nat).testBit _ = _
    split <;> simp
  | b :: bs, hbs, j₀, q, k, hk => by
    change (b <<< (w * j₀) ||| packS bs w (j₀ + 1)).testBit (w * q + k) = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft,
      famS_packS_bit bs (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) (j₀ + 1) q k hk]
    rcases Nat.lt_trichotomy q j₀ with hq | hq | hq
    · have h1 : w * (q + 1) ≤ w * j₀ := Nat.mul_le_mul_left _ hq
      rw [Nat.mul_succ] at h1
      have h2 : ¬ (w * q + k ≥ w * j₀) := by omega
      have h3 : ¬ j₀ ≤ q := by omega
      have h4 : ¬ j₀ + 1 ≤ q := by omega
      simp [h2, h3, h4]
    · rw [hq]
      have h4 : ¬ j₀ + 1 ≤ j₀ := by omega
      simp [h4]
    · have h1 : w * (j₀ + 1) ≤ w * q := Nat.mul_le_mul_left _ hq
      rw [Nat.mul_succ] at h1
      have hge : w ≤ w * q + k - w * j₀ := by omega
      have hq1 : j₀ + 1 ≤ q := hq
      have hq2 : j₀ ≤ q := Nat.le_of_lt hq
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hbs b List.mem_cons_self)
        (Nat.pow_le_pow_right (by decide) hge)), Bool.and_false, Bool.false_or,
        if_pos hq1, if_pos hq2]
      have e : q - j₀ = q - (j₀ + 1) + 1 := by omega
      rw [e, List.getD_cons_succ]

theorem famS_slot {w : Nat} {bs : List Nat} (hbs : ∀ b ∈ bs, b < 2 ^ w) (u : Nat) :
    slotS (packS bs w 0) w u = bs.getD u 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  change ((packS bs w 0 >>> (w * u)) &&& (1 <<< w - 1)).testBit t = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases ht : t < w
  · rw [famS_packS_bit bs hbs 0 u t ht]
    simp [ht]
  · have hb := famS_getD_lt hbs (Nat.two_pow_pos w) u
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt ht)))]
    simp [ht]

theorem famS_packS_append (w : Nat) : ∀ (l₁ l₂ : List Nat) (u : Nat),
    packS (l₁ ++ l₂) w u = packS l₁ w u ||| packS l₂ w (u + l₁.length)
  | [], l₂, u => by
    change packS l₂ w u = 0 ||| packS l₂ w (u + 0)
    rw [Nat.zero_or, Nat.add_zero]
  | a :: l₁, l₂, u => by
    change (a <<< (w * u) ||| packS (l₁ ++ l₂) w (u + 1)) =
      (a <<< (w * u) ||| packS l₁ w (u + 1)) ||| packS l₂ w (u + (l₁.length + 1))
    rw [famS_packS_append w l₁ l₂ (u + 1), Nat.or_assoc, Nat.add_assoc, Nat.add_comm 1]

theorem famS_packMs (w M : Nat) : ∀ (ms : List Mem) (u acc : Nat) (k : Nat → Nat → Nat),
    packMs ms w M u acc k = k (u + ms.length) (acc ||| packS ((ms.map (·.1)).map (· ||| M)) w u)
  | [], u, acc, k => by
    change k u acc = k (u + 0) (acc ||| 0)
    rw [Nat.or_zero, Nat.add_zero]
  | e :: ms, u, acc, k => by
    change withN (u + 1) (fun u' => withN (acc ||| (e.1 ||| M) <<< (w * u))
      (fun acc' => packMs ms w M u' acc' k)) = _
    rw [famS_withN, famS_withN, famS_packMs w M ms]
    change k (u + 1 + ms.length) (acc ||| (e.1 ||| M) <<< (w * u) ||| packS _ w (u + 1)) =
      k (u + (ms.length + 1)) (acc ||| ((e.1 ||| M) <<< (w * u) ||| packS _ w (u + 1)))
    rw [Nat.or_assoc, Nat.add_assoc, Nat.add_comm 1]

theorem famS_famL_cons (c : Nat × List Mem) (ch : List (Nat × List Mem)) (i : Nat) :
    famL (c :: ch) i = (if c.1 = i then c.2.map (·.1) else []) ++ famL ch i := by
  simp only [famL, List.flatMap_cons]

theorem famS_packFam_go (i w M : Nat) : ∀ (ch : List (Nat × List Mem)) (u acc : Nat),
    List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
      (fun c _ ih u acc => Bool.rec (motive := fun _ => Nat) (ih u acc)
        (packMs c.2 w M u acc ih) (Nat.beq c.1 i)) ch u acc =
      acc ||| packS ((famL ch i).map (· ||| M)) w u
  | [], u, acc => by
    have h0 : famL [] i = [] := rfl
    rw [h0]
    exact (Nat.or_zero acc).symm
  | c :: ch, u, acc => by
    dsimp only
    rw [famS_famL_cons]
    cases hb : Nat.beq c.1 i with
    | false =>
      have hne : ¬ c.1 = i := fun he => by
        rw [he, Nat.beq_refl] at hb
        cases hb
      rw [if_neg hne, List.nil_append]
      exact famS_packFam_go i w M ch u acc
    | true =>
      rw [if_pos (Nat.eq_of_beq_eq_true hb), List.map_append, famS_packS_append]
      dsimp only
      rw [famS_packMs, famS_packFam_go i w M ch, Nat.or_assoc, List.length_map, List.length_map]

theorem famS_packFam (ch : List (Nat × List Mem)) (i w M : Nat) :
    packFam ch i w M = packS ((famL ch i).map (· ||| M)) w 0 :=
  (famS_packFam_go i w M ch 0 0).trans (Nat.zero_or _)

theorem famS_lowM {a m : Nat} (ha : a < 2 ^ m) : (a ||| 2 ^ m) &&& (2 ^ m - 1) = a := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases ht : t < m
  · have hne : m ≠ t := by omega
    simp [ht, hne]
  · have hb : a.testBit t = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt ht)))
    simp [ht, hb]

theorem famS_or_ne {a m : Nat} : a ||| 2 ^ m ≠ 0 := by
  intro h
  have := congrArg (Nat.testBit · m) h
  simp at this

theorem famS_or_inj {a b m : Nat} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : a ||| 2 ^ m = b ||| 2 ^ m) : a = b := by
  rw [← famS_lowM ha, ← famS_lowM hb, h]

theorem famS_pow2 {t : Nat} (h0 : 0 < t) (h : t &&& (t - 1) = 0) : ∃ e, t = 2 ^ e := by
  obtain ⟨e, he⟩ : ∃ e, e = t.log2 := ⟨_, rfl⟩
  refine ⟨e, ?_⟩
  have hle : 2 ^ e ≤ t := by
    rw [he]
    exact Nat.log2_self_le (by omega)
  have hlt : t < 2 ^ (e + 1) := by
    rw [he]
    exact Nat.lt_log2_self
  rw [Nat.pow_succ] at hlt
  refine Nat.le_antisymm (Nat.le_of_not_lt fun hgt => ?_) hle
  have b1 : t.testBit e = true := by
    have e1 : t = 2 ^ e + (t - 2 ^ e) := by omega
    have hr : t - 2 ^ e < 2 ^ e := by omega
    rw [e1, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr] <;> rfl
  have b2 : (t - 1).testBit e = true := by
    have e2 : t - 1 = 2 ^ e + (t - 1 - 2 ^ e) := by omega
    have hr : t - 1 - 2 ^ e < 2 ^ e := by omega
    rw [e2, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr] <;> rfl
  have := congrArg (Nat.testBit · e) h
  simp [Nat.testBit_and, b1, b2] at this

@[expose] def famNxG (r p : Nat) : Nat := r ^^^ (r &&& p)

theorem famS_nxG_div2 (r p : Nat) : famNxG r p / 2 = famNxG (r / 2) (p / 2) := by
  unfold famNxG
  rw [Nat.xor_div_two, Nat.and_div_two]

theorem famS_nxG_or {x p : Nat} (h : x &&& p = 0) : famNxG (x ||| p) p = x := by
  apply Nat.eq_of_testBit_eq
  intro t
  have ht := congrArg (Nat.testBit · t) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [famNxG, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or]
  cases hx : x.testBit t <;> cases hp : p.testBit t <;> simp_all

theorem famS_nxG_mod2 (r p : Nat) :
    famNxG r p % 2 = if r % 2 = 1 ∧ p % 2 = 0 then 1 else 0 := by
  have h : (famNxG r p).testBit 0 = (r.testBit 0 && !p.testBit 0) := by
    simp only [famNxG, Nat.testBit_xor, Nat.testBit_and]
    cases r.testBit 0 <;> cases p.testBit 0 <;> rfl
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr <;>
    rcases Nat.mod_two_eq_zero_or_one p with hp | hp <;>
    rcases Nat.mod_two_eq_zero_or_one (famNxG r p) with hg | hg <;> simp [hr, hp, hg] at h ⊢

theorem famS_and_mod2 {x p : Nat} (h : x &&& p = 0) : x % 2 = 0 ∨ p % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx
  · exact Or.inl hx
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp
  · exact Or.inr hp
  exfalso
  have := congrArg (Nat.testBit · 0) h
  simp [Nat.testBit_and, Nat.testBit_zero, hx, hp] at this

theorem famS_nx_core : ∀ (y x p : Nat), x &&& p = 0 → y &&& p = 0 → x < y →
    x < famNxG ((x ||| p) + 1) p ∧ famNxG ((x ||| p) + 1) p ≤ y := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro x p hxp hyp hxy
  have hx0 := famS_and_mod2 hxp
  have hy0 := famS_and_mod2 hyp
  have hx1 : x / 2 &&& p / 2 = 0 := by rw [← Nat.and_div_two, hxp]
  have hy1 : y / 2 &&& p / 2 = 0 := by rw [← Nat.and_div_two, hyp]
  obtain ⟨s, hs⟩ : ∃ s, s = x ||| p := ⟨_, rfl⟩
  rw [← hs]
  have hs1 : s / 2 = x / 2 ||| p / 2 := by rw [hs, Nat.or_div_two]
  have hs0 := Nat.testBit_zero s
  rw [hs, Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, ← hs] at hs0
  have hG1 := famS_nxG_div2 (s + 1) p
  have hG0 := famS_nxG_mod2 (s + 1) p
  have eG := Nat.div_add_mod (famNxG (s + 1) p) 2
  have ex := Nat.div_add_mod x 2
  have ey := Nat.div_add_mod y 2
  have es := Nat.div_add_mod s 2
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp
  · rcases Nat.mod_two_eq_zero_or_one x with hxm | hxm
    · have hsm : s % 2 = 0 := by
        rw [hxm, hp] at hs0
        simpa using hs0
      have hr : (s + 1) / 2 = x / 2 ||| p / 2 := by omega
      rw [hr, famS_nxG_or hx1] at hG1
      rw [if_pos (by omega)] at hG0
      omega
    · have hsm : s % 2 = 1 := by
        rw [hxm, hp] at hs0
        simpa using hs0
      have hr : (s + 1) / 2 = (x / 2 ||| p / 2) + 1 := by omega
      rw [hr] at hG1
      rw [if_neg (by omega)] at hG0
      obtain ⟨h1, h2⟩ := ih (y / 2) (by omega) (x / 2) (p / 2) hx1 hy1 (by omega)
      omega
  · have hsm : s % 2 = 1 := by
      rw [hp] at hs0
      simpa using hs0
    have hr : (s + 1) / 2 = (x / 2 ||| p / 2) + 1 := by omega
    rw [hr] at hG1
    rw [if_neg (by omega)] at hG0
    obtain ⟨h1, h2⟩ := ih (y / 2) (by omega) (x / 2) (p / 2) hx1 hy1 (by omega)
    omega

theorem famS_nxt {K piv x y : Nat} (hpiv : piv < 2 ^ K) (hxp : x &&& piv = 0)
    (hy : y < 2 ^ K) (hyp : y &&& piv = 0) (hxy : x < y) :
    x < nxtS (2 ^ K) piv x ∧ nxtS (2 ^ K) piv x ≤ y ∧ nxtS (2 ^ K) piv x &&& piv = 0 := by
  have he : nxtS (2 ^ K) piv x = famNxG ((x ||| piv) + 1) piv &&& (2 ^ K - 1) := by
    apply Nat.eq_of_testBit_eq
    intro t
    change (((x ||| piv) + 1) &&& ((2 ^ K - 1) ^^^ piv)).testBit t = _
    simp only [famNxG, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
    by_cases ht : t < K
    · simp only [ht, decide_true]
      cases ((x ||| piv) + 1).testBit t <;> cases piv.testBit t <;> rfl
    · have hp : piv.testBit t = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hpiv (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [ht, hp]
  obtain ⟨h1, h2⟩ := famS_nx_core y x piv hxp hyp hxy
  rw [he, Nat.and_two_pow_sub_one_of_lt_two_pow (lt_of_le_of_lt h2 hy)]
  refine ⟨h1, h2, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [famNxG, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
  cases ((x ||| piv) + 1).testBit t <;> cases piv.testBit t <;> rfl

theorem famS_look {K w M PF BS A piv : Nat} (hpiv : piv < 2 ^ K) :
    ∀ (vs : List Nat) (x : Nat), lookS (2 ^ K) w M PF BS A piv vs (nxtS (2 ^ K) piv x) = true →
      x &&& piv = 0 → ∀ y, y < 2 ^ K → y &&& piv = 0 → x < y →
        ∃ v, slotS PF w v = (A &&& slotS BS (2 ^ K) y) ||| M
  | [], x, h, hx, y, hy, hyp, hxy => by
    have h0 : nxtS (2 ^ K) piv x = 0 := Nat.eq_of_beq_eq_true h
    have := (famS_nxt hpiv hx hy hyp hxy).1
    omega
  | v :: vs, x, h, hx, y, hy, hyp, hxy => by
    obtain ⟨-, h⟩ := famS_bAnd h
    obtain ⟨hv, h⟩ := famS_bAnd h
    have h := famS_withN_true h
    obtain ⟨-, h2, h3⟩ := famS_nxt hpiv hx hy hyp hxy
    rcases Nat.lt_or_eq_of_le h2 with hlt | heq
    · exact famS_look hpiv vs _ h h3 y hy hyp hlt
    · refine ⟨v, ?_⟩
      rw [← heq]
      exact Nat.eq_of_beq_eq_true hv

theorem famS_cov {m BS A piv : Nat} : ∀ (zs : List Nat) (acc : Nat),
    covS m BS A piv zs acc = true →
      Cover piv zs acc ∧ ∀ z ∈ zs, z < m ∧ A &&& slotS BS m z = A
  | [], acc, h => ⟨Nat.eq_of_beq_eq_true h, fun z hz => absurd hz List.not_mem_nil⟩
  | z :: zs, acc, h => by
    have h := famS_withN_true (y := Nat.land z piv) (k := fun t =>
      bAnd(Nat.blt z m,
      bAnd(Nat.beq (Nat.land A (slotS BS m z)) A,
      bAnd(Nat.blt 0 t,
      bAnd(Nat.beq (Nat.land t (Nat.sub t 1)) 0,
      bAnd(Nat.beq (Nat.land t acc) 0, covS m BS A piv zs (Nat.lor acc t))))))) h
    obtain ⟨h1, h⟩ := famS_bAnd h
    obtain ⟨h2, h⟩ := famS_bAnd h
    obtain ⟨h3, h⟩ := famS_bAnd h
    obtain ⟨h4, h⟩ := famS_bAnd h
    obtain ⟨h5, h6⟩ := famS_bAnd h
    obtain ⟨ih1, ih2⟩ := famS_cov zs _ h6
    refine ⟨⟨famS_pow2 (Nat.blt_eq.mp h3) (Nat.eq_of_beq_eq_true h4),
      Nat.eq_of_beq_eq_true h5, ih1⟩, fun z' hz' => ?_⟩
    rcases List.mem_cons.1 hz' with rfl | hz'
    · exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩
    · exact ih2 z' hz'

@[expose] def famCk (m w M PF BS : Nat) (c : FamC) (A : Nat) : Prop :=
  c.1 &&& (m - 1) = c.1 ∧ covS m BS A c.1 c.2.1 0 = true ∧
    lookS m w M PF BS A c.1 c.2.2 (nxtS m c.1 0) = true

theorem famS_ms {m w M PF BS : Nat} : ∀ (cs : List FamC) (u₀ : Nat),
    famMs m w M PF BS cs u₀ = true → ∀ k < cs.length,
      famCk m w M PF BS (cs.getD k (0, [], [])) (slotS PF w (u₀ + k) &&& (M - 1))
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | c :: cs, u₀, h, k, hk => by
    obtain ⟨hc, hr⟩ := famS_bAnd h
    rcases k with _ | k
    · have hc := famS_withN_true hc
      obtain ⟨h1, hc⟩ := famS_bAnd hc
      obtain ⟨h2, h3⟩ := famS_bAnd hc
      exact ⟨Nat.eq_of_beq_eq_true h1, h2, h3⟩
    · have hr := famS_withN_true hr
      have e : u₀ + (k + 1) = u₀ + 1 + k := by omega
      rw [List.getD_cons_succ, e]
      exact famS_ms cs (u₀ + 1) hr k (by simpa using hk)

theorem famS_main {K m : Nat} {L bs : List Nat} {cs : List FamC} (hm : m = 2 ^ K)
    (hbs : ∀ b ∈ bs, b < 2 ^ m) (hA : ∀ A ∈ L, A < 2 ^ m)
    (h : famW cs m (m + 1) (2 ^ m) (packS (L.map (· ||| 2 ^ m)) (m + 1) 0) (packS bs m 0) = true) :
    L.length = cs.length ∧ L.getLast? = some (2 ^ m - 1) ∧
      ∀ u < L.length, ∃ piv zs, piv < m ∧ Cover piv zs 0 ∧
        (∀ z ∈ zs, z < m ∧ L.getD u 0 &&& bs.getD z 0 = L.getD u 0) ∧
        ∀ j < m, j &&& piv = 0 → j ≠ 0 →
          ∃ v < L.length, L.getD v 0 = L.getD u 0 &&& bs.getD j 0 := by
  have hLw : ∀ b ∈ L.map (· ||| 2 ^ m), b < 2 ^ (m + 1) := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact Nat.or_lt_two_pow (lt_of_lt_of_le (hA a ha) (Nat.pow_le_pow_right (by decide)
      (Nat.le_succ m))) (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self m))
  have hPFlt : ∀ u < L.length,
      slotS (packS (L.map (· ||| 2 ^ m)) (m + 1) 0) (m + 1) u = L.getD u 0 ||| 2 ^ m := by
    intro u hu
    rw [famS_slot hLw, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem hu]
    rfl
  have hPFge : ∀ u, L.length ≤ u →
      slotS (packS (L.map (· ||| 2 ^ m)) (m + 1) 0) (m + 1) u = 0 := by
    intro u hu
    rw [famS_slot hLw, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hu)]
    rfl
  have hPFv : ∀ u a, slotS (packS (L.map (· ||| 2 ^ m)) (m + 1) 0) (m + 1) u = a ||| 2 ^ m →
      u < L.length := by
    intro u a hu
    by_contra hlt
    rw [hPFge u (by omega)] at hu
    exact famS_or_ne hu.symm
  have hBS : ∀ z, slotS (packS bs m 0) m z = bs.getD z 0 := famS_slot hbs
  have h := famS_withN_true h
  obtain ⟨hz, h⟩ := famS_bAnd h
  obtain ⟨hlast, hms⟩ := famS_bAnd h
  have hz := Nat.eq_of_beq_eq_true hz
  have hlast : slotS (packS (L.map (· ||| 2 ^ m)) (m + 1) 0) (m + 1) (lenS cs - 1) =
      (2 ^ m - 1) ||| 2 ^ m := Nat.eq_of_beq_eq_true hlast
  rw [famS_lenS] at hz hlast
  have hge : L.length ≤ cs.length := by
    by_contra hlt
    have h0 : slotS (packS (L.map (· ||| 2 ^ m)) (m + 1) 0) (m + 1) cs.length = 0 := by
      change (Nat.shiftRight (packS (L.map (· ||| 2 ^ m)) (m + 1) 0)
        (Nat.mul (m + 1) cs.length)) &&& _ = 0
      rw [hz, Nat.zero_and]
    rw [hPFlt _ (by omega)] at h0
    exact famS_or_ne h0
  have hlt : cs.length - 1 < L.length := hPFv _ (2 ^ m - 1) hlast
  have hlen : L.length = cs.length := by omega
  refine ⟨hlen, ?_, ?_⟩
  ·
    have hl := hlast
    rw [hPFlt _ hlt] at hl
    have hlv := famS_or_inj (famS_getD_lt hA (Nat.two_pow_pos m) _)
      (Nat.sub_lt (Nat.two_pow_pos m) Nat.one_pos) hl
    rw [List.getLast?_eq_getElem?, hlen, List.getElem?_eq_getElem (by omega), ← hlv,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  · intro u hu
    obtain ⟨hpiv, hcov, hlook⟩ := famS_ms cs 0 hms u (by omega)
    rw [Nat.zero_add, hPFlt u hu, famS_lowM (famS_getD_lt hA (Nat.two_pow_pos m) u)] at hcov hlook
    obtain ⟨hc1, hc2⟩ := famS_cov _ _ hcov
    have hpm : (cs.getD u (0, [], [])).1 < m := by
      rw [← hpiv, hm]
      exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos K) Nat.one_pos)
    refine ⟨_, _, hpm, hc1, fun z hz => ?_, fun j hj hjp hj0 => ?_⟩
    · obtain ⟨hzm, hzA⟩ := hc2 z hz
      rw [hBS] at hzA
      exact ⟨hzm, hzA⟩
    · subst hm
      obtain ⟨v, hv⟩ := famS_look hpm _ 0 hlook (Nat.zero_and _) j hj hjp
        (Nat.pos_of_ne_zero hj0)
      rw [hBS] at hv
      have hvL := hPFv v _ hv
      rw [hPFlt v hvL] at hv
      exact ⟨v, hvL, famS_or_inj (famS_getD_lt hA (Nat.two_pow_pos _) v)
        (lt_of_le_of_lt Nat.and_le_left (famS_getD_lt hA (Nat.two_pow_pos _) u)) hv⟩

theorem famRep_spec {p : Rep} {ch : List (Nat × List Mem)} {i : Nat} {cs : List FamC} {K : Nat}
    (hm : p.2.1.length = 2 ^ K) (hbl : p.2.2.1.length = p.2.1.length)
    (hbs : ∀ b ∈ p.2.2.1, b < 2 ^ p.2.1.length)
    (hA : ∀ A ∈ famL ch i, A < 2 ^ p.2.1.length) (h : famRep p ch i cs = true) :
    (famL ch i).length = cs.length ∧ (famL ch i).getLast? = some (2 ^ p.2.1.length - 1) ∧
      ∀ u < (famL ch i).length, ∃ piv zs, piv < p.2.1.length ∧ Cover piv zs 0 ∧
        (∀ z ∈ zs, z < p.2.1.length ∧
          (famL ch i).getD u 0 &&& p.2.2.1.getD z 0 = (famL ch i).getD u 0) ∧
        ∀ j < p.2.1.length, j &&& piv = 0 → j ≠ 0 →
          ∃ v < (famL ch i).length,
            (famL ch i).getD v 0 = (famL ch i).getD u 0 &&& p.2.2.1.getD j 0 := by
  unfold famRep at h
  have e : Nat.shiftLeft 1 p.2.1.length = 2 ^ p.2.1.length := Nat.one_shiftLeft _
  rw [famS_withN, famS_withN, famS_withN, famS_withN, famS_withN, famS_lenS, famS_packFam,
    e] at h
  exact famS_main hm hbs hA h

theorem XSpan.lt {zs : List Nat} {K : Nat} (hzs : ∀ z ∈ zs, z < 2 ^ K) {z : Nat}
    (h : XSpan zs z) : z < 2 ^ K := by
  induction h with
  | nil => exact Nat.two_pow_pos K
  | skip _ ih => exact ih fun z hz => hzs z (List.mem_cons_of_mem _ hz)
  | take _ ih =>
    exact Nat.xor_lt_two_pow (hzs _ List.mem_cons_self)
      (ih fun z hz => hzs z (List.mem_cons_of_mem _ hz))

theorem XSpan.prop {zs : List Nat} {Q : Nat → Prop} (h0 : Q 0)
    (hx : ∀ a b, a ∈ zs → Q b → Q (a ^^^ b)) {z : Nat} (h : XSpan zs z) : Q z := by
  induction h with
  | nil => exact h0
  | skip _ ih => exact ih fun a b ha hb => hx a b (List.mem_cons_of_mem _ ha) hb
  | take _ ih =>
    exact hx _ _ List.mem_cons_self (ih fun a b ha hb => hx a b (List.mem_cons_of_mem _ ha) hb)

theorem exists_xspan {piv : Nat} : ∀ {zs : List Nat} {acc : Nat}, Cover piv zs acc → ∀ j : Nat,
    ∃ z, XSpan zs z ∧ ∀ t, ((j ^^^ z) &&& piv).testBit t = true → acc.testBit t = true
  | [], acc, h, j => by
    refine ⟨0, XSpan.nil, fun t ht => ?_⟩
    have h' : acc = piv := h
    rw [Nat.xor_zero, Nat.testBit_and, Bool.and_eq_true] at ht
    rw [h']
    exact ht.2
  | z₀ :: zs, acc, h, j => by
    obtain ⟨⟨e, he⟩, hdis, hc⟩ := h
    obtain ⟨z', hz', hbits⟩ := exists_xspan hc j
    by_cases hj : (j ^^^ z').testBit e = true
    · refine ⟨z₀ ^^^ z', XSpan.take hz', fun t ht => ?_⟩
      have hz₀ : ∀ t, piv.testBit t = true → z₀.testBit t = decide (e = t) := by
        intro t hp
        have := congrArg (fun x => Nat.testBit x t) he
        simp only [Nat.testBit_and, hp, Bool.and_true, Nat.testBit_two_pow] at this
        exact this
      have hpt : piv.testBit t = true := by
        rw [Nat.testBit_and, Bool.and_eq_true] at ht
        exact ht.2
      have ht' : ((j ^^^ z') &&& piv).testBit t = true ∧ t ≠ e := by
        have hre : j ^^^ (z₀ ^^^ z') = z₀ ^^^ (j ^^^ z') := by
          rw [← Nat.xor_assoc, Nat.xor_comm j z₀, Nat.xor_assoc]
        rw [hre] at ht
        rw [Nat.testBit_and, Nat.testBit_xor, hz₀ t hpt, hpt, Bool.and_true] at ht
        by_cases hte : t = e
        · subst hte
          rw [hj] at ht
          simp at ht
        · refine ⟨?_, hte⟩
          rw [Nat.testBit_and, hpt, Bool.and_true]
          simpa [Ne.symm hte] using ht
      have hacc := hbits t ht'.1
      rw [Nat.testBit_or, Bool.or_eq_true, he, Nat.testBit_two_pow] at hacc
      rcases hacc with ha | ha
      · exact ha
      · exact absurd (of_decide_eq_true ha).symm ht'.2
    · refine ⟨z', XSpan.skip hz', fun t ht => ?_⟩
      have hacc := hbits t ht
      rw [Nat.testBit_or, Bool.or_eq_true, he, Nat.testBit_two_pow] at hacc
      rcases hacc with ha | ha
      · exact ha
      · have hte : e = t := of_decide_eq_true ha
        subst hte
        rw [Nat.testBit_and, Bool.and_eq_true] at ht
        exact absurd ht.1 hj

theorem famL_closed {K : Nat} {L : List Nat} {bs : Nat → Nat}
    (hbil : ∀ A z j, z < 2 ^ K → j < 2 ^ K → A &&& bs z = A → A &&& bs (j ^^^ z) = A &&& bs j)
    (hb0 : ∀ u < L.length, L.getD u 0 &&& bs 0 = L.getD u 0)
    (hcl : ∀ u < L.length, ∃ piv zs, piv < 2 ^ K ∧ Cover piv zs 0 ∧
      (∀ z ∈ zs, z < 2 ^ K ∧ L.getD u 0 &&& bs z = L.getD u 0) ∧
      ∀ j < 2 ^ K, j &&& piv = 0 → j ≠ 0 → ∃ v < L.length, L.getD v 0 = L.getD u 0 &&& bs j) :
    ∀ u < L.length, ∀ j < 2 ^ K, ∃ v < L.length, L.getD v 0 = L.getD u 0 &&& bs j := by
  intro u hu j hj
  obtain ⟨piv, zs, -, hcov, hzs, hlook⟩ := hcl u hu
  obtain ⟨z, hz, hbits⟩ := exists_xspan hcov j
  set A := L.getD u 0
  have hzlt : z < 2 ^ K := hz.lt fun z hz => (hzs z hz).1
  have hAz : z < 2 ^ K ∧ A &&& bs z = A := by
    refine hz.prop (Q := fun z => z < 2 ^ K ∧ A &&& bs z = A) ⟨Nat.two_pow_pos K, hb0 u hu⟩ ?_
    intro a b ha hb
    obtain ⟨hal, haA⟩ := hzs a ha
    refine ⟨Nat.xor_lt_two_pow hal hb.1, ?_⟩
    rw [Nat.xor_comm, hbil A a b hal hb.1 haA, hb.2]
  have hj' : j ^^^ z < 2 ^ K := Nat.xor_lt_two_pow hj hzlt
  have hpiv : (j ^^^ z) &&& piv = 0 := by
    apply Nat.eq_of_testBit_eq
    intro t
    rw [Nat.zero_testBit]
    cases ht : ((j ^^^ z) &&& piv).testBit t
    · rfl
    · have := hbits t ht
      rw [Nat.zero_testBit] at this
      exact absurd this (by simp)
  have heq : A &&& bs j = A &&& bs (j ^^^ z) := by
    have := hbil A z (j ^^^ z) hzlt hj' hAz.2
    rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
  rw [heq]
  by_cases h0 : j ^^^ z = 0
  · exact ⟨u, hu, by rw [h0, hb0 u hu]⟩
  · exact hlook (j ^^^ z) hj' hpiv h0

theorem foldl_mem {m : Nat} {L : List Nat} {bs : Nat → Nat}
    (hcl : ∀ u < L.length, ∀ j < m, ∃ v < L.length, L.getD v 0 = L.getD u 0 &&& bs j) :
    ∀ (l : List Nat), (∀ j ∈ l, j < m) → ∀ u < L.length,
      ∃ v < L.length, L.getD v 0 = l.foldl (fun acc j => acc &&& bs j) (L.getD u 0)
  | [], _, u, hu => ⟨u, hu, rfl⟩
  | j :: l, hl, u, hu => by
    obtain ⟨v, hv, hve⟩ := hcl u hu j (hl j List.mem_cons_self)
    obtain ⟨w, hw, hwe⟩ := foldl_mem hcl l (fun k hk => hl k (List.mem_cons_of_mem j hk)) v hv
    refine ⟨w, hw, ?_⟩
    rw [hwe, hve, List.foldl_cons]

end CFSG.KC.FixBoundK

end
