
module

public import Certificates.Data.Kernel.ThDemp.Orb
import CFSG.Certificates.Kernel.ThDemp.OrbUnfoldBase

public section

namespace CFSG.Certificates.ThDemp.Facts

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThDemp CFSG.KC.Loop

variable (D : DempData) (O : OrbData)

section BatchHelpers

open CFSG.Certificates.ThDemp.Lanes

private theorem jz_lane64_succ (N y : ℕ) : lane64 N (y + 1) = lane64 (N / 2 ^ 64) y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_lane64, testBit_lane64, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight,
    show 64 * (y + 1) + i = 64 + (64 * y + i) by omega]

private theorem jz_lane64_zero (N : ℕ) : lane64 N 0 = N % 2 ^ 64 := by
  simp [lane64]

private theorem jz_lane64_sub (y : ℕ) : ∀ A C : ℕ, C ≤ A →
    (∀ z ≤ y, lane64 C z ≤ lane64 A z) → lane64 (A - C) y = lane64 A y - lane64 C y := by
  induction y with
  | zero =>
    intro A C hCA hz
    have h0 := hz 0 le_rfl
    simp only [jz_lane64_zero] at h0 ⊢
    omega
  | succ y ih =>
    intro A C hCA hz
    have h0 := hz 0 (Nat.zero_le _)
    simp only [jz_lane64_zero] at h0
    have e : (A - C) / 2 ^ 64 = A / 2 ^ 64 - C / 2 ^ 64 := by omega
    have h1 : C / 2 ^ 64 ≤ A / 2 ^ 64 := by omega
    rw [jz_lane64_succ, jz_lane64_succ, jz_lane64_succ, e]
    refine ih _ _ h1 fun z hz' => ?_
    have := hz (z + 1) (by omega)
    rwa [jz_lane64_succ, jz_lane64_succ] at this

private theorem jz_lane64_eq {N v z : ℕ} (hv : v < 2 ^ 64)
    (h : ∀ i < 64, N.testBit (64 * z + i) = v.testBit i) : lane64 N z = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_lane64]
  by_cases hi : i < 64
  · simp [hi, h i hi]
  · have : v.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, this]

private theorem jz_repN_eq {x d n : ℕ} (hx : x < 2 ^ 64) (hn : n ≤ 2 ^ d) :
    repN x 64 d n = rep x 64 n := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_repN (by omega) hx hn, testBit_rep (by omega) hx]

private theorem jz_rep_lt {x : ℕ} (hx : x < 2 ^ 64) (n : ℕ) : rep x 64 n < 2 ^ (64 * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_rep (by omega) hx]
  have : ¬ j / 64 < n := by omega
  simp [this]

private theorem jz_rep_succ {x : ℕ} (hx : x < 2 ^ 64) (n : ℕ) :
    rep x 64 (n + 1) = 2 ^ (64 * n) * x + rep x 64 n := by
  rw [Nat.two_pow_add_eq_or_of_lt (jz_rep_lt hx n) x, Rows.rep_succ_eq, Nat.shiftLeft_eq,
    Nat.mul_comm x (2 ^ (64 * n)), Nat.or_comm]

private theorem jz_mul_rep {k : ℕ} (hk : k < 2 ^ 64) : ∀ n, k * rep 1 64 n = rep k 64 n
  | 0 => by simp [rep]
  | n + 1 => by
    rw [jz_rep_succ (by omega : 1 < 2 ^ 64), jz_rep_succ hk, Nat.mul_add, jz_mul_rep hk n,
      Nat.mul_one, Nat.mul_comm k]

private theorem jz_testBit_mul_repN {k d n : ℕ} (hk : k < 2 ^ 64) (hn : n ≤ 2 ^ d) (p : ℕ) :
    (k * repN 1 64 d n).testBit p = (decide (p / 64 < n) && k.testBit (p % 64)) := by
  rw [jz_repN_eq (by omega) hn, jz_mul_rep hk, testBit_rep (by omega) hk]

private theorem jz_bit_H {H d n y : ℕ} (hH : H = repN (Nat.shiftLeft 1 63) 64 d n)
    (hn : n ≤ 2 ^ d) (hy : y < n) : H.testBit (64 * y + 63) = true := by
  have h63 : Nat.shiftLeft 1 63 = 2 ^ 63 := Nat.one_shiftLeft 63
  rw [h63] at hH
  rw [hH, testBit_repN (by omega) (by decide) hn]
  have e1 : (64 * y + 63) / 64 = y := by omega
  have e2 : (64 * y + 63) % 64 = 63 := by omega
  rw [e1, e2, Nat.testBit_two_pow_self]
  simp [hy]

private theorem jz_clear {H C d n y k KY : ℕ} (hH : H = repN (Nat.shiftLeft 1 63) 64 d n)
    (hC : C = repN 1 64 d n) (hn : n ≤ 2 ^ d) (hk : k < 2 ^ 64) (hy : y < n)
    (hm : lane64 KY y = k) : (jz H C KY k).testBit (64 * y + 63) = false := by
  have h63 : Nat.shiftLeft 1 63 = 2 ^ 63 := Nat.one_shiftLeft 63
  rw [h63] at hH
  have hlt63 : 2 ^ 63 < 2 ^ 64 := by decide
  have hCb : ∀ p, C.testBit p = (decide (p / 64 < n) && (1 : ℕ).testBit (p % 64)) := fun p => by
    rw [hC]
    exact testBit_repN (by omega) (by decide) hn p
  have hHb : ∀ p, H.testBit p =
      (decide (p / 64 < n) && (2 ^ 63 : ℕ).testBit (p % 64)) := fun p => by
    rw [hH]
    exact testBit_repN (by omega) hlt63 hn p
  have hkC : ∀ p, (k * C).testBit p = (decide (p / 64 < n) && k.testBit (p % 64)) := fun p => by
    rw [hC]
    exact jz_testBit_mul_repN hk hn p
  have hHC : H = 2 ^ 63 * C := by
    rw [hH, hC, jz_repN_eq hlt63 hn, jz_repN_eq (by decide) hn, jz_mul_rep hlt63]
  have hjz : jz H C KY k = (((KY ^^^ k * C) ||| H) - C) &&& H := rfl
  generalize hA : (KY ^^^ k * C) ||| H = A at hjz
  have hlaneC : ∀ z < n, lane64 C z = 1 := fun z hz => by
    apply jz_lane64_eq (by decide)
    intro i hi
    rw [hCb]
    have e1 : (64 * z + i) / 64 = z := by omega
    have e2 : (64 * z + i) % 64 = i := by omega
    simp [e1, e2, hz]
  have hbitA : ∀ z < n, A.testBit (64 * z + 63) = true := fun z hz => by
    rw [← hA, Nat.testBit_or, hHb]
    have e1 : (64 * z + 63) / 64 = z := by omega
    have e2 : (64 * z + 63) % 64 = 63 := by omega
    rw [e1, e2, Nat.testBit_two_pow_self]
    simp [hz]
  have hgeA : ∀ z < n, 2 ^ 63 ≤ lane64 A z := fun z hz => by
    apply Nat.ge_two_pow_of_testBit
    rw [testBit_lane64]
    simp [hbitA z hz]
  have hlaneA : lane64 A y = 2 ^ 63 := by
    apply jz_lane64_eq hlt63
    intro i hi
    have e1 : (64 * y + i) / 64 = y := by omega
    have e2 : (64 * y + i) % 64 = i := by omega
    have hKY : KY.testBit (64 * y + i) = k.testBit i := by
      rw [← hm, testBit_lane64]
      simp [hi]
    rw [← hA, Nat.testBit_or, Nat.testBit_xor, hHb, hkC, hKY, e1, e2]
    simp [hy]
  have hCA : C ≤ A := by
    have h1 : C ≤ H := by
      rw [hHC]
      exact Nat.le_mul_of_pos_left C (Nat.two_pow_pos 63)
    rw [← hA]
    exact h1.trans Nat.right_le_or
  have hdom : ∀ z ≤ y, lane64 C z ≤ lane64 A z := fun z hz => by
    rw [hlaneC z (by omega)]
    have := hgeA z (by omega)
    omega
  have hsub := jz_lane64_sub y A C hCA hdom
  rw [hlaneA, hlaneC y hy] at hsub
  have hbit : (A - C).testBit (64 * y + 63) = false := by
    have h1 : (lane64 (A - C) y).testBit 63 = false := by
      rw [hsub]
      exact Nat.testBit_lt_two_pow (by omega)
    rw [testBit_lane64] at h1
    simpa using h1
  rw [hjz, Nat.testBit_and, hbit, Bool.false_and]

private theorem batch_testBit_of_bitB {F p : ℕ} (h : bitB F p = true) : F.testBit p = true := by
  have h1 : (F >>> p) &&& 1 = 1 := Nat.eq_of_beq_eq_true h
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] at h1
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp [h1]

private theorem batch_flagsOf : ∀ (gs : List (List ℕ)) (p : ℕ),
    (flagsOf gs).testBit p = true → ∃ g ∈ gs, lget g 0 % 512 = p
  | [], p, h => by
    have e : flagsOf [] = 0 := rfl
    rw [e, Nat.zero_testBit] at h
    exact absurd h (by simp)
  | g :: gs, p, h => by
    have e : flagsOf (g :: gs) = flagsOf gs ||| 1 <<< (lget g 0 % 512) := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨g', hg', hp⟩ := batch_flagsOf gs p h
      exact ⟨g', List.mem_cons_of_mem _ hg', hp⟩
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff] at h
      exact ⟨g, by simp, h⟩

private theorem batch_maskOf : ∀ (es : List ℕ) (q : ℕ),
    (maskOf es).testBit q = true → ∃ e ∈ es, q = 64 * (e >>> 25) + 63
  | [], q, h => by
    have e : maskOf [] = 0 := rfl
    rw [e, Nat.zero_testBit] at h
    exact absurd h (by simp)
  | e :: es, q, h => by
    have e' : maskOf (e :: es) = maskOf es ||| 1 <<< (64 * (e >>> 25) + 63) := rfl
    rw [e', Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨e₁, he₁, hq⟩ := batch_maskOf es q h
      exact ⟨e₁, List.mem_cons_of_mem _ he₁, hq⟩
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff] at h
      exact ⟨e, by simp, h.symm⟩

private theorem batch_recAnd {P : List ℕ → Bool} : ∀ gs : List (List ℕ),
    List.rec (motive := fun _ => Bool) true (fun g _ ih => andB (P g) ih) gs = true →
    ∀ g ∈ gs, P g = true
  | [], _, g, hg => by simp at hg
  | _ :: gs, h, g, hg => by
    obtain ⟨h1, h2⟩ := Unfold.andB_split h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact h1
    · exact batch_recAnd gs h2 g hg

private theorem batch_match {H C KY KX p y : ℕ} (hH : H = repN (Nat.shiftLeft 1 63) 64 15 26040)
    (hC : C = repN 1 64 15 26040) (hy : y < 26040) (hmatch : keyAt KX p = keyAt KY y) :
    (jz H C KY (keyAt KX p)).testBit (64 * y + 63) = false ∧ H.testBit (64 * y + 63) = true := by
  have hn : (26040 : ℕ) ≤ 2 ^ 15 := by decide
  have hk : keyAt KX p < 2 ^ 64 := by
    rw [keyAt_eq]
    exact Nat.mod_lt _ (Nat.two_pow_pos 64)
  have hm : lane64 KY y = keyAt KX p := by rw [← keyAt_eq, hmatch]
  exact ⟨jz_clear hH hC hn hk hy hm, jz_bit_H hH hn hy⟩

private theorem batch_match_ne {H C KY KX p y : ℕ} (hH : H = repN (Nat.shiftLeft 1 63) 64 15 26040)
    (hC : C = repN 1 64 15 26040) (hy : y < 26040) (hmatch : keyAt KX p = keyAt KY y) :
    jz H C KY (keyAt KX p) ≠ H := by
  intro h4
  obtain ⟨hclear, hHbit⟩ := batch_match hH hC hy hmatch
  rw [h4, hHbit] at hclear
  exact absurd hclear (by simp)

private theorem batch_core {H C KY KX y3 : ℕ} {gs : List (List ℕ)}
    (hH : H = repN (Nat.shiftLeft 1 63) 64 15 26040) (hC : C = repN 1 64 15 26040)
    (h : andB (allBelow 512 8 (fun p => Bool.rec (motive := fun _ => Bool)
        (Nat.beq (jz H C KY (keyAt KX p)) H) true (bitB (flagsOf gs) p)))
      (List.rec (motive := fun _ => Bool) true (fun g _ ih => andB
        (andB (Nat.beq (Nat.div (lget g 0) 512) y3)
          (Nat.beq (Nat.xor (jz H C KY (keyAt KX (Nat.mod (lget g 0) 512))) H)
            (maskOf g.tail))) ih) gs) = true) :
    ∀ p < 512, ∀ y < 26040, keyAt KX p = keyAt KY y →
      ∃ g ∈ gs, lget g 0 = 512 * y3 + p ∧ ∃ e ∈ g.tail, e >>> 25 = y := by
  obtain ⟨h1, h2⟩ := Unfold.andB_split h
  intro p hp y hy hmatch
  obtain ⟨hclear, hHbit⟩ := batch_match hH hC hy hmatch
  have hflag : bitB (flagsOf gs) p = true := by
    cases hb : bitB (flagsOf gs) p
    · exfalso
      have h3 := Unfold.allBelow_spec h1 (by decide) p hp
      rw [hb] at h3
      exact batch_match_ne hH hC hy hmatch (Nat.eq_of_beq_eq_true h3)
    · rfl
  obtain ⟨g, hg, hgp⟩ := batch_flagsOf gs p (batch_testBit_of_bitB hflag)
  obtain ⟨h6, h7⟩ := Unfold.andB_split (batch_recAnd gs h2 g hg)
  have hdiv : lget g 0 / 512 = y3 := Nat.eq_of_beq_eq_true h6
  have hmask : jz H C KY (keyAt KX (lget g 0 % 512)) ^^^ H = maskOf g.tail :=
    Nat.eq_of_beq_eq_true h7
  rw [hgp] at hmask
  have hbit : (maskOf g.tail).testBit (64 * y + 63) = true := by
    rw [← hmask, Nat.testBit_xor, hclear, hHbit]
    rfl
  obtain ⟨e, he, hq⟩ := batch_maskOf g.tail _ hbit
  exact ⟨g, hg, by omega, e, he, by omega⟩

private theorem batch_cross_core {H C KY KX : ℕ}
    (hH : H = repN (Nat.shiftLeft 1 63) 64 15 26040) (hC : C = repN 1 64 15 26040)
    (h : allBelow 512 8 (fun p => Nat.beq (jz H C KY (keyAt KX p)) H) = true) :
    ∀ p < 512, ∀ y < 26040, keyAt KX p ≠ keyAt KY y := by
  intro p hp y hy hmatch
  exact batch_match_ne hH hC hy hmatch
    (Nat.eq_of_beq_eq_true (Unfold.allBelow_spec h (by decide) p hp))

end BatchHelpers

theorem batchChk_sound {i y3 : Nat} (h : batchChk D O i y3 = true) :
    ∀ p < 512, ∀ y < 26040, keyAt (xKeys D (pt D O i) y3) p = keyAt (lget O.ky i) y →
      ∃ g ∈ O.grpOf i y3, lget g 0 = 512 * y3 + p ∧ ∃ e ∈ g.tail, e >>> 25 = y := by
  unfold batchChk at h
  simp only [Batches.strictB_eq] at h
  exact batch_core rfl rfl h

theorem crossChk_sound {i j y3 : Nat} (h : crossChk D O i j y3 = true) :
    ∀ p < 512, ∀ y < 26040, keyAt (xKeys D (pt D O i) y3) p ≠ keyAt (lget O.ky j) y := by
  unfold crossChk at h
  simp only [Batches.strictB_eq] at h
  exact batch_cross_core rfl rfl h

private def low_code (p : Nat × Nat) : Nat := (p.2 + 32768 * p.1).succ

private def low_Run (prev : Nat) (ps : List (Nat × Nat)) (r : Nat) : Prop :=
  prev ≤ r ∧ (∀ p ∈ ps, prev < low_code p ∧ low_code p ≤ r) ∧
    ps.Pairwise fun p q => low_code p < low_code q

private theorem low_Run_nil (prev : Nat) : low_Run prev [] prev :=
  ⟨le_rfl, by simp, List.Pairwise.nil⟩

private theorem low_Run_cons {prev r : Nat} {p : Nat × Nat} {ps : List (Nat × Nat)}
    (hp : prev < low_code p) (h : low_Run (low_code p) ps r) : low_Run prev (p :: ps) r := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hp.le.trans h1, ?_, List.pairwise_cons.2 ⟨fun q hq => (h2 q hq).1, h3⟩⟩
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact ⟨hp, h1⟩
  · exact ⟨hp.trans (h2 q hq).1, (h2 q hq).2⟩

private theorem low_Run_append {prev r₁ r₂ : Nat} {ps qs : List (Nat × Nat)}
    (h1 : low_Run prev ps r₁) (h2 : low_Run r₁ qs r₂) : low_Run prev (ps ++ qs) r₂ := by
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  refine ⟨a1.trans a2, ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact ⟨(b1 p hp).1, (b1 p hp).2.trans a2⟩
    · exact ⟨a1.trans_lt (b2 p hp).1, (b2 p hp).2⟩
  · rw [List.pairwise_append]
    exact ⟨c1, c2, fun p hp q hq => lt_of_le_of_lt (b1 p hp).2 (b2 q hq).1⟩

private theorem low_Run_nodup {prev r : Nat} {ps : List (Nat × Nat)} (h : low_Run prev ps r) :
    ps.Nodup :=
  h.2.2.imp fun {p q} hlt heq => by
    subst heq
    exact lt_irrefl _ hlt

private noncomputable def low_gpairs (g : List Nat) : List (Nat × Nat) :=
  g.tail.map fun e => (lget g 0, e >>> 25)

private theorem low_pairOK {Z W : List Nat} {x e : Nat} (h : pairOK D Z W x e = true) :
    x < 12288 ∧ e >>> 25 < 26040 ∧ ∃ G, combChk D.rm (xPt Z x) (yPt W (e >>> 25)) G = true := by
  change andB (Nat.blt x 12288) (andB (Nat.blt (e >>> 25) 26040)
    (combChk D.rm (xPt Z x) (yPt W (e >>> 25)) (bitsN e 0 25))) = true at h
  obtain ⟨h1, h2⟩ := Unfold.andB_split h
  obtain ⟨h2, h3⟩ := Unfold.andB_split h2
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, _, h3⟩

private theorem low_groupRun_cons {Z W : List Nat} {x e : Nat} {es : List Nat} {prev : Nat}
    (h : 0 < groupRun D Z W x (e :: es) prev) :
    Nat.blt prev (low_code (x, e >>> 25)) = true ∧ pairOK D Z W x e = true ∧
      groupRun D Z W x (e :: es) prev = groupRun D Z W x es (low_code (x, e >>> 25)) := by
  have hc : groupRun D Z W x (e :: es) prev = Bool.rec (motive := fun _ => Nat) 0
      (groupRun D Z W x es (low_code (x, e >>> 25)))
      (andB (Nat.blt prev (low_code (x, e >>> 25))) (pairOK D Z W x e)) := rfl
  cases hb : andB (Nat.blt prev (low_code (x, e >>> 25))) (pairOK D Z W x e)
  · rw [hc, hb] at h
    exact absurd h (lt_irrefl 0)
  · obtain ⟨h1, h2⟩ := Unfold.andB_split hb
    exact ⟨h1, h2, by rw [hc, hb]⟩

private theorem low_groupRun {Z W : List Nat} {x : Nat} :
    ∀ (es : List Nat) (prev : Nat), 0 < groupRun D Z W x es prev →
      (∀ e ∈ es, pairOK D Z W x e = true) ∧
        low_Run prev (es.map fun e => (x, e >>> 25)) (groupRun D Z W x es prev)
  | [], prev, _ => ⟨by simp, low_Run_nil prev⟩
  | e :: es, prev, h => by
    obtain ⟨h1, h2, h3⟩ := low_groupRun_cons D h
    have h4 : 0 < groupRun D Z W x es (low_code (x, e >>> 25)) := h3 ▸ h
    obtain ⟨ih1, ih2⟩ := low_groupRun es _ h4
    rw [h3]
    refine ⟨?_, low_Run_cons (Nat.blt_eq.mp h1) ih2⟩
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h2
    · exact ih1 e' he'

private theorem low_groupsRun_cons {Z W : List Nat} {g : List Nat} {gs : List (List Nat)}
    {prev : Nat} (h : 0 < groupsRun D Z W (g :: gs) prev) :
    0 < groupRun D Z W (lget g 0) g.tail prev ∧
      groupsRun D Z W (g :: gs) prev =
        groupsRun D Z W gs (groupRun D Z W (lget g 0) g.tail prev) := by
  have hc : groupsRun D Z W (g :: gs) prev = Bool.rec (motive := fun _ => Nat) 0
      (groupsRun D Z W gs (groupRun D Z W (lget g 0) g.tail prev))
      (Nat.blt 0 (groupRun D Z W (lget g 0) g.tail prev)) := rfl
  cases hb : Nat.blt 0 (groupRun D Z W (lget g 0) g.tail prev)
  · rw [hc, hb] at h
    exact absurd h (lt_irrefl 0)
  · exact ⟨Nat.blt_eq.mp hb, by rw [hc, hb]⟩

private theorem low_groupsRun {Z W : List Nat} :
    ∀ (gs : List (List Nat)) (prev : Nat), 0 < groupsRun D Z W gs prev →
      (∀ g ∈ gs, ∀ e ∈ g.tail, pairOK D Z W (lget g 0) e = true) ∧
        low_Run prev (gs.flatMap low_gpairs) (groupsRun D Z W gs prev)
  | [], prev, _ => ⟨by simp, low_Run_nil prev⟩
  | g :: gs, prev, h => by
    obtain ⟨h1, h2⟩ := low_groupsRun_cons D h
    have h4 : 0 < groupsRun D Z W gs (groupRun D Z W (lget g 0) g.tail prev) := h2 ▸ h
    obtain ⟨ih1, ih2⟩ := low_groupsRun gs _ h4
    obtain ⟨g1, g2⟩ := low_groupRun D g.tail prev h1
    rw [h2, List.flatMap_cons]
    refine ⟨?_, low_Run_append g2 ih2⟩
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact g1
    · exact ih1 g' hg'

private theorem low_batchesRun_cons {Z W : List Nat} {gs : List (List Nat)}
    {bs : List (List (List Nat))} {prev : Nat} (h : 0 < batchesRun D Z W (gs :: bs) prev) :
    0 < groupsRun D Z W gs prev ∧
      batchesRun D Z W (gs :: bs) prev = batchesRun D Z W bs (groupsRun D Z W gs prev) := by
  have hc : batchesRun D Z W (gs :: bs) prev = Bool.rec (motive := fun _ => Nat) 0
      (batchesRun D Z W bs (groupsRun D Z W gs prev)) (Nat.blt 0 (groupsRun D Z W gs prev)) := rfl
  cases hb : Nat.blt 0 (groupsRun D Z W gs prev)
  · rw [hc, hb] at h
    exact absurd h (lt_irrefl 0)
  · exact ⟨Nat.blt_eq.mp hb, by rw [hc, hb]⟩

private theorem low_batchesRun {Z W : List Nat} :
    ∀ (bs : List (List (List Nat))) (prev : Nat), 0 < batchesRun D Z W bs prev →
      (∀ gs ∈ bs, ∀ g ∈ gs, ∀ e ∈ g.tail, pairOK D Z W (lget g 0) e = true) ∧
        low_Run prev (bs.flatMap fun gs => gs.flatMap low_gpairs) (batchesRun D Z W bs prev)
  | [], prev, _ => ⟨by simp, low_Run_nil prev⟩
  | gs :: bs, prev, h => by
    obtain ⟨h1, h2⟩ := low_batchesRun_cons D h
    have h4 : 0 < batchesRun D Z W bs (groupsRun D Z W gs prev) := h2 ▸ h
    obtain ⟨ih1, ih2⟩ := low_batchesRun bs _ h4
    obtain ⟨g1, g2⟩ := low_groupsRun D gs prev h1
    rw [h2, List.flatMap_cons]
    refine ⟨?_, low_Run_append g2 ih2⟩
    intro gs' hgs'
    rcases List.mem_cons.1 hgs' with rfl | hgs'
    · exact g1
    · exact ih1 gs' hgs'

private theorem low_pairsLen_groups (gs : List (List Nat)) :
    List.rec (motive := fun _ => Nat) 0 (fun g _ ih2 => Nat.add g.tail.length ih2) gs =
      (gs.flatMap low_gpairs).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change Nat.add g.tail.length (List.rec (motive := fun _ => Nat) 0
      (fun g _ ih2 => Nat.add g.tail.length ih2) gs) = _
    rw [ih, List.flatMap_cons, List.length_append]
    simp [low_gpairs]

private theorem low_pairsLen (bs : List (List (List Nat))) :
    pairsLen bs = (bs.flatMap fun gs => gs.flatMap low_gpairs).length := by
  induction bs with
  | nil => rfl
  | cons gs bs ih =>
    change Nat.add (List.rec (motive := fun _ => Nat) 0
      (fun g _ ih2 => Nat.add g.tail.length ih2) gs) (pairsLen bs) = _
    rw [low_pairsLen_groups, ih, List.flatMap_cons, List.length_append]
    rfl

private theorem low_lgetLL_mem :
    ∀ (bs : List (List (List Nat))) (b : Nat), lgetLL bs b ∈ bs ∨ lgetLL bs b = []
  | [], _ => Or.inr rfl
  | gs :: bs, 0 => Or.inl (List.mem_cons_self ..)
  | gs :: bs, b + 1 => by
    rcases low_lgetLL_mem bs b with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h

theorem lowChk_sound {i : Nat} (h : lowChk D O i = true) :
    ∃ L : List (Nat × Nat), L.length = lget O.sb i ∧ L.Nodup ∧
      (∀ e ∈ L, e.1 < 12288 ∧ e.2 < 26040 ∧ ∃ G,
        combChk D.rm (xPt (xBat D (pt D O i)) e.1) (yPt (yBat D O (pt D O i)) e.2) G = true) ∧
      ∀ b, ∀ g ∈ O.grpOf i b, ∀ e ∈ g.tail, (lget g 0, e >>> 25) ∈ L := by
  unfold lowChk at h
  beta_reduce at h
  rw [Batches.strictB_eq] at h
  obtain ⟨h1, h2⟩ := Unfold.andB_split h
  have hlen : pairsLen (lgetL3 O.grp i) = lget O.sb i := Nat.eq_of_beq_eq_true h1
  have hpos := Nat.blt_eq.mp h2
  obtain ⟨hpairs, hrun⟩ := low_batchesRun D (lgetL3 O.grp i) 0 hpos
  refine ⟨(lgetL3 O.grp i).flatMap fun gs => gs.flatMap low_gpairs, ?_, low_Run_nodup hrun, ?_, ?_⟩
  · rw [← hlen, low_pairsLen]
  · intro p hp
    simp only [List.mem_flatMap, low_gpairs, List.mem_map] at hp
    obtain ⟨gs, hgs, g, hg, e, he, rfl⟩ := hp
    exact low_pairOK D (hpairs gs hgs g hg e he)
  · intro b g hg e he
    rcases low_lgetLL_mem (lgetL3 O.grp i) b with hb | hb
    · simp only [List.mem_flatMap, low_gpairs, List.mem_map]
      exact ⟨O.grpOf i b, hb, g, hg, e, he, rfl⟩
    · exact absurd hg (by rw [OrbData.grpOf, hb]; simp)

section

set_option exponentiation.threshold 2000

private theorem orb_lane_append {N E n : ℕ} (hN : N < 2 ^ (1280 * n)) (hE : E < 2 ^ 1280) :
    N ||| E <<< (1280 * n) < 2 ^ (1280 * (n + 1)) ∧
    Lanes.lane (N ||| E <<< (1280 * n)) n = E ∧
    ∀ k < n, Lanes.lane (N ||| E <<< (1280 * n)) k = Lanes.lane N k := by
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    have h1 : N.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by omega) (by omega)))
    have h2 : E.testBit (i - 1280 * n) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [h1, h2]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Lanes.testBit_lane, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hi : i < 1280
    · have h1 : N.testBit (1280 * n + i) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by omega) (by omega)))
      have e : 1280 * n + i - 1280 * n = i := by omega
      simp [hi, h1, e]
    · have h2 : E.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hi, h2]
  · intro k hk
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Lanes.testBit_lane, Lanes.testBit_lane, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hi : i < 1280
    · have : ¬ (1280 * k + i ≥ 1280 * n) := by omega
      simp [hi, this]
    · simp [hi]

private theorem orb_mulB_lt (hrm : D.rm = 2 ^ 248 - 1) (A B : ℕ) :
    mulB (cR 5) D.rm A B < 2 ^ 1280 := by
  rw [hrm, Batches.cR_eq]
  exact lt_of_lt_of_le (Rows.mulB_lt 5 A B) (by norm_num)

private theorem orb_qBuild_succ (m : ℕ) :
    qBuild D O (m + 1) = qBuild D O m ||| (mulB (cR 5) D.rm (ptAt (qBuild D O m)
      (lget O.par (m + 1) &&& 255)) (gen D (lget O.par (m + 1) >>> 8))) <<< (1280 * (m + 1)) := by
  have e : qBuild D O (m + 1) = strictN (qBuild D O m) (fun S' => S' ||| (mulB (cR 5) D.rm
      (ptAt S' (lget O.par (m + 1) &&& 255)) (gen D (lget O.par (m + 1) >>> 8))) <<<
      (1280 * (m + 1))) := rfl
  exact e.trans (Lanes.strictN_eq _ _)

private theorem orb_qBuild_lt (hrm : D.rm = 2 ^ 248 - 1) (h9 : pt D O 9 < 2 ^ 1280) :
    ∀ m, qBuild D O m < 2 ^ (1280 * (m + 1))
  | 0 => h9
  | m + 1 => by
    rw [orb_qBuild_succ]
    exact (orb_lane_append (orb_qBuild_lt hrm h9 m) (orb_mulB_lt D hrm _ _)).1

private theorem orb_ptAt_succ (hrm : D.rm = 2 ^ 248 - 1) (h9 : pt D O 9 < 2 ^ 1280) (m : ℕ) :
    (∀ k ≤ m, ptAt (qBuild D O (m + 1)) k = ptAt (qBuild D O m) k) ∧
    ptAt (qBuild D O (m + 1)) (m + 1) = mulB (cR 5) D.rm (ptAt (qBuild D O m)
      (lget O.par (m + 1) &&& 255)) (gen D (lget O.par (m + 1) >>> 8)) := by
  have := orb_lane_append (orb_qBuild_lt D O hrm h9 m) (orb_mulB_lt D hrm
    (ptAt (qBuild D O m) (lget O.par (m + 1) &&& 255)) (gen D (lget O.par (m + 1) >>> 8)))
  rw [← orb_qBuild_succ] at this
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [Batches.ptAt_eq, Batches.ptAt_eq]
    exact this.2.2 k (by omega)
  · rw [Batches.ptAt_eq]
    exact this.2.1

private theorem orb_ptAt_stable (hrm : D.rm = 2 ^ 248 - 1) (h9 : pt D O 9 < 2 ^ 1280) {k n : ℕ}
    (hkn : k ≤ n) : ptAt (qBuild D O n) k = ptAt (qBuild D O k) k := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [(orb_ptAt_succ D O hrm h9 n).1 k hkn, ih]

private theorem orb_key_inj (f key : ℕ → ℕ) (hf : ∀ t < 248, f t < 248)
    (hmono : ∀ t < 247, key (f t) < key (f (t + 1))) :
    ∀ k < 248, ∀ k' < 248, key k = key k' → k = k' := by
  have hstrict : ∀ d t, t + d + 1 < 248 → key (f t) < key (f (t + d + 1)) := by
    intro d
    induction d with
    | zero => exact fun t ht => hmono t (by omega)
    | succ d ih =>
      exact fun t ht => lt_trans (ih t (by omega)) (hmono (t + d + 1) (by omega))
  have hinj : ∀ t < 248, ∀ t' < 248, key (f t) = key (f t') → t = t' := by
    intro t ht t' ht' e
    rcases lt_trichotomy t t' with hlt | rfl | hgt
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      exact absurd e (ne_of_lt (hstrict d t ht'))
    · rfl
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hgt
      exact absurd e.symm (ne_of_lt (hstrict d t' ht))
  have hsurj : Function.Surjective (fun t : Fin 248 => (⟨f t, hf t t.2⟩ : Fin 248)) :=
    Finite.injective_iff_surjective.mp fun a b e =>
      Fin.ext (hinj a a.2 b b.2 (by rw [show f a = f b from congrArg Fin.val e]))
  intro k hk k' hk' e
  obtain ⟨a, ha⟩ := hsurj ⟨k, hk⟩
  obtain ⟨b, hb⟩ := hsurj ⟨k', hk'⟩
  have ha' : f a = k := congrArg Fin.val ha
  have hb' : f b = k' := congrArg Fin.val hb
  rw [← ha', ← hb'] at e ⊢
  exact congrArg _ (hinj a a.2 b b.2 e)

private theorem orb_bitB_bitsOf (l : List ℕ) (p : ℕ) : bitB (bitsOf l) p = true ↔ p ∈ l := by
  have hb : ∀ F : ℕ, bitB F p = F.testBit p := fun F => by
    unfold bitB
    change Nat.beq ((F >>> p) &&& 1) 1 = F.testBit p
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq,
      Bool.eq_iff_iff]
    simp
  rw [hb]
  induction l with
  | nil => simp [bitsOf]
  | cons a l ih =>
    have e : bitsOf (a :: l) = bitsOf l ||| 1 <<< a := rfl
    rw [e, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h

end

theorem orbChk_sound (h : orbChk D O = true) (hrm : D.rm = 2 ^ 248 - 1)
    (h9 : pt D O 9 < 2 ^ 1280) :
    O.fx5.length = 3 ∧ (ptAt (qStack D O) 0 = pt D O 9) ∧
    (∀ k, 0 < k → k < 248 → ∃ p < k, ∃ g < 2,
      ptAt (qStack D O) k = mulB (cR 5) D.rm (ptAt (qStack D O) p) (gen D g)) ∧
    (∀ q < 248, ∀ g < 2, ∃ j < 248, ∃ G,
      combChk D.rm (mulB (cR 5) D.rm (ptAt (qStack D O) q) (gen D g)) (ptAt (qStack D O) j) G = true) ∧
    (∀ k < 248, ∀ k' < 248, keyAt (keys248 D (qStack D O)) k = keyAt (keys248 D (qStack D O)) k' →
      k = k') ∧
    (∀ k < 248, keyAt (keys248 D (qStack D O)) k =
        keyAt (keys248 D (mulB (cR 1240) D.rm (qStack D O) (chainEl D O.x5))) k → k ∈ O.fx5) := by
  set_option exponentiation.threshold 2000 in
  have hstab : ∀ k ≤ 247, ptAt (qStack D O) k = ptAt (qBuild D O k) k := fun k hk =>
    orb_ptAt_stable D O hrm h9 hk
  unfold orbChk at h
  obtain ⟨hfx, h⟩ := Unfold.andB_split h
  obtain ⟨-, h⟩ := Unfold.andB_split h
  obtain ⟨-, h⟩ := Unfold.andB_split h
  obtain ⟨-, h⟩ := Unfold.andB_split h
  obtain ⟨hpar, h⟩ := Unfold.andB_split h
  simp only [Batches.strictB_eq] at h
  obtain ⟨hord, h⟩ := Unfold.andB_split h
  obtain ⟨hkey, h⟩ := Unfold.andB_split h
  obtain ⟨hedge, hfix⟩ := Unfold.andB_split h
  refine ⟨Nat.eq_of_beq_eq_true hfx, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hstab 0 (by omega)]
    show ptAt (pt D O 9) 0 = pt D O 9
    rw [Batches.ptAt_eq]
    simpa [Lanes.lane] using Nat.mod_eq_of_lt h9
  ·
    intro k hk0 hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hm : m < 247 := by omega
    obtain ⟨hp1, hp2⟩ := Unfold.andB_split (Unfold.allBelow_spec hpar (by decide) m hm)
    have hp1' : lget O.par (m + 1) &&& 255 < m + 1 := Nat.blt_eq.mp hp1
    refine ⟨lget O.par (m + 1) &&& 255, hp1', lget O.par (m + 1) >>> 8, Nat.blt_eq.mp hp2, ?_⟩
    rw [hstab (m + 1) (by omega), (orb_ptAt_succ D O hrm h9 m).2, hstab _ (by omega),
      orb_ptAt_stable D O hrm h9 (by omega)]
  ·
    intro q hq g hg
    have he : ∀ t < 496, lget O.edges t &&& 255 < 248 ∧
        combChk D.rm (mulB (cR 5) D.rm (ptAt (qStack D O) (t >>> 1)) (gen D (t &&& 1)))
          (ptAt (qStack D O) (lget O.edges t &&& 255)) (lget O.edges t >>> 8) = true := by
      intro t ht
      obtain ⟨h1, h2⟩ := Unfold.andB_split (Unfold.allBelow_spec hedge (by decide) t ht)
      exact ⟨Nat.blt_eq.mp h1, h2⟩
    obtain ⟨he1, he2⟩ := he (2 * q + g) (by omega)
    have e1 : (2 * q + g) >>> 1 = q := by omega
    have e2 : (2 * q + g) &&& 1 = g := by rw [Nat.and_one_is_mod]; omega
    rw [e1, e2] at he2
    exact ⟨_, he1, _, he2⟩
  ·
    refine orb_key_inj (lget O.ord) (keyAt (keys248 D (qStack D O))) (fun t ht => ?_)
      (fun t ht => ?_)
    · exact Nat.blt_eq.mp (Unfold.allBelow_spec hord (by decide) t ht)
    · exact Nat.blt_eq.mp (Unfold.allBelow_spec hkey (by decide) t ht)
  ·
    intro k hk e
    by_contra hmem
    have hk' := Unfold.allBelow_spec hfix (by decide) k hk
    have hb : bitB (bitsOf O.fx5) k = false := by
      cases hb : bitB (bitsOf O.fx5) k
      · rfl
      · exact absurd ((orb_bitB_bitsOf _ _).mp hb) hmem
    rw [hb] at hk'
    have h1 : BigS.notB (Nat.beq (keyAt (keys248 D (qStack D O)) k)
        (keyAt (keys248 D (mulB (cR 1240) D.rm (qStack D O) (chainEl D O.x5))) k)) = true := hk'
    have h2 := Unfold.notB_true h1
    rw [e, Nat.beq_refl] at h2
    exact Bool.noConfusion h2

end CFSG.Certificates.ThDemp.Facts

end
