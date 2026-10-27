module

public import Certificates.Data.Kernel.Fi22Omega.Check
public import CFSG.Certificates.Kernel.BenesSound
public import CFSG.Certificates.Kernel.PackSetSound
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.End

public section

namespace CFSG.KC.Fi22Omega

open Equiv CFSG.KC.Benes CFSG.KC.MonsterConv.Perm CFSG.KC.Enum
open scoped Pointwise

@[expose] def maskSet (M : Nat) : Set (Fin 3510) := {p | M.testBit p = true}

theorem band_true {a b : Bool} (h : band a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem rec_true {c x y : Bool} (h : Bool.rec (motive := fun _ => Bool) x y c = true)
    (hc : c = true) : y = true := by
  subst hc
  exact h

theorem rec_false {c x y : Bool} (h : Bool.rec (motive := fun _ => Bool) x y c = true)
    (hc : c = false) : x = true := by
  subst hc
  exact h

theorem lt_of_shiftRight_eq_zero {S n : Nat} (h : S >>> n = 0) : S < 2 ^ n := by
  rw [Nat.shiftRight_eq_div_pow] at h
  rcases Nat.lt_or_ge S (2 ^ n) with hl | hl
  · exact hl
  · have := Nat.div_pos hl (Nat.two_pow_pos n)
    omega

theorem allBlk_true {b : Nat} {f : Nat → Bool} : ∀ {len : Nat}, allBlk b f len = true →
    ∀ l < len, f (b + l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
      at h
    cases h1 : f (Nat.add b len) <;> rw [h1] at h
    · exact absurd (h : false = true) Bool.false_ne_true
    rcases Nat.lt_or_ge l len with h2 | h2
    · exact allBlk_true h l h2
    · have e : l = len := by omega
      subst e
      exact h1

theorem testBit_img {N S : Nat} (hN : StagesValid 12 N) {r : Nat} (hr : r < 4096) :
    (img N S).testBit r = S.testBit (benesPerm 12 N r) := by
  have hq : benesPerm (nat_lit 12) N r < 4096 :=
    lt_of_lt_of_eq (benesPerm_lt (k := nat_lit 12) hN (lt_of_lt_of_eq hr (by decide)))
      (by decide)
  have h := (testBit_netApply (k := nat_lit 12) (W := nat_lit 4096) (P := nat_lit 2) (by decide)
    hN (Nat.lor S (Nat.shiftLeft salt (nat_lit 4096)))).1 0 (by decide) r hr
  rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add] at h
  unfold img
  rw [nland, Nat.testBit_and, h, ones_eq, Nat.testBit_two_pow_sub_one, nlor, Nat.testBit_or, nshl,
    Nat.testBit_shiftLeft]
  have e1 : decide (r < nat_lit 4096) = true := decide_eq_true hr
  have hq' : ¬ (benesPerm (nat_lit 12) N r ≥ nat_lit 4096) := Nat.not_le.mpr hq
  have e2 : decide (benesPerm (nat_lit 12) N r ≥ nat_lit 4096) = false := decide_eq_false hq'
  rw [e1, e2, Bool.false_and, Bool.or_false, Bool.and_true]

theorem testBit_img_ge {N S : Nat} {r : Nat} (hr : 4096 ≤ r) : (img N S).testBit r = false := by
  unfold img
  rw [nland, Nat.testBit_and, ones_eq, Nat.testBit_two_pow_sub_one]
  have hr' : ¬ (r < nat_lit 4096) := Nat.not_lt.mpr hr
  have e : decide (r < nat_lit 4096) = false := decide_eq_false hr'
  rw [e, Bool.and_false]

theorem img_sound {N S : Nat} {σ : Perm (Fin 3510)} (hN : StagesValid 12 N)
    (hσ : ∀ p : Fin 3510, benesPerm 12 N p = (σ⁻¹ p : Nat)) (hS : S < 2 ^ 3510) :
    maskSet (img N S) = σ • maskSet S ∧ img N S < 2 ^ 3510 := by
  refine ⟨?_, lt_of_testBit_ge fun q hq => ?_⟩
  · ext p
    rw [Set.mem_smul_set_iff_inv_smul_mem, Perm.smul_def]
    change (img N S).testBit p = true ↔ S.testBit (σ⁻¹ p) = true
    have hp := p.2
    rw [testBit_img hN (by omega), hσ p]
  · rcases Nat.lt_or_ge q 4096 with h4 | h4
    · rw [testBit_img hN h4]
      have hb : 3510 ≤ benesPerm 12 N q := by
        by_contra hlt
        have e := hσ (σ ⟨benesPerm 12 N q, by omega⟩)
        have hinv : ∀ x, σ⁻¹ (σ x) = x := fun x => by simp
        rw [hinv] at e
        have e' := congrArg (benesInv 12 N) e
        simp only [Fin.val_mk] at e'
        rw [benesInv_benesPerm hN, benesInv_benesPerm hN] at e'
        have := (σ ⟨benesPerm 12 N q, by omega⟩).2
        omega
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hS (Nat.pow_le_pow_right (n := 2) (by decide) hb))
    · exact testBit_img_ge h4

theorem testBit_orPlanes {S : Nat} (h sh : Nat → Nat) (hsh : ∀ k, sh k = k * S) : ∀ n,
    (∀ k < n, h k < 2 ^ S) →
    Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.lor acc (Nat.shiftLeft (h k) (sh k))) n <
      2 ^ (n * S) ∧
    ∀ b < n, ∀ p < S, (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.lor acc (Nat.shiftLeft (h k) (sh k))) n).testBit (b * S + p) =
        (h b).testBit p
  | 0, _ => ⟨Nat.two_pow_pos _, fun b hb => absurd hb (Nat.not_lt_zero b)⟩
  | n + 1, hh => by
    obtain ⟨ih1, ih2⟩ := testBit_orPlanes h sh hsh n fun k hk => hh k (by omega)
    have hsl : Nat.shiftLeft (h n) (sh n) < 2 ^ ((n + 1) * S) := by
      rw [hsh, nshl, Nat.shiftLeft_eq, Nat.succ_mul, Nat.pow_add, Nat.mul_comm (2 ^ (n * S))]
      exact Nat.mul_lt_mul_of_pos_right (hh n (by omega)) (Nat.two_pow_pos _)
    change Nat.lor (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.lor acc (Nat.shiftLeft (h k) (sh k))) n) (Nat.shiftLeft (h n) (sh n)) <
        _ ∧ ∀ b < n + 1, ∀ p < S, (Nat.lor (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.lor acc (Nat.shiftLeft (h k) (sh k))) n)
        (Nat.shiftLeft (h n) (sh n))).testBit (b * S + p) = (h b).testBit p
    refine ⟨Nat.or_lt_two_pow (lt_of_lt_of_le ih1 (Nat.pow_le_pow_right (by omega)
      (Nat.mul_le_mul_right S (Nat.le_succ n)))) hsl, fun b hb p hp => ?_⟩
    rw [nlor, Nat.testBit_or, nshl, Nat.testBit_shiftLeft, hsh]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
    · have hlt : b * S + p < n * S := by
        have := Nat.mul_le_mul_right S (Nat.succ_le_of_lt hb)
        rw [Nat.succ_mul] at this
        omega
      rw [ih2 b hb p hp]
      have : ¬ (b * S + p ≥ n * S) := by omega
      simp [this]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ih1 (Nat.pow_le_pow_right (by omega)
        (Nat.le_add_right _ _)))]
      have e : b * S + p - b * S = p := by omega
      simp [e]

theorem ext_lt4096 {G p : Nat} (hp : p < 4096) : ext G p < 2 ^ 12 := by
  unfold ext
  cases hb : Nat.blt p (nat_lit 3510)
  · exact lt_of_lt_of_eq hp (by decide)
  · change (G >>> (12 * p)) &&& 4095 < 2 ^ 12
    exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem testBit_planes {G b p : Nat} (hb : b < 12) (hp : p < 4096) :
    (planes G).testBit (4096 * b + p) = (ext G p).testBit b := by
  have hpl : ∀ c, plane G c < 2 ^ 4096 := by
    intro c
    have h := (testBit_orPlanes (S := 1)
      (fun p => Nat.land (Nat.shiftRight (ext G p) c) (nat_lit 1)) (fun p => p)
      (fun k => (Nat.mul_one k).symm) 4096
      (fun k _ => lt_of_le_of_lt Nat.and_le_right (by decide))).1
    rw [Nat.mul_one] at h
    exact h
  have h1 := (testBit_orPlanes (S := 4096) (fun c => plane G c) (fun c => Nat.mul c (nat_lit 4096))
    (fun k => rfl) 12 fun k _ => hpl k).2 b hb p hp
  rw [Nat.mul_comm 4096 b]
  refine h1.trans ?_
  have h2 := (testBit_orPlanes (S := 1)
      (fun p => Nat.land (Nat.shiftRight (ext G p) b) (nat_lit 1)) (fun p => p)
      (fun k => (Nat.mul_one k).symm) 4096
      (fun k _ => lt_of_le_of_lt Nat.and_le_right (by decide))).2 p hp 0 (by decide)
  rw [Nat.mul_one, Nat.add_zero] at h2
  refine h2.trans ?_
  change ((ext G p >>> b) &&& 1).testBit 0 = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_zero]
  cases (ext G p).testBit b <;> rfl

theorem testBit_idP12 {u r : Nat} (hu : u < 12) (hr : r < 4096) :
    (idP 12).testBit (4096 * u + r) = r.testBit u := by
  have e : Nat.shiftLeft (nat_lit 1) (nat_lit 12) = 2 ^ 12 := rfl
  have e2 : (2 : Nat) ^ 12 = 4096 := rfl
  have hpl : ∀ c < 12, idPlane (Nat.shiftLeft (nat_lit 1) (nat_lit 12)) c < 2 ^ 4096 := by
    intro c hc
    rw [e]
    refine lt_of_testBit_ge fun q hq => ?_
    rw [idPlane_testBit hc, e2]
    have : ¬ q < 4096 := by omega
    simp [this]
  have h1 := (testBit_orPlanes (S := 4096)
    (fun c => idPlane (Nat.shiftLeft (nat_lit 1) (nat_lit 12)) c)
    (fun c => Nat.mul c (Nat.shiftLeft (nat_lit 1) (nat_lit 12))) (fun k => rfl) 12 hpl).2 u hu r hr
  rw [Nat.mul_comm 4096 u]
  refine h1.trans ?_
  have h3 := idPlane_testBit (k := 12) hu r
  rw [e2, decide_eq_true hr, Bool.true_and] at h3
  exact h3

theorem bindOK_sound {NT : Nat → Nat} {G l : Nat} (h : bindOK NT G l = true) :
    StagesValid 12 (NT l) ∧ ∀ r < 4096, ext G (benesPerm 12 (NT l) r) = r := by
  obtain ⟨h1, h2⟩ := band_true h
  have hN := stagesValid_of_netValid h1
  refine ⟨hN, fun r hr => ?_⟩
  have E := Nat.eq_of_beq_eq_true h2
  have hq : benesPerm (nat_lit 12) (NT l) r < 4096 :=
    lt_of_lt_of_eq (benesPerm_lt (k := nat_lit 12) hN (lt_of_lt_of_eq hr (by decide))) (by decide)
  have hlt : ext G (benesPerm 12 (NT l) r) < 2 ^ 12 := ext_lt4096 hq
  apply Nat.eq_of_testBit_eq
  intro u
  rcases Nat.lt_or_ge u 12 with hu | hu
  · have h3 := (testBit_netApply (k := nat_lit 12) (W := nat_lit 4096) (P := nat_lit 12)
      (by decide) hN (planes G)).1 u hu r hr
    rw [E, testBit_idP12 hu hr, testBit_planes hu hq] at h3
    exact h3.symm
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hu)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (lt_of_lt_of_eq hr (by decide))
        (Nat.pow_le_pow_right (by omega) hu))]

theorem ext_of_lt {G p : Nat} (h : p < 3510) : ext G p = pg 12 4095 G p := by
  have hb : Nat.blt p (nat_lit 3510) = true := Nat.blt_eq.mpr h
  unfold ext
  rw [hb]

theorem ext_of_ge {G p : Nat} (h : 3510 ≤ p) : ext G p = p := by
  have hb : Nat.blt p (nat_lit 3510) = false := by
    cases e : Nat.blt p (nat_lit 3510)
    · rfl
    · exact absurd (Nat.blt_eq.mp e) (Nat.not_lt.mpr h)
  unfold ext
  rw [hb]

theorem netActs_of_bind {NT : Nat → Nat} {G l : Nat} {σ : Perm (Fin 3510)}
    (h : bindOK NT G l = true) (hG : ∀ q : Fin 3510, pg 12 4095 G q = (σ q : Nat)) :
    StagesValid 12 (NT l) ∧ ∀ p : Fin 3510, benesPerm 12 (NT l) p = (σ⁻¹ p : Nat) := by
  obtain ⟨hv, hb⟩ := bindOK_sound h
  refine ⟨hv, fun p => ?_⟩
  have hp0 := p.2
  have hp := hb p (by omega)
  rcases Nat.lt_or_ge (benesPerm 12 (NT l) p) 3510 with h3 | h3
  · rw [ext_of_lt h3] at hp
    have e := hG ⟨_, h3⟩
    rw [hp] at e
    have e' : σ ⟨_, h3⟩ = p := Fin.ext e.symm
    have hinv : ∀ x, σ⁻¹ (σ x) = x := fun x => by simp
    have e2 : σ⁻¹ p = ⟨_, h3⟩ := by
      have := congrArg (fun x => σ⁻¹ x) e'
      simp only [hinv] at this
      exact this.symm
    rw [e2]
  · rw [ext_of_ge h3] at hp
    omega

theorem nodes_of_chunks {T NT RT : Nat → Nat} (h : ∀ c < 966, chunkOK T NT RT c = true) :
    ∀ i < 61776, nodeOK T NT RT i = true := by
  intro i hi
  have hc := allBlk_true (h (i / 64) (by omega)) (i % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.mul (nat_lit 64) (i / 64) + i % 64 = i := Nat.div_add_mod i 64
  rw [e] at hc
  exact rec_true hc (Nat.blt_eq.mpr hi)

theorem nodeOK_sound {T NT RT : Nat → Nat} {i : Nat} (h : nodeOK T NT RT i = true) :
    msk (recAt T i) < 2 ^ 3510 ∧
    (i + 1 < 61776 → key (msk (recAt T i)) < key (msk (recAt T (i + 1)))) ∧
    blkF (recAt T i) < 4 ∧
    (depF (recAt T i) = 0 → i = RT (blkF (recAt T i))) ∧
    (depF (recAt T i) ≠ 0 → parF (recAt T i) < 61776 ∧ letF (recAt T i) < 2 ∧
      depF (recAt T (parF (recAt T i))) + 1 = depF (recAt T i) ∧
      blkF (recAt T (parF (recAt T i))) = blkF (recAt T i) ∧
      img (NT (letF (recAt T i))) (msk (recAt T (parF (recAt T i)))) = msk (recAt T i)) := by
  unfold nodeOK at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h2⟩ := band_true h
  obtain ⟨h3, h4⟩ := band_true h2
  obtain ⟨h5, h6⟩ := band_true h4
  refine ⟨lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true h1),
    fun hi => Nat.blt_eq.mp (rec_true h3 (Nat.blt_eq.mpr hi)), Nat.blt_eq.mp h5,
    fun hd => Nat.eq_of_beq_eq_true (rec_true h6 (Nat.beq_eq.mpr hd)), fun hd => ?_⟩
  have hb : Nat.beq (depF (recAt T i)) 0 = false := by
    cases e : Nat.beq (depF (recAt T i)) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hd
  have h7 := rec_false h6 hb
  unfold edgeOK at h7
  simp only [strictB_eq] at h7
  obtain ⟨g1, g2⟩ := band_true h7
  obtain ⟨g3, g4⟩ := band_true g2
  obtain ⟨g5, g6⟩ := band_true g4
  obtain ⟨g7, g8⟩ := band_true g6
  exact ⟨Nat.blt_eq.mp g1, Nat.blt_eq.mp g3, Nat.eq_of_beq_eq_true g5,
    Nat.eq_of_beq_eq_true g7, Nat.eq_of_beq_eq_true g8⟩

theorem cntOK_sound {T : Nat → Nat} (h : cntOK T = true)
    (hb : ∀ i < 61776, blkF (recAt T i) < 4) (c : Nat) (hc : c < 4) :
    ((Finset.range 61776).filter fun i => blkF (recAt T i) = c).card =
      [1, 37800, 22400, 1575].getD c 0 := by
  have hfold : ∀ n s, (List.range n).foldr (fun i acc => Nat.add acc
      (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 20) (blkF (recAt T i))))) s =
        s + ∑ i ∈ Finset.range n, 2 ^ (20 * blkF (recAt T i)) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih,
        Finset.sum_range_succ]
      change s + 1 <<< (20 * blkF (recAt T n)) + _ = _
      rw [Nat.one_shiftLeft]
      omega
  have hsum : cnt T 61776 = ∑ i ∈ Finset.range 61776, 2 ^ (20 * blkF (recAt T i)) := by
    unfold cnt
    rw [CFSG.KC.Pack.foldN_eq, hfold, Nat.zero_add]
  have hfib : ∑ i ∈ Finset.range 61776, 2 ^ (20 * blkF (recAt T i)) =
      ∑ j ∈ Finset.range 4,
        ((Finset.range 61776).filter fun i => blkF (recAt T i) = j).card * 2 ^ (20 * j) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => blkF (recAt T i)) (t := Finset.range 4)
      (fun i hi => Finset.mem_range.2 (hb i (Finset.mem_range.1 hi)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const,
      smul_eq_mul]
  have hk : ∀ j, ((Finset.range 61776).filter fun i => blkF (recAt T i) = j).card ≤ 61776 :=
    fun j => (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  have he : cnt T 61776 = Nat.add (nat_lit 1) (Nat.add (Nat.shiftLeft (nat_lit 37800) (nat_lit 20))
      (Nat.add (Nat.shiftLeft (nat_lit 22400) (nat_lit 40))
        (Nat.shiftLeft (nat_lit 1575) (nat_lit 60)))) := Nat.eq_of_beq_eq_true h
  rw [hsum, hfib] at he
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, nadd, nshl, Nat.reduceShiftLeft,
    Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.zero_add] at he
  have k0 := hk 0
  have k1 := hk 1
  have k2 := hk 2
  have k3 := hk 3
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
  · change _ = 1
    omega
  · change _ = 37800
    omega
  · change _ = 22400
    omega
  · change _ = 1575
    omega

theorem mapsOK_sound {A : Nat → Nat} {w : Nat} {M M' : Nat} :
    ∀ {L : List Nat}, mapsOK A w L M M' = true →
      ∀ p ∈ L, M.testBit p = true → M'.testBit (wordPt A 128 w p) = true
  | [], _, p, hp, _ => absurd hp List.not_mem_nil
  | q :: L, h, p, hp, hM => by
    obtain ⟨h1, h2⟩ := band_true h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact rec_true h1 hM
    · exact mapsOK_sound h2 p hp hM

theorem testBit_wordMask {A : Nat → Nat} {w q : Nat} :
    ∀ {L : List Nat}, (wordMask A w L).testBit q = true ↔ ∃ p ∈ L, wordPt A 128 w p = q
  | [] => by
    change (0 : Nat).testBit q = true ↔ _
    simp
  | p :: L => by
    change (Nat.lor (Nat.shiftLeft 1 (wordPt A 128 w p)) (wordMask A w L)).testBit q = true ↔ _
    rw [nlor, nshl, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_wordMask]
    simp only [decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (e | ⟨r, hr, e⟩)
      · exact ⟨p, Or.inl rfl, e⟩
      · exact ⟨r, Or.inr hr, e⟩
    · rintro ⟨r, hr | hr, e⟩
      · subst hr
        exact Or.inl e
      · exact Or.inr ⟨r, hr, e⟩

end CFSG.KC.Fi22Omega

end
