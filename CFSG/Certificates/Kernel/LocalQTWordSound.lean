module

public import Certificates.Data.Kernel.LocalQT.Word
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.Certificates.Kernel.LocalQTPermSound
public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.KC.LQT.W

open Equiv CFSG.SectionRank
open scoped commutatorElement

private theorem andT {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KC.Ord.andB]

private theorem ne_of_notB {x y : ℕ} (h : CFSG.KC.Ord.notB (Nat.beq x y) = true) : x ≠ y := by
  intro hxy
  rw [hxy] at h
  cases hb : Nat.beq y y
  · exact Nat.ne_of_beq_eq_false hb rfl
  · rw [hb] at h
    exact absurd h (by decide)

private theorem letB_eq (y : ℕ) (k : ℕ → Bool) : P.letB y k = k y := by
  cases y <;> rfl

private theorem img_eq (s i : ℕ) : P.img s i = s / 32 ^ i % 32 := by
  change (s >>> (5 * i)) &&& (2 ^ 5 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

private theorem ofFn_sum (n : ℕ) (g : ℕ → ℕ) :
    P.ofFn n g = ∑ i ∈ Finset.range n, g i * 32 ^ i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change P.ofFn n g + g n <<< (5 * n) = _
    rw [Finset.sum_range_succ, ih, Nat.shiftLeft_eq, Nat.pow_mul]

private theorem inv_sum (n s : ℕ) : P.inv n s = ∑ i ∈ Finset.range n, i * 32 ^ P.img s i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change P.inv n s + n <<< (5 * P.img s n) = _
    rw [Finset.sum_range_succ, ih, Nat.shiftLeft_eq, Nat.pow_mul]

private theorem ofFn_succ (n : ℕ) (g : ℕ → ℕ) : P.ofFn (n + 1) g = P.ofFn n g + g n * 32 ^ n := by
  rw [ofFn_sum, ofFn_sum, Finset.sum_range_succ]

private theorem ofFn_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    P.ofFn n f = P.ofFn n g := by
  rw [ofFn_sum, ofFn_sum]
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

private theorem ofFn_lt {n : ℕ} {g : ℕ → ℕ} (hg : ∀ i < n, g i < 32) : P.ofFn n g < 32 ^ n := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    have h1 := ih fun i hi => hg i (by omega)
    have h2 : g n * 32 ^ n ≤ 31 * 32 ^ n := Nat.mul_le_mul_right _ (by have := hg n (by omega); omega)
    rw [ofFn_succ, pow_succ]
    omega

private theorem img_ofFn {n : ℕ} {g : ℕ → ℕ} (hg : ∀ i < n, g i < 32) {i : ℕ} (hi : i < n) :
    P.img (P.ofFn n g) i = g i := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hA := ofFn_lt (n := n) (g := g) fun j hj => hg j (by omega)
    rw [img_eq, ofFn_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · have e0 : (32 : ℕ) ^ n = 32 ^ i * 32 ^ (n - i - 1) * 32 := by
        rw [← Nat.pow_add, ← Nat.pow_succ]
        congr 1
        omega
      have e : g n * 32 ^ n = 32 ^ i * (g n * 32 ^ (n - i - 1) * 32) := by
        rw [e0]
        ring
      rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_right, ← img_eq]
      exact ih (fun j hj => hg j (by omega)) hi
    · subst hi
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hA, Nat.zero_add,
        Nat.mod_eq_of_lt (hg _ (Nat.lt_succ_self _))]

private noncomputable def cd {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  P.ofFn n fun i => if h : i < n then (σ ⟨i, h⟩ : ℕ) else 0

private def Rep (n s : ℕ) (σ : Perm (Fin n)) : Prop := ∀ i : Fin n, P.img s i = σ i

private theorem cd_lt {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n)) :
    ∀ j < n, (if h : j < n then (σ ⟨j, h⟩ : ℕ) else 0) < 32 := fun j hj => by
  rw [dite_eq_left hj]
  have := (σ ⟨j, hj⟩).isLt
  omega

private theorem rep_cd {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n)) : Rep n (cd σ) σ := by
  intro i
  unfold cd
  rw [img_ofFn (cd_lt hn σ) i.isLt, dite_eq_left i.isLt]

private theorem cd_inj {n : ℕ} (hn : n ≤ 32) {σ τ : Perm (Fin n)} (h : cd σ = cd τ) : σ = τ :=
  Equiv.ext fun i => Fin.ext (by rw [← rep_cd hn σ i, ← rep_cd hn τ i, h])

private theorem mul_rep {n s t : ℕ} {σ τ : Perm (Fin n)} (hs : Rep n s σ) (ht : Rep n t τ) :
    P.mul n s t = cd (σ * τ) := by
  refine ofFn_congr fun i hi => ?_
  have hti : P.img t i = τ ⟨i, hi⟩ := ht ⟨i, hi⟩
  rw [hti, hs (τ ⟨i, hi⟩), dite_eq_left hi, Perm.mul_apply]

private theorem inv_rep {n s : ℕ} {σ : Perm (Fin n)} (hs : Rep n s σ) : P.inv n s = cd σ⁻¹ := by
  rw [inv_sum, cd, ofFn_sum, Finset.sum_range, Finset.sum_range]
  exact Fintype.sum_equiv σ _ _ fun i => by rw [hs i, dite_eq_left (σ i).isLt]; simp

private theorem one_eq (n : ℕ) : P.one n = cd (1 : Perm (Fin n)) :=
  ofFn_congr fun i hi => by rw [dite_eq_left hi, Perm.one_apply]

private theorem pow_rep {n s : ℕ} (hn : n ≤ 32) {σ : Perm (Fin n)} (hs : Rep n s σ) :
    ∀ k, P.pow n s k = cd (σ ^ k)
  | 0 => by rw [pow_zero]; exact one_eq n
  | k + 1 => by
    change P.mul n (P.pow n s k) s = _
    rw [pow_rep hn hs k, mul_rep (rep_cd hn _) hs, pow_succ]

private theorem mul_cd {n : ℕ} (hn : n ≤ 32) (σ τ : Perm (Fin n)) :
    P.mul n (cd σ) (cd τ) = cd (σ * τ) :=
  mul_rep (rep_cd hn σ) (rep_cd hn τ)

private theorem inv_cd {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n)) : P.inv n (cd σ) = cd σ⁻¹ :=
  inv_rep (rep_cd hn σ)

private theorem pow_cd {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n)) (k : ℕ) :
    P.pow n (cd σ) k = cd (σ ^ k) :=
  pow_rep hn (rep_cd hn σ) k

private theorem n_le {n c : ℕ} {σ : Perm (Fin n)} (h : ∀ i : Fin n, (σ i : ℕ) = P.img c i) :
    n ≤ 32 := by
  by_contra hn
  have hn' : 32 < n := by omega
  have h1 := h (σ⁻¹ ⟨32, hn'⟩)
  have e : σ (σ⁻¹ ⟨32, hn'⟩) = ⟨32, hn'⟩ := σ.apply_symm_apply _
  rw [e] at h1
  have h2 : P.img c (σ⁻¹ ⟨32, hn'⟩) < 32 := by
    rw [img_eq]
    exact Nat.mod_lt _ (by norm_num)
  change 32 = _ at h1
  omega

private theorem char_of {ch c : Char} (h : ch.toNat = c.toNat) : ch = c :=
  Char.ext (UInt32.toNat_inj.mp h)

private theorem letter_eq (n ca cb : ℕ) (ch : Char) :
    Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (P.inv n cb) cb (Nat.beq (Char.toNat ch) 98)) ca
      (Nat.beq (Char.toNat ch) 97) =
      if ch = 'a' then ca else if ch = 'b' then cb else P.inv n cb := by
  cases h1 : Nat.beq (Char.toNat ch) 97
  · have ha : ch ≠ 'a' := by
      rintro rfl
      exact absurd h1 (by decide)
    rw [ite_eq_right ha]
    cases h2 : Nat.beq (Char.toNat ch) 98
    · have hb : ch ≠ 'b' := by
        rintro rfl
        exact absurd h2 (by decide)
      rw [ite_eq_right hb]
    · rw [ite_eq_left (char_of (c := 'b') (Nat.eq_of_beq_eq_true h2))]
  · rw [ite_eq_left (char_of (c := 'a') (Nat.eq_of_beq_eq_true h1))]

private theorem wordC_eq {n : ℕ} (hn : n ≤ 32) {ca cb : ℕ} {a b : Perm (Fin n)} (ha : Rep n ca a)
    (hb : Rep n cb b) : ∀ l : List Char, wordC n ca cb l = cd (mathieuWord a b l)
  | [] => one_eq n
  | ch :: l => by
    have e : wordC n ca cb (ch :: l) = P.mul n (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ) (P.inv n cb) cb (Nat.beq (Char.toNat ch) 98)) ca
        (Nat.beq (Char.toNat ch) 97)) (wordC n ca cb l) := rfl
    have e2 : mathieuWord a b (ch :: l) =
        (if ch = 'a' then a else if ch = 'b' then b else b⁻¹) * mathieuWord a b l := rfl
    have hL : Rep n (if ch = 'a' then ca else if ch = 'b' then cb else P.inv n cb)
        (if ch = 'a' then a else if ch = 'b' then b else b⁻¹) := by
      split_ifs
      · exact ha
      · exact hb
      · rw [inv_rep hb]
        exact rep_cd hn _
    rw [e, e2, letter_eq, wordC_eq hn ha hb l, mul_rep hL (rep_cd hn _)]

private theorem map_word {G H : Type*} [Group G] [Group H] (f : G →* H) (a b : G) :
    ∀ l, f (mathieuWord a b l) = mathieuWord (f a) (f b) l
  | [] => map_one f
  | ch :: l => by
    have e1 : mathieuWord a b (ch :: l) =
        (if ch = 'a' then a else if ch = 'b' then b else b⁻¹) * mathieuWord a b l := rfl
    have e2 : mathieuWord (f a) (f b) (ch :: l) =
        (if ch = 'a' then f a else if ch = 'b' then f b else (f b)⁻¹) *
          mathieuWord (f a) (f b) l := rfl
    rw [e1, e2, map_mul, map_word f a b l]
    congr 1
    split_ifs <;> simp

private theorem allN_spec {m : ℕ} {f : ℕ → Bool} (h : P.allN m f = true) :
    ∀ i < m, f i = true := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    obtain ⟨h1, h2⟩ := andT h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

private theorem distinct_spec {m : ℕ} {f : ℕ → ℕ} (h : distinct m f = true) :
    ∀ i < m, ∀ j < i, f i ≠ f j := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    obtain ⟨h1, h2⟩ := andT h
    intro i hi j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h2 i hi j hj
    · exact ne_of_notB (allN_spec (f := fun j => CFSG.KC.Ord.notB (Nat.beq (f i) (f j))) h1 j hj)

theorem sq3_sound {n : ℕ} {S : Subgroup (Perm (Fin n))} (A B : S) {ca cb : ℕ}
    (hA : ∀ i : Fin n, ((A : Perm (Fin n)) i : ℕ) = P.img ca i)
    (hB : ∀ i : Fin n, ((B : Perm (Fin n)) i : ℕ) = P.img cb i) {lx ly lh : List Char}
    {a b c d : ℕ} (hk : sq3OK n ca cb lx ly lh a b c d = true) :
    mathieuWord A B lx ^ 3 = 1 ∧ mathieuWord A B ly ^ 3 = 1 ∧
      mathieuWord A B lx * mathieuWord A B ly = mathieuWord A B ly * mathieuWord A B lx ∧
      (Function.Injective fun t : Fin 3 × Fin 3 =>
        mathieuWord A B lx ^ (t.1 : ℕ) * mathieuWord A B ly ^ (t.2 : ℕ)) ∧
      mathieuWord A B lh * mathieuWord A B lx * (mathieuWord A B lh)⁻¹ =
        mathieuWord A B lx ^ a * mathieuWord A B ly ^ b ∧
      mathieuWord A B lh * mathieuWord A B ly * (mathieuWord A B lh)⁻¹ =
        mathieuWord A B lx ^ c * mathieuWord A B ly ^ d := by
  have hn := n_le hA
  have ew : ∀ l, wordC n ca cb l = cd (S.subtype (mathieuWord A B l)) := fun l => by
    rw [wordC_eq hn (a := (A : Perm (Fin n))) (b := (B : Perm (Fin n))) (fun i => (hA i).symm)
      (fun i => (hB i).symm), map_word]
    rfl
  simp only [sq3OK, sq3C, letB_eq, ew] at hk
  generalize mathieuWord A B lx = x at hk ⊢
  generalize mathieuWord A B ly = y at hk ⊢
  generalize mathieuWord A B lh = h at hk ⊢
  simp only [mul_cd hn, inv_cd hn, pow_cd hn, one_eq, P.conj, P.comm] at hk
  obtain ⟨h1, hk⟩ := andT hk
  obtain ⟨h2, hk⟩ := andT hk
  obtain ⟨h3, hk⟩ := andT hk
  obtain ⟨h4, hk⟩ := andT hk
  obtain ⟨h5, h6⟩ := andT hk
  have inj : ∀ {u v : S}, cd (S.subtype u) = cd (S.subtype v) → u = v := fun he =>
    S.subtype_injective (cd_inj hn he)
  have beq : ∀ {σ τ : Perm (Fin n)}, Nat.beq (cd σ) (cd τ) = true → cd σ = cd τ :=
    fun he => Nat.eq_of_beq_eq_true he
  refine ⟨inj (by rw [map_pow, map_one]; exact beq h1), inj (by rw [map_pow, map_one]; exact beq h2),
    inj (by rw [map_mul, map_mul]; exact beq h3), ?_,
    inj (by simp only [map_mul, map_pow, map_inv]; exact beq h5),
    inj (by simp only [map_mul, map_pow, map_inv]; exact beq h6)⟩
  rintro ⟨i, j⟩ ⟨i', j'⟩ he
  dsimp only at he
  have key : ∀ i j : Fin 3, (i + 3 * j : ℕ) < 9 ∧
      cd (S.subtype (x ^ (i : ℕ) * y ^ (j : ℕ))) =
        cd (S.subtype x ^ Nat.mod (i + 3 * j : ℕ) 3 * S.subtype y ^ Nat.div (i + 3 * j : ℕ) 3) := by
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    have e1 : Nat.mod (i + 3 * j : ℕ) 3 = i := (by omega : (i + 3 * j : ℕ) % 3 = i)
    have e2 : Nat.div (i + 3 * j : ℕ) 3 = j := (by omega : (i + 3 * j : ℕ) / 3 = j)
    refine ⟨by omega, ?_⟩
    rw [e1, e2, map_mul, map_pow, map_pow]
  obtain ⟨c1, d1⟩ := key i j
  obtain ⟨c2, d2⟩ := key i' j'
  have hd := distinct_spec h4
  have hN : (i + 3 * j : ℕ) = i' + 3 * j' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hd _ c2 _ hlt (by rw [← d1, ← d2, he])
    · exact hd _ c1 _ hlt (by rw [← d1, ← d2, he])
  have hi := i.isLt
  have hj := j.isLt
  have hi' := i'.isLt
  have hj' := j'.isLt
  obtain rfl : i = i' := Fin.ext (by omega)
  obtain rfl : j = j' := Fin.ext (by omega)
  rfl

theorem cub3_sound {n : ℕ} {S : Subgroup (Perm (Fin n))} (A B : S) {ca cb : ℕ}
    (hA : ∀ i : Fin n, ((A : Perm (Fin n)) i : ℕ) = P.img ca i)
    (hB : ∀ i : Fin n, ((B : Perm (Fin n)) i : ℕ) = P.img cb i) {lx ly lh : List Char}
    {a b c d e f μ : ℕ} (hk : cub3OK n ca cb lx ly lh a b c d e f μ = true) :
    let x := mathieuWord A B lx
    let y := mathieuWord A B ly
    let h := mathieuWord A B lh
    x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      (Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
        x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ)) ∧
      h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ c ∧
      h * y * h⁻¹ = x ^ d * y ^ e * ⁅x, y⁆ ^ f ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ μ := by
  dsimp only
  have hn := n_le hA
  have ew : ∀ l, wordC n ca cb l = cd (S.subtype (mathieuWord A B l)) := fun l => by
    rw [wordC_eq hn (a := (A : Perm (Fin n))) (b := (B : Perm (Fin n))) (fun i => (hA i).symm)
      (fun i => (hB i).symm), map_word]
    rfl
  simp only [cub3OK, cub3C, letB_eq, ew] at hk
  generalize mathieuWord A B lx = x at hk ⊢
  generalize mathieuWord A B ly = y at hk ⊢
  generalize mathieuWord A B lh = h at hk ⊢
  have hz : S.subtype x * S.subtype y * (S.subtype x)⁻¹ * (S.subtype y)⁻¹ = S.subtype ⁅x, y⁆ := by
    rw [map_commutatorElement, commutatorElement_def]
  simp only [mul_cd hn, inv_cd hn, pow_cd hn, one_eq, P.conj, P.comm, hz] at hk
  obtain ⟨h1, hk⟩ := andT hk
  obtain ⟨h2, hk⟩ := andT hk
  obtain ⟨h3, hk⟩ := andT hk
  obtain ⟨h4, hk⟩ := andT hk
  obtain ⟨h5, hk⟩ := andT hk
  obtain ⟨h6, hk⟩ := andT hk
  obtain ⟨h7, hk⟩ := andT hk
  obtain ⟨h8, h9⟩ := andT hk
  have inj : ∀ {u v : S}, cd (S.subtype u) = cd (S.subtype v) → u = v := fun he =>
    S.subtype_injective (cd_inj hn he)
  have beq : ∀ {σ τ : Perm (Fin n)}, Nat.beq (cd σ) (cd τ) = true → cd σ = cd τ :=
    fun he => Nat.eq_of_beq_eq_true he
  refine ⟨inj (by rw [map_pow, map_one]; exact beq h1), inj (by rw [map_pow, map_one]; exact beq h2),
    fun he => ne_of_notB h3 (by rw [he, map_one]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ⁅x, y⁆ * x = x * ⁅x, y⁆ := inj (by rw [map_mul, map_mul]; exact beq h4)
    exact e
  · have e : ⁅x, y⁆ * y = y * ⁅x, y⁆ := inj (by rw [map_mul, map_mul]; exact beq h5)
    exact e
  · rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ he
    dsimp only at he
    have key : ∀ i j k : Fin 3, (i + 3 * j + 9 * k : ℕ) < 27 ∧
        cd (S.subtype (x ^ (i : ℕ) * y ^ (j : ℕ) * ⁅x, y⁆ ^ (k : ℕ))) =
          cd (S.subtype x ^ Nat.mod (i + 3 * j + 9 * k : ℕ) 3 *
            S.subtype y ^ Nat.mod (Nat.div (i + 3 * j + 9 * k : ℕ) 3) 3 *
            S.subtype ⁅x, y⁆ ^ Nat.div (i + 3 * j + 9 * k : ℕ) 9) := by
      intro i j k
      have hi := i.isLt
      have hj := j.isLt
      have hk := k.isLt
      have e1 : Nat.mod (i + 3 * j + 9 * k : ℕ) 3 = i :=
        (by omega : (i + 3 * j + 9 * k : ℕ) % 3 = i)
      have e2 : Nat.mod (Nat.div (i + 3 * j + 9 * k : ℕ) 3) 3 = j :=
        (by omega : (i + 3 * j + 9 * k : ℕ) / 3 % 3 = j)
      have e3 : Nat.div (i + 3 * j + 9 * k : ℕ) 9 = k :=
        (by omega : (i + 3 * j + 9 * k : ℕ) / 9 = k)
      refine ⟨by omega, ?_⟩
      rw [e1, e2, e3, map_mul, map_mul, map_pow, map_pow, map_pow]
    obtain ⟨c1, d1⟩ := key i j k
    obtain ⟨c2, d2⟩ := key i' j' k'
    have hd := distinct_spec h6
    have hN : (i + 3 * j + 9 * k : ℕ) = i' + 3 * j' + 9 * k' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact hd _ c2 _ hlt (by rw [← d1, ← d2, he])
      · exact hd _ c1 _ hlt (by rw [← d1, ← d2, he])
    have hi := i.isLt
    have hj := j.isLt
    have hk := k.isLt
    have hi' := i'.isLt
    have hj' := j'.isLt
    have hk' := k'.isLt
    obtain rfl : i = i' := Fin.ext (by omega)
    obtain rfl : j = j' := Fin.ext (by omega)
    obtain rfl : k = k' := Fin.ext (by omega)
    rfl
  · exact inj (by simp only [map_mul, map_pow, map_inv]; exact beq h7)
  · exact inj (by simp only [map_mul, map_pow, map_inv]; exact beq h8)
  · exact inj (by simp only [map_mul, map_pow, map_inv]; exact beq h9)

@[expose] def codeP {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  ((List.finRange n).map fun i => (σ i : ℕ) * 32 ^ (i : ℕ)).sum

theorem genAt_map {n : ℕ} (L : List (Perm (Fin n))) (i : ℕ) :
    genAt n (L.map codeP) i = P.code (L.getD i 1) := by
  induction L generalizing i with
  | nil => exact P.code_one
  | cons g L ih =>
    change Bool.rec (motive := fun _ => ℕ) (genAt n (L.map codeP) (Nat.sub i 1)) (codeP g)
      (Nat.beq i 0) = _
    cases i with
    | zero => rfl
    | succ i =>
      change genAt n (L.map codeP) (Nat.sub (i + 1) 1) = _
      rw [ih]
      rfl

theorem words_sound {n : ℕ} (A B : List (Perm (Fin n))) (W : List (List ℕ)) {LA LB : List ℕ}
    (hA : A.map codeP = LA) (hB : B.map codeP = LB) (hk : wordsOK n LA LB W = true) :
    B = W.map (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW A) := by
  subst hA hB
  have hc : (codeP : Perm (Fin n) → ℕ) = P.code := rfl
  unfold wordsOK at hk
  obtain ⟨hn, hk'⟩ := andT hk
  clear hk
  have hn : n ≤ 32 := Nat.le_of_ble_eq_true hn
  have hgen := genAt_map (n := n)
  have hev : ∀ w : List ℕ, evalWK n (A.map codeP) w =
      P.code (CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW A w) := by
    intro w
    induction w with
    | nil => exact P.code_one
    | cons i w ih =>
      change P.mul n (genAt n (A.map codeP) i) (evalWK n (A.map codeP) w) = _
      rw [hgen, ih, P.code_mul hn]
      rfl
  induction W generalizing B with
  | nil =>
    cases B with
    | nil => rfl
    | cons _ _ => exact absurd hk' (by simp)
  | cons w W ih =>
    cases B with
    | nil => exact absurd hk' (by simp)
    | cons b B =>
      change CFSG.KC.Ord.andB (Nat.beq (codeP b) (evalWK n (A.map codeP) w)) _ = true at hk'
      obtain ⟨h1, h2⟩ := andT hk'
      rw [hev, hc, P.beq_code hn] at h1
      rw [h1, ih B h2, List.map_cons]

end CFSG.KC.LQT.W

end
