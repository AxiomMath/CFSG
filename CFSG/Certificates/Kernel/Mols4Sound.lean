module

public import Certificates.Data.Kernel.Mols4
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquaresInputs
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.Mols4

open CFSG.KLie.CT CFSG.ComponentClassification.WittDesign

@[expose] def IsTriple (PL t : Nat) (r : Fin 3 → Equiv.Perm (Fin 4)) : Prop :=
  t < 13824 ∧ ∀ x : Fin 3, ∀ y : Fin 4, ((r x) y).val = img (pc PL (sel t x.val)) y.val

@[expose] def MolsLevel2G (ra rb rc : Fin 3 → Equiv.Perm (Fin 4)) : Prop :=
  ∀ r₂ : Fin 3 → Equiv.Perm (Fin 4), (∀ x : Fin 3, r₂ x 0 = x.succ) → ColumnsInj (latinSq r₂) →
    ∀ r₃ : Fin 3 → Equiv.Perm (Fin 4), ColumnsInj (latinSq r₃) → Orth (latinSq r₂) (latinSq r₃) →
    ∀ r₄ : Fin 3 → Equiv.Perm (Fin 4), ColumnsInj (latinSq r₄) → Orth (latinSq r₂) (latinSq r₄) →
      Orth (latinSq r₃) (latinSq r₄) →
      (r₂ = ra ∧ r₃ = rb ∧ r₄ = rc) ∨ (r₂ = ra ∧ r₃ = rc ∧ r₄ = rb)

end CFSG.KC.Mols4

end

namespace CFSG.KC.Mols4

open CFSG.KLie.CT CFSG.KC.Loop CFSG.ComponentClassification.WittDesign

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem orB_eq_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [orB]

theorem notB_eq_true {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem beq_true_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

theorem nIf_eq (b : Bool) (x y : Nat) :
    Bool.rec (motive := fun _ => Nat) y x b = if b = true then x else y := by
  cases b <;> rfl

theorem allN_eq_true {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

theorem testBit_orN {n : Nat} {f : Nat → Nat} {j : Nat} :
    (orN n fun i => pw2 (f i)).testBit j = true ↔ ∃ i < n, f i = j := by
  induction n with
  | zero =>
    change Nat.testBit 0 j = true ↔ _
    simp
  | succ n ih =>
    change ((pw2 (f n)) ||| orN n fun i => pw2 (f i)).testBit j = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, pw2_eq, Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact Or.inr ⟨i, h, rfl⟩
      · exact Or.inl rfl

theorem orN_eq_mask {n : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < n) :
    (orN n fun i => pw2 (f i)) = 2 ^ n - 1 ↔ ∀ j < n, ∃ i < n, f i = j := by
  constructor
  · intro h j hj
    apply testBit_orN.1
    rw [h, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hj
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hj : j < n
    · rw [decide_eq_true hj]
      exact testBit_orN.2 (h j hj)
    · rw [decide_eq_false hj, Bool.eq_false_iff]
      intro ht
      obtain ⟨i, hi, rfl⟩ := testBit_orN.1 ht
      exact hj (hf i hi)

theorem orN_eq_mask_iff_inj {n : Nat} {f : Nat → Nat} (v : Fin n → Fin n)
    (hv : ∀ i (h : i < n), f i = (v ⟨i, h⟩).val) :
    (orN n fun i => pw2 (f i)) = 2 ^ n - 1 ↔ Function.Injective v := by
  rw [orN_eq_mask (fun i hi => by rw [hv i hi]; exact (v _).isLt), Finite.injective_iff_surjective]
  constructor
  · intro h j
    obtain ⟨i, hi, he⟩ := h j.val j.isLt
    exact ⟨⟨i, hi⟩, Fin.ext ((hv i hi).symm.trans he)⟩
  · intro h j hj
    obtain ⟨i, he⟩ := h ⟨j, hj⟩
    exact ⟨i.val, i.isLt, (hv i.val i.isLt).trans (congrArg Fin.val he)⟩

theorem img_lt (c y : Nat) : img c y < 4 := by
  have h : img c y ≤ maskN 2 := Nat.and_le_right
  have e : maskN 2 = 3 := rfl
  omega

theorem pc_lt (PL i : Nat) : pc PL i < 256 := by
  have h : pc PL i ≤ maskN 8 := Nat.and_le_right
  have e : maskN 8 = 255 := rfl
  omega

theorem testBit_img (c y b : Nat) :
    (img c y).testBit b = (decide (b < 2) && c.testBit (y * 2 + b)) := by
  have e : img c y = (c >>> (y * 2)) &&& (2 ^ 2 - 1) := rfl
  rw [e, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, Bool.and_comm]

theorem code_ext {c c' : Nat} (hc : c < 256) (hc' : c' < 256)
    (h : ∀ y < 4, img c y = img c' y) : c = c' := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 8
  · have h1 := testBit_img c (k / 2) (k % 2)
    have h2 := testBit_img c' (k / 2) (k % 2)
    rw [h (k / 2) (by omega)] at h1
    have hk2 : k / 2 * 2 + k % 2 = k := by omega
    have hb : decide (k % 2 < 2) = true := decide_eq_true (Nat.mod_lt _ (by decide))
    rw [hk2, hb, Bool.true_and] at h1 h2
    rw [← h1, h2]
  · have h256 : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc h256),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc' h256)]

theorem sumN_eq (n : Nat) (g : Nat → Nat) : sumN n g = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => rw [Finset.sum_range_zero]; rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact Nat.add_comm _ _

theorem popc_eq_card (w X : Nat) :
    popc w X = ((Finset.range w).filter fun j => X.testBit j = true).card := by
  rw [Finset.card_filter]
  unfold popc
  rw [sumN_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Nat.land (Nat.shiftRight X j) 1 = (X >>> j) % 2 := Nat.and_one_is_mod _
  have e2 : X.testBit j = decide ((X >>> j) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rw [e2]
  rcases Nat.mod_two_eq_zero_or_one (X >>> j) with h | h
  · rw [h]
    exact e.trans h
  · rw [h]
    exact e.trans h

theorem pc_inj {PL : Nat} (hP : permsOK PL = true) {i j : Nat} (hi : i < 24) (hj : j < 24)
    (h : pc PL i = pc PL j) : i = j := by
  have h2 : popc 256 (orN 24 fun i => pw2 (pc PL i)) = 24 :=
    Nat.eq_of_beq_eq_true (andB_eq_true.1 hP).2
  rw [popc_eq_card] at h2
  have himg : ((Finset.range 256).filter fun j =>
      (orN 24 fun i => pw2 (pc PL i)).testBit j = true) = (Finset.range 24).image (pc PL) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, testBit_orN]
    constructor
    · rintro ⟨_, i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨pc_lt PL i, i, hi, rfl⟩
  rw [himg] at h2
  have hinj := Finset.card_image_iff.1 (h2.trans (Finset.card_range 24).symm)
  exact hinj (Finset.mem_coe.2 (Finset.mem_range.2 hi)) (Finset.mem_coe.2 (Finset.mem_range.2 hj)) h

noncomputable def cf (PL i : Nat) (y : Fin 4) : Fin 4 := ⟨img (pc PL i) y.val, img_lt _ _⟩

theorem cf_inj {PL : Nat} (hP : permsOK PL = true) {i : Nat} (hi : i < 24) :
    Function.Injective (cf PL i) :=
  (orN_eq_mask_iff_inj (f := fun y => img (pc PL i) y) (cf PL i) (fun _ _ => rfl)).1
    (Nat.eq_of_beq_eq_true (allN_eq_true.1 (andB_eq_true.1 hP).1 i hi))

theorem exists_code {PL : Nat} (hP : permsOK PL = true) (σ : Equiv.Perm (Fin 4)) :
    ∃ i < 24, ∀ y : Fin 4, (σ y).val = img (pc PL i) y.val := by
  let Φ : Fin 24 → Equiv.Perm (Fin 4) := fun i =>
    Equiv.ofBijective (cf PL i) (Finite.injective_iff_bijective.1 (cf_inj hP i.isLt))
  have hΦ : Function.Injective Φ := by
    intro i j h
    have h' : ∀ y < 4, img (pc PL i) y = img (pc PL j) y := fun y hy =>
      congrArg (fun e : Equiv.Perm (Fin 4) => (e ⟨y, hy⟩).val) h
    exact Fin.ext (pc_inj hP i.isLt j.isLt (code_ext (pc_lt PL i) (pc_lt PL j) h'))
  have hb : Function.Bijective Φ := (Fintype.bijective_iff_injective_and_card Φ).2
    ⟨hΦ, by rw [Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]; rfl⟩
  obtain ⟨i, rfl⟩ := hb.2 σ
  exact ⟨i.val, i.isLt, fun y => rfl⟩

theorem pow24 (x : Nat) :
    Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun _ ih => Nat.mul (nat_lit 24) ih) x = 24 ^ x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change 24 * Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun _ ih => Nat.mul (nat_lit 24) ih) x = _
    rw [ih, Nat.pow_succ, Nat.mul_comm]

theorem sel_eq (t x : Nat) : sel t x = t / 24 ^ x % 24 := by
  unfold sel
  rw [pow24]
  rfl

theorem sel_digits {i j k : Nat} (hj : j < 24) (hk : k < 24) (hi : i < 24) :
    sel (i + 24 * j + 576 * k) 0 = i ∧ sel (i + 24 * j + 576 * k) 1 = j ∧
      sel (i + 24 * j + 576 * k) 2 = k := by
  have e2 : (24 : Nat) ^ 2 = 576 := rfl
  rw [sel_eq, sel_eq, sel_eq, pow_zero, pow_one, e2, Nat.div_one]
  omega

theorem exists_triple {PL : Nat} (hP : permsOK PL = true) (r : Fin 3 → Equiv.Perm (Fin 4)) :
    ∃ t, IsTriple PL t r := by
  obtain ⟨i, hi, h0⟩ := exists_code hP (r 0)
  obtain ⟨j, hj, h1⟩ := exists_code hP (r 1)
  obtain ⟨k, hk, h2⟩ := exists_code hP (r 2)
  obtain ⟨d0, d1, d2⟩ := sel_digits hj hk hi
  refine ⟨i + 24 * j + 576 * k, by omega, fun x y => ?_⟩
  fin_cases x
  · exact (h0 y).trans (congrArg (fun s => img (pc PL s) y.val) d0.symm)
  · exact (h1 y).trans (congrArg (fun s => img (pc PL s) y.val) d1.symm)
  · exact (h2 y).trans (congrArg (fun s => img (pc PL s) y.val) d2.symm)

theorem triple_eq {PL t u : Nat} {r s : Fin 3 → Equiv.Perm (Fin 4)} (ht : IsTriple PL t r)
    (hs : IsTriple PL u s) (e : t = u) : r = s := by
  subst e
  funext x
  apply Equiv.ext
  intro y
  exact Fin.ext ((ht.2 x y).trans (hs.2 x y).symm)

theorem ent_eq {PL t : Nat} {r : Fin 3 → Equiv.Perm (Fin 4)} (ht : IsTriple PL t r)
    {x y : Nat} (hx : x < 4) (hy : y < 4) : ent PL t x y = (latinSq r ⟨x, hx⟩ ⟨y, hy⟩).val := by
  cases x with
  | zero => rfl
  | succ x =>
    exact (ht.2 ⟨x, by omega⟩ ⟨y, hy⟩).symm

theorem latinT_iff {PL t : Nat} {r : Fin 3 → Equiv.Perm (Fin 4)} (ht : IsTriple PL t r) :
    latinT PL t = true ↔ ColumnsInj (latinSq r) := by
  unfold latinT
  rw [allN_eq_true]
  constructor
  · intro h y x x' hxx'
    exact (orN_eq_mask_iff_inj (f := fun x => ent PL t x y) (fun x => latinSq r x y)
      (fun i hi => ent_eq ht hi y.isLt)).1 (Nat.eq_of_beq_eq_true (h y.val y.isLt)) hxx'
  · intro h y hy
    exact beq_true_of_eq ((orN_eq_mask_iff_inj (f := fun x => ent PL t x y)
      (fun x => latinSq r x ⟨y, hy⟩) (fun i hi => ent_eq ht hi hy)).2
      (fun x x' hxx' => h ⟨y, hy⟩ x x' hxx'))

def pairF (A B : Fin 4 → Fin 4 → Fin 4) (c : Fin 16) : Fin 16 :=
  ⟨4 * (A ⟨c.val / 4, by omega⟩ ⟨c.val % 4, by omega⟩).val +
      (B ⟨c.val / 4, by omega⟩ ⟨c.val % 4, by omega⟩).val, by
    have := (A ⟨c.val / 4, by omega⟩ ⟨c.val % 4, by omega⟩).isLt
    have := (B ⟨c.val / 4, by omega⟩ ⟨c.val % 4, by omega⟩).isLt
    omega⟩

theorem pairF_inj {A B : Fin 4 → Fin 4 → Fin 4} (h : Orth A B) : Function.Injective (pairF A B) := by
  intro c c' hcc
  have e : 4 * (A ⟨c.val / 4, by omega⟩ ⟨c.val % 4, by omega⟩).val +
      (B ⟨c.val / 4, by omega⟩ ⟨c.val % 4, by omega⟩).val =
      4 * (A ⟨c'.val / 4, by omega⟩ ⟨c'.val % 4, by omega⟩).val +
      (B ⟨c'.val / 4, by omega⟩ ⟨c'.val % 4, by omega⟩).val := congrArg Fin.val hcc
  have := (A ⟨c.val / 4, by omega⟩ ⟨c.val % 4, by omega⟩).isLt
  have := (B ⟨c.val / 4, by omega⟩ ⟨c.val % 4, by omega⟩).isLt
  have := (A ⟨c'.val / 4, by omega⟩ ⟨c'.val % 4, by omega⟩).isLt
  have := (B ⟨c'.val / 4, by omega⟩ ⟨c'.val % 4, by omega⟩).isLt
  obtain ⟨hx, hy⟩ := h ⟨c.val / 4, by omega⟩ ⟨c.val % 4, by omega⟩ ⟨c'.val / 4, by omega⟩
    ⟨c'.val % 4, by omega⟩ (Fin.ext (by omega)) (Fin.ext (by omega))
  have hx' : c.val / 4 = c'.val / 4 := congrArg Fin.val hx
  have hy' : c.val % 4 = c'.val % 4 := congrArg Fin.val hy
  exact Fin.ext (by omega)

theorem orthT_of_orth {PL t u : Nat} {r s : Fin 3 → Equiv.Perm (Fin 4)} (ht : IsTriple PL t r)
    (hu : IsTriple PL u s) (h : Orth (latinSq r) (latinSq s)) : orthT PL t u = true := by
  have hv : ∀ c (hc : c < 16), 4 * ent PL t (c / 4) (c % 4) + ent PL u (c / 4) (c % 4) =
      (pairF (latinSq r) (latinSq s) ⟨c, hc⟩).val := by
    intro c hc
    rw [ent_eq ht (x := c / 4) (y := c % 4) (by omega) (by omega),
      ent_eq hu (x := c / 4) (y := c % 4) (by omega) (by omega)]
    rfl
  exact beq_true_of_eq ((orN_eq_mask_iff_inj
    (f := fun c => 4 * ent PL t (c / 4) (c % 4) + ent PL u (c / 4) (c % 4))
    (pairF (latinSq r) (latinSq s)) hv).2 (pairF_inj h))

theorem rec_sum (G : Nat → Nat) (k : Nat) :
    Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 => Nat.add (G l) ih2) k =
      ∑ l ∈ Finset.range k, G l := by
  induction k with
  | zero => rw [Finset.sum_range_zero]; rfl
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact Nat.add_comm _ _

theorem sumBelow_eq (m hi : Nat) (f : Nat → Nat) :
    sumBelow m hi f = ∑ i ∈ Finset.range (64 * hi), if i < m then f i else 0 := by
  induction hi with
  | zero => rw [Nat.mul_zero, Finset.sum_range_zero]; rfl
  | succ h ih =>
    change Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
      Nat.add ((fun i => nIf(Nat.blt i m, f i, 0)) (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 +
        sumBelow m h f = _
    rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
      Nat.add_comm (Finset.sum (Finset.range 64) _)]
    refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
    have e6 : (2 : Nat) ^ 6 = 64 := rfl
    have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
      change h <<< 6 + l = 64 * h + l
      rw [Nat.shiftLeft_eq, e6]
      omega
    simp only [e, nIf_eq, Nat.blt_eq]

theorem mem_list {PL LL : Nat} (hL : listOK PL LL = true) {t : Nat} (ht : t < 13824)
    (hlat : latinT PL t = true) : ∃ a < 24, lt LL a = t := by
  obtain ⟨h1, h'⟩ := andB_eq_true.1 hL
  obtain ⟨h2, h''⟩ := andB_eq_true.1 h'
  obtain ⟨h3, h4⟩ := andB_eq_true.1 h''
  have h1 := allN_eq_true.1 h1
  have h3 : lt LL 23 < 13824 := Nat.le_of_ble_eq_true h3
  have hsucc : ∀ i < 23, lt LL i < lt LL (i + 1) :=
    fun i hi => Nat.le_of_ble_eq_true (allN_eq_true.1 h2 i hi)
  have hmono : ∀ i j, i < j → j < 24 → lt LL i < lt LL j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact (ih h (by omega)).trans (hsucc j (by omega))
      · exact hsucc i (by omega)
  have hbd : ∀ i < 24, lt LL i < 13824 := by
    intro i hi
    rcases Nat.lt_or_ge i 23 with h | h
    · exact (hmono i 23 h (by omega)).trans h3
    · have e : i = 23 := by omega
      subst e
      exact h3
  have h4 := Nat.eq_of_beq_eq_true h4
  rw [sumBelow_eq] at h4
  have hcard : ((Finset.range 13824).filter fun t => latinT PL t = true).card = 24 := by
    rw [Finset.card_filter]
    refine Eq.trans ?_ h4
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [Finset.mem_range.1 hs, ↓reduceIte, nIf_eq]
  have hsub : (Finset.range 24).image (lt LL) ⊆
      (Finset.range 13824).filter fun t => latinT PL t = true := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hs
    have hi := Finset.mem_range.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hbd i hi), h1 i hi⟩
  have himc : ((Finset.range 24).image (lt LL)).card = 24 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hi : i < 24 := by simpa using hi
    have hj : j < 24 := by simpa using hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact (hmono i j h hj).ne hij
    · exact (hmono j i h hi).ne' hij
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, himc])
  have hm : t ∈ (Finset.range 13824).filter fun t => latinT PL t = true :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 ht, hlat⟩
  rw [← heq] at hm
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hm
  exact ⟨a, Finset.mem_range.1 ha, rfl⟩

end CFSG.KC.Mols4

public section

namespace CFSG.KC.Mols4

open CFSG.KLie.CT CFSG.ComponentClassification.WittDesign

theorem sound {PL LL tA tB tC : Nat} {ra rb rc : Fin 3 → Equiv.Perm (Fin 4)}
    (hP : permsOK PL = true) (hL : listOK PL LL = true)
    (hA : IsTriple PL tA ra) (hB : IsTriple PL tB rb) (hC : IsTriple PL tC rc)
    (h : molsK PL LL tA tB tC = true) : MolsLevel2G ra rb rc := by
  intro r₂ h0 hl2 r₃ hl3 ho23 r₄ hl4 ho24 ho34
  obtain ⟨t₂, ht₂⟩ := exists_triple hP r₂
  obtain ⟨t₃, ht₃⟩ := exists_triple hP r₃
  obtain ⟨t₄, ht₄⟩ := exists_triple hP r₄
  obtain ⟨a, ha, rfl⟩ := mem_list hL ht₂.1 ((latinT_iff ht₂).2 hl2)
  obtain ⟨b, hb, rfl⟩ := mem_list hL ht₃.1 ((latinT_iff ht₃).2 hl3)
  obtain ⟨c, hc, rfl⟩ := mem_list hL ht₄.1 ((latinT_iff ht₄).2 hl4)
  have hrow : allN 3 (fun x => Nat.beq (img (pc PL (sel (lt LL a) x)) 0) (Nat.succ x)) = true :=
    allN_eq_true.2 fun x hx => by
      have e := ht₂.2 ⟨x, hx⟩ 0
      rw [h0 ⟨x, hx⟩] at e
      exact beq_true_of_eq e.symm
  have k1 := allN_eq_true.1 h a ha
  beta_reduce at k1
  rcases orB_eq_true.1 k1 with hn | k2
  · exact absurd ((notB_eq_true.1 hn).symm.trans hrow) Bool.false_ne_true
  have k2 := allN_eq_true.1 k2 b hb
  beta_reduce at k2
  rcases orB_eq_true.1 k2 with hn | k3
  · exact absurd ((notB_eq_true.1 hn).symm.trans (orthT_of_orth ht₂ ht₃ ho23)) Bool.false_ne_true
  have k3 := allN_eq_true.1 k3 c hc
  beta_reduce at k3
  rcases orB_eq_true.1 k3 with hn | k4
  · exact absurd ((notB_eq_true.1 hn).symm.trans (andB_eq_true.2
      ⟨orthT_of_orth ht₂ ht₄ ho24, orthT_of_orth ht₃ ht₄ ho34⟩)) Bool.false_ne_true
  obtain ⟨e2, k5⟩ := andB_eq_true.1 k4
  have r2 := triple_eq ht₂ hA (Nat.eq_of_beq_eq_true e2)
  rcases orB_eq_true.1 k5 with k6 | k6
  · obtain ⟨e3, e4⟩ := andB_eq_true.1 k6
    exact Or.inl ⟨r2, triple_eq ht₃ hB (Nat.eq_of_beq_eq_true e3),
      triple_eq ht₄ hC (Nat.eq_of_beq_eq_true e4)⟩
  · obtain ⟨e3, e4⟩ := andB_eq_true.1 k6
    exact Or.inr ⟨r2, triple_eq ht₃ hC (Nat.eq_of_beq_eq_true e3),
      triple_eq ht₄ hB (Nat.eq_of_beq_eq_true e4)⟩

end CFSG.KC.Mols4

end
