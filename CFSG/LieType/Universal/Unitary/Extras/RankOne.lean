module

public import CFSG.LieType.Universal.Unitary.Extras.Torus
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.LieType.Universal.Unitary.SUExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

@[expose] def IsBlk (blk : Fin n → ℕ) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ a b, ¬(blk a = blk b ∧ blk a ≠ 0) → M a b = (1 : Matrix (Fin n) (Fin n) F) a b

theorem isBlk_one (blk : Fin n → ℕ) : IsBlk blk (1 : Matrix (Fin n) (Fin n) F) :=
  fun _ _ _ => rfl

theorem IsBlk.mul {blk : Fin n → ℕ} {M N : Matrix (Fin n) (Fin n) F} (hM : IsBlk blk M)
    (hN : IsBlk blk N) : IsBlk blk (M * N) := by
  intro a b hab
  rw [Matrix.mul_apply]
  by_cases ha : blk a = 0
  · rw [Finset.sum_eq_single a]
    · rw [hM a a (by simp [ha]), one_apply_eq, one_mul, hN a b hab]
    · intro c _ hca
      rw [hM a c (by simp [ha]), one_apply_ne (Ne.symm hca), zero_mul]
    · simp
  · have hab' : blk a ≠ blk b := fun h => hab ⟨h, ha⟩
    rw [one_apply_ne (fun h => hab' (by rw [h]))]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : blk c = blk a
    · rw [hN c b (fun h => hab' (hc.symm.trans h.1)),
        one_apply_ne (fun h => hab' (by rw [← hc, h])), mul_zero]
    · rw [hM a c (fun h => hc h.1.symm), one_apply_ne (fun h => hc (by rw [h])), zero_mul]

@[expose] def toBlock (p q : Fin n) (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin 2) (Fin 2) F :=
  !![M p p, M p q; M q p, M q q]

section TwoBlock

variable {blk : Fin n → ℕ} {p q : Fin n}

theorem mul_apply_of_isBlk (hpq : p ≠ q) (hblk : ∀ c, blk c = blk p → c = p ∨ c = q)
    {M N : Matrix (Fin n) (Fin n) F} (hM : IsBlk blk M) {a : Fin n} (ha : blk a = blk p)
    (b : Fin n) : (M * N) a b = M a p * N p b + M a q * N q b := by
  rw [Matrix.mul_apply, Finset.sum_eq_add p q hpq]
  · intro c _ ⟨hcp, hcq⟩
    have hc : blk c ≠ blk p := fun h => by rcases hblk c h with h' | h' <;> contradiction
    rw [hM a c (fun h => hc (h.1.symm.trans ha)),
      one_apply_ne (fun h => hc (by rw [← h]; exact ha)), zero_mul]
  · simp
  · simp

theorem toBlock_mul (hpq : p ≠ q) (hblk : ∀ c, blk c = blk p → c = p ∨ c = q)
    (hqp : blk q = blk p) {M N : Matrix (Fin n) (Fin n) F} (hM : IsBlk blk M) :
    toBlock p q (M * N) = toBlock p q M * toBlock p q N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toBlock, Matrix.mul_apply, Fin.sum_univ_two, mul_apply_of_isBlk hpq hblk hM rfl,
      mul_apply_of_isBlk hpq hblk hM hqp]

theorem toBlock_one (hpq : p ≠ q) : toBlock p q (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toBlock, hpq, hpq.symm]

end TwoBlock

theorem mul_apply_col_of_col {W M : Matrix (Fin n) (Fin n) F} {p q : Fin n}
    (hM : ∀ r, r ≠ q → M r p = 0) (r : Fin n) : (W * M) r p = W r q * M q p := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · intro s _ hs
    rw [hM s hs, mul_zero]
  · simp

theorem mat_inv_col {w : SU σ n} {p q : Fin n} {c : F} (hc : c ≠ 0)
    (hw : ∀ r, mat σ n w r p = if r = q then c else 0) (r : Fin n) :
    mat σ n w⁻¹ r q = if r = p then c⁻¹ else 0 := by
  have h1 : (mat σ n w⁻¹ * mat σ n w) r p = (1 : Matrix (Fin n) (Fin n) F) r p := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [mul_apply_col_of_col (fun s hs => by rw [hw, ite_eq_right hs])] at h1
  rw [hw, ite_eq_left rfl] at h1
  by_cases hr : r = p
  · rw [hr, one_apply_eq] at h1
    rw [hr, ite_eq_left rfl]
    field_simp
    exact h1
  · rw [one_apply_ne hr] at h1
    rw [ite_eq_right hr]
    exact (mul_eq_zero.mp h1).resolve_right hc

@[expose] def FixCol (p : Fin n) (g : SU σ n) : Prop := ∀ r, r ≠ p → mat σ n g r p = 0

theorem fixCol_inv_mul {w g : SU σ n} {p q : Fin n} {c : F} (hc : c ≠ 0)
    (hw : ∀ r, mat σ n w r p = if r = q then c else 0) (hg : ∀ r, r ≠ q → mat σ n g r p = 0) :
    FixCol p (w⁻¹ * g) := by
  intro r hr
  rw [map_mul, mul_apply_col_of_col hg, mat_inv_col hc hw, ite_eq_right hr, zero_mul]

theorem bruhat_of_fixCol {L X H : Subgroup (SU σ n)} {w : SU σ n} {p : Fin n}
    (hXL : X ≤ L) (hw : w ∈ L)
    (hfix : ∀ g ∈ L, FixCol p g → ∃ h ∈ H, ∃ u ∈ X, g = h * u)
    (hmove : ∀ g ∈ L, ¬FixCol p g → ∃ u ∈ X, FixCol p (w⁻¹ * u⁻¹ * g)) (g : SU σ n)
    (hg : g ∈ L) :
    (∃ h ∈ H, ∃ u ∈ X, g = h * u) ∨ ∃ u ∈ X, ∃ h ∈ H, ∃ v ∈ X, g = u * w * h * v := by
  by_cases hc : FixCol p g
  · exact Or.inl (hfix g hg hc)
  · right
    obtain ⟨u, hu, hfu⟩ := hmove g hg hc
    obtain ⟨h, hh, v, hv, hhv⟩ :=
      hfix _ (mul_mem (mul_mem (inv_mem hw) (inv_mem (hXL hu))) hg) hfu
    refine ⟨u, hu, h, hh, v, hv, ?_⟩
    calc g = u * w * (w⁻¹ * u⁻¹ * g) := by group
      _ = u * w * h * v := by rw [hhv]; group

theorem mul_single_mul_apply (U V : Matrix (Fin n) (Fin n) F) (r s : Fin n) (c : F)
    (a b : Fin n) : (U * single r s c * V) a b = U a r * c * V s b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [mul_single_apply_same]
  · intro t _ ht
    rw [mul_single_apply_of_ne (hbj := ht), zero_mul]
  · simp

theorem conj_one_add_apply {U V : Matrix (Fin n) (Fin n) F} (hUV : U * V = 1)
    (N : Matrix (Fin n) (Fin n) F) (a b : Fin n) :
    (U * (1 + N) * V) a b = (1 : Matrix (Fin n) (Fin n) F) a b + (U * N * V) a b := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hUV, Matrix.add_apply]

theorem rankOne_induction (hσ : ∀ c, σ (σ c) = c) {k : Fin (n / 2)} {C : SU σ n → Prop}
    {g : SU σ n} (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k)
    (hpos : ∀ x ∈ rootGroup σ hσ n (Pi.single k 1), C x)
    (hneg : ∀ x ∈ rootGroup σ hσ n (-Pi.single k 1), C x)
    (h1 : C 1) (hmul : ∀ x y, C x → C y → C (x * y)) : C g := by
  rw [CFSG.LieType.CurtisTits.rankOne, sup_eq_iSup] at hg
  refine Subgroup.iSup_induction _ hg (C := C) (fun b x hx => ?_) h1 hmul
  cases b
  · exact hneg x hx
  · exact hpos x hx

theorem isBlk_of_mem_rootGroup (hσ : ∀ c, σ (σ c) = c) {blk : Fin n → ℕ}
    {γ : Fin (n / 2) → ℤ}
    (hblk : ∀ a b, (weight n a - weight n b = toStd n γ ∨
      weight n a - weight n b = 2 • toStd n γ) → blk a = blk b ∧ blk a ≠ 0) {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n γ) : IsBlk blk (mat σ n x) := by
  intro a b hab
  apply mat_apply_of_mem_rootGroup hσ hx
  · exact fun h => hab (hblk a b (Or.inl h))
  · exact fun h => hab (hblk a b (Or.inr h))

theorem weight_ne_weight_sub {a i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i)
    (hj : j ≠ Fin.rev j) (hji : j ≠ Fin.rev i) : weight n a ≠ weight n i - weight n j := by
  intro h
  obtain ⟨ci, hci⟩ := exists_weight_ne_zero hi
  obtain ⟨cj, hcj⟩ := exists_weight_ne_zero hj
  have hc : ci ≠ cj := by
    rintro rfl
    apply hji
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    simp only [Fin.val_rev]
    omega
  have h1 : weight n a ci ≠ 0 := by
    rw [congrFun h ci, Pi.sub_apply, weight_apply', weight_apply']
    have := ci.isLt
    have := cj.isLt
    have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    have hji' : j.val ≠ n - 1 - i.val := fun e => hji (Fin.ext (by simp only [Fin.val_rev]; omega))
    split_ifs <;> omega
  have h2 : weight n a cj ≠ 0 := by
    rw [congrFun h cj, Pi.sub_apply, weight_apply', weight_apply']
    have := ci.isLt
    have := cj.isLt
    have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    have hji' : j.val ≠ n - 1 - i.val := fun e => hji (Fin.ext (by simp only [Fin.val_rev]; omega))
    split_ifs <;> omega
  exact hc (eq_of_weight_ne_zero h1 h2)

theorem weight_ne_zero {i : Fin n} (hi : i ≠ Fin.rev i) : weight n i ≠ 0 := by
  intro h0
  obtain ⟨c, hc⟩ := exists_weight_ne_zero hi
  have h1 := congrFun h0 c
  rw [weight_apply', Pi.zero_apply] at h1
  have := c.isLt
  split_ifs at h1 <;> omega

section Short

variable {hσ : ∀ c, σ (σ c) = c} {k : Fin (n / 2)} (hk : k.val + 1 < n / 2)

@[expose] def blkShort (k : Fin (n / 2)) (hk : k.val + 1 < n / 2) (s : Fin n) : ℕ :=
  if s = lowIdx k ∨ s = lowIdx ⟨k.val + 1, hk⟩ then 1
  else if s = Fin.rev (lowIdx k) ∨ s = Fin.rev (lowIdx ⟨k.val + 1, hk⟩) then 2 else 0

omit [Field F] in
include hk in
theorem short_facts :
    lowIdx (n := n) k ≠ lowIdx ⟨k.val + 1, hk⟩ ∧ lowIdx (n := n) k ≠ Fin.rev (lowIdx k) ∧
      lowIdx (n := n) ⟨k.val + 1, hk⟩ ≠ Fin.rev (lowIdx ⟨k.val + 1, hk⟩) ∧
      lowIdx (n := n) ⟨k.val + 1, hk⟩ ≠ Fin.rev (lowIdx k) :=
  ⟨lowIdx_ne_succ hk, lowIdx_ne_rev k k, lowIdx_ne_rev _ _, lowIdx_ne_rev _ _⟩

omit [Field F] in
theorem blkShort_eq_one_iff (s : Fin n) :
    blkShort k hk s = 1 ↔ s = lowIdx k ∨ s = lowIdx ⟨k.val + 1, hk⟩ := by
  unfold blkShort
  split_ifs with h1 h2 <;> simp_all

omit [Field F] in
theorem blkShort_eq_two_iff (s : Fin n) :
    blkShort k hk s = 2 ↔ s = Fin.rev (lowIdx k) ∨ s = Fin.rev (lowIdx ⟨k.val + 1, hk⟩) := by
  obtain ⟨h1, h2, h3, h4⟩ := short_facts (n := n) hk
  have h5 : lowIdx (n := n) k ≠ Fin.rev (lowIdx ⟨k.val + 1, hk⟩) := lowIdx_ne_rev _ _
  unfold blkShort
  split_ifs with h6 h7
  · rcases h6 with rfl | rfl
    · simp [h2, h5]
    · simp [h3, h4]
  · simp [h7]
  · simp only [false_iff]
    exact h7

omit [Field F] in
theorem blkShort_of_rev_mem {s : Fin n} (hs : blkShort k hk s = 1) :
    blkShort k hk (Fin.rev s) = 2 := by
  rw [blkShort_eq_one_iff] at hs
  rw [blkShort_eq_two_iff]
  rcases hs with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Field F] in
theorem blkShort_lowIdx : blkShort k hk (lowIdx k) = 1 := by
  rw [blkShort_eq_one_iff]
  exact Or.inl rfl

omit [Field F] in
theorem blkShort_succ : blkShort k hk (lowIdx ⟨k.val + 1, hk⟩) = 1 := by
  rw [blkShort_eq_one_iff]
  exact Or.inr rfl

omit [Field F] in
theorem blkShort_rev {s : Fin n} (hs : blkShort k hk s = 1) : blkShort k hk (Fin.rev s) = 2 :=
  blkShort_of_rev_mem hk hs

theorem toStd_short : toStd n (Pi.single k 1) =
    weight n (lowIdx k) - weight n (lowIdx (n := n) ⟨k.val + 1, hk⟩) :=
  (toStd_single_eq_weight_sub hk).symm

theorem toStd_short_neg : toStd n (-Pi.single k 1) =
    weight n (lowIdx (n := n) ⟨k.val + 1, hk⟩) - weight n (lowIdx k) := by
  rw [toStd_neg, toStd_short hk, neg_sub]

theorem blkShort_of_weight {γ : Fin (n / 2) → ℤ}
    (hγ : toStd n γ = weight n (lowIdx k) - weight n (lowIdx (n := n) ⟨k.val + 1, hk⟩) ∨
      toStd n γ = weight n (lowIdx (n := n) ⟨k.val + 1, hk⟩) - weight n (lowIdx k))
    (a b : Fin n) (hab : weight n a - weight n b = toStd n γ ∨
      weight n a - weight n b = 2 • toStd n γ) :
    blkShort k hk a = blkShort k hk b ∧ blkShort k hk a ≠ 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := short_facts (n := n) hk
  have h1' := h1.symm
  rcases hab with hab | hab
  · rcases hγ with hγ | hγ <;> rw [hγ] at hab
    · rcases eq_of_weight_sub_eq_sub h1 h2 h3 h4 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [blkShort_lowIdx, blkShort_succ]
        exact ⟨rfl, one_ne_zero⟩
      · rw [blkShort_rev hk (blkShort_lowIdx hk), blkShort_rev hk (blkShort_succ hk)]
        exact ⟨rfl, two_ne_zero⟩
    · have h4' : lowIdx (n := n) k ≠ Fin.rev (lowIdx ⟨k.val + 1, hk⟩) := lowIdx_ne_rev _ _
      rcases eq_of_weight_sub_eq_sub h1' h3 h2 h4' hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [blkShort_lowIdx, blkShort_succ]
        exact ⟨rfl, one_ne_zero⟩
      · rw [blkShort_rev hk (blkShort_lowIdx hk), blkShort_rev hk (blkShort_succ hk)]
        exact ⟨rfl, two_ne_zero⟩
  · exfalso
    have hne : toStd n γ ≠ 0 := by
      rcases hγ with hγ | hγ
      · rw [hγ]
        exact sub_ne_zero.mpr (weight_injective.ne h1)
      · rw [hγ]
        exact sub_ne_zero.mpr (weight_injective.ne h1')
    obtain ⟨-, hwa⟩ := eq_rev_of_weight_sub_eq_two_smul hab hne
    rcases hγ with hγ | hγ <;> rw [hγ] at hwa
    · exact weight_ne_weight_sub h1 h2 h3 h4 hwa
    · exact weight_ne_weight_sub h1' h3 h2 (lowIdx_ne_rev _ _) hwa

theorem blkShort_hblk (c : Fin n) (hc : blkShort k hk c = blkShort k hk (lowIdx k)) :
    c = lowIdx k ∨ c = lowIdx ⟨k.val + 1, hk⟩ := by
  rw [blkShort_lowIdx, blkShort_eq_one_iff] at hc
  exact hc

include hk in
theorem toStd_short_ne_zero : toStd n (Pi.single k 1) ≠ 0 := by
  rw [toStd_short hk]
  exact sub_ne_zero.mpr (weight_injective.ne (lowIdx_ne_succ hk))

include hk in
theorem toStd_short_neg_ne_zero : toStd n (-Pi.single k 1) ≠ 0 := by
  rw [toStd_neg]
  exact neg_ne_zero.mpr (toStd_short_ne_zero hk)

theorem toBlock_of_mem_pos {x : SU σ n} (hx : x ∈ rootGroup σ hσ n (Pi.single k 1)) :
    toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n x) =
      !![1, mat σ n x (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩); 0, 1] := by
  have he := toStd_short_ne_zero hk
  have hqp : mat σ n x (lowIdx ⟨k.val + 1, hk⟩) (lowIdx k) = 0 :=
    mat_apply_of_weight_sub_eq_neg hσ he hx (by rw [toStd_short hk, neg_sub])
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toBlock, mat_apply_self_of_mem_rootGroup hσ he hx, hqp]

theorem toBlock_of_mem_neg {y : SU σ n} (hy : y ∈ rootGroup σ hσ n (-Pi.single k 1)) :
    toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n y) =
      !![1, 0; mat σ n y (lowIdx ⟨k.val + 1, hk⟩) (lowIdx k), 1] := by
  have he := toStd_short_neg_ne_zero hk
  have hpq : mat σ n y (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) = 0 :=
    mat_apply_of_weight_sub_eq_neg hσ he hy (by rw [toStd_short_neg hk, neg_sub])
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toBlock, mat_apply_self_of_mem_rootGroup hσ he hy, hpq]

theorem blkShort_succ_eq : blkShort k hk (lowIdx ⟨k.val + 1, hk⟩) = blkShort k hk (lowIdx k) := by
  rw [blkShort_succ, blkShort_lowIdx]

theorem isBlk_short_of_mem {g : SU σ n}
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) :
    IsBlk (blkShort k hk) (mat σ n g) ∧
      (toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n g)).det = 1 := by
  refine rankOne_induction hσ hg (C := fun g => IsBlk (blkShort k hk) (mat σ n g) ∧
    (toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n g)).det = 1) ?_ ?_ ?_ ?_
  · intro x hx
    refine ⟨isBlk_of_mem_rootGroup hσ (blkShort_of_weight hk (Or.inl (toStd_short hk))) hx, ?_⟩
    rw [toBlock_of_mem_pos hk hx, Matrix.det_fin_two_of]
    ring
  · intro y hy
    refine ⟨isBlk_of_mem_rootGroup hσ (blkShort_of_weight hk (Or.inr (toStd_short_neg hk))) hy,
      ?_⟩
    rw [toBlock_of_mem_neg hk hy, Matrix.det_fin_two_of]
    ring
  · rw [map_one]
    exact ⟨isBlk_one _, by rw [toBlock_one (lowIdx_ne_succ hk), det_one]⟩
  · intro x y hx hy
    rw [map_mul]
    exact ⟨hx.1.mul hy.1, by
      rw [toBlock_mul (lowIdx_ne_succ hk) (blkShort_hblk hk) (blkShort_succ_eq hk) hx.1, det_mul,
        hx.2, hy.2, one_mul]⟩

theorem eq_one_of_toBlock_short {Q : SU σ n}
    (hQ : Q ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k)
    (hb : toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n Q) = 1) : Q = 1 := by
  obtain ⟨hblk, -⟩ := isBlk_short_of_mem hk hQ
  set p : Fin n := lowIdx k with hp
  set q : Fin n := lowIdx ⟨k.val + 1, hk⟩ with hq
  have hpq : p ≠ q := lowIdx_ne_succ hk
  have hpp : mat σ n Q p p = 1 := by simpa [toBlock] using congrFun (congrFun hb 0) 0
  have hpq' : mat σ n Q p q = 0 := by simpa [toBlock] using congrFun (congrFun hb 0) 1
  have hqp' : mat σ n Q q p = 0 := by simpa [toBlock] using congrFun (congrFun hb 1) 0
  have hqq : mat σ n Q q q = 1 := by simpa [toBlock] using congrFun (congrFun hb 1) 1
  have hblock : ∀ a b, (a = p ∨ a = q) → (b = p ∨ b = q) →
      mat σ n Q a b = (1 : Matrix (Fin n) (Fin n) F) a b := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · rw [hpp, one_apply_eq]
    · rw [hpq', one_apply_ne hpq]
    · rw [hqp', one_apply_ne hpq.symm]
    · rw [hqq, one_apply_eq]
  have hcol : ∀ s, (s = p ∨ s = q) → ∀ a, mat σ n Q a s = (1 : Matrix (Fin n) (Fin n) F) a s := by
    intro s hs a
    by_cases ha : a = p ∨ a = q
    · exact hblock a s ha hs
    · apply hblk a s
      rintro ⟨h1, -⟩
      rw [(blkShort_eq_one_iff hk s).mpr hs, blkShort_eq_one_iff] at h1
      exact ha h1
  apply mat_injective
  rw [map_one]
  ext a b
  by_cases hab : blkShort k hk a = blkShort k hk b ∧ blkShort k hk a ≠ 0
  · obtain ⟨h1, h2⟩ := hab
    by_cases ha1 : blkShort k hk a = 1
    · exact hblock a b ((blkShort_eq_one_iff hk a).mp ha1)
        ((blkShort_eq_one_iff hk b).mp (h1 ▸ ha1))
    · have ha2 : blkShort k hk a = 2 := by
        unfold blkShort at ha1 h2 ⊢
        split_ifs at ha1 h2 ⊢ <;> simp_all
      rcases (blkShort_eq_two_iff hk a).mp ha2 with rfl | rfl
      · exact mat_rev_apply_of_col (hcol p (Or.inl rfl)) b
      · exact mat_rev_apply_of_col (hcol q (Or.inr rfl)) b
  · exact hblk a b hab

theorem eq_of_toBlock_short {g g' : SU σ n}
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k)
    (hg' : g' ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k)
    (h : toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n g) =
      toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n g')) : g = g' := by
  have hgi := inv_mem hg
  have hQ := eq_one_of_toBlock_short hk (mul_mem hgi hg') (by
    rw [map_mul, toBlock_mul (lowIdx_ne_succ hk) (blkShort_hblk hk) (blkShort_succ_eq hk)
      (isBlk_short_of_mem hk hgi).1, ← h,
      ← toBlock_mul (lowIdx_ne_succ hk) (blkShort_hblk hk) (blkShort_succ_eq hk)
      (isBlk_short_of_mem hk hgi).1, ← map_mul, inv_mul_cancel, map_one,
      toBlock_one (lowIdx_ne_succ hk)])
  exact inv_mul_eq_one.mp hQ

theorem rootMatrix_apply_pq {p q : Fin n} (hpq : p ≠ q) (hqp : q ≠ Fin.rev p) (c : F) :
    rootMatrix σ p q c p q = c := by
  have h : ¬(Fin.rev q = p ∧ Fin.rev p = q) := fun h => hqp h.2.symm
  simp [rootMatrix, one_apply_ne hpq, h]

theorem levelWeyl_col_short {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (r : Fin n) :
    mat σ n (levelWeyl hσ ζ k) r (lowIdx k) =
      if r = lowIdx ⟨k.val + 1, hk⟩ then -1 else 0 := by
  rw [mat_apply, coe_levelWeyl hσ hζ, SpecialLinear.signedPerm_apply]
  have hπ : levelPerm k (lowIdx k) = lowIdx (n := n) ⟨k.val + 1, hk⟩ := by
    rw [levelPerm, dite_eq_left hk, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _), Equiv.swap_apply_left]
  have hs : levelSign σ (ζ : F) k (lowIdx k) = -1 := by
    rw [levelSign, dite_eq_left hk, shortSign, ite_eq_left rfl, inv_one]
  rw [hπ, hs]

include hk in
theorem rankOne_bruhat_short {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    (hnorm : ∀ x, σ x = x → ∃ a, σ a * a = x) (g : SU σ n)
    (hg : g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) :
    (∃ h ∈ levelTorus σ k, ∃ u ∈ rootGroup σ hσ n (Pi.single k 1), g = h * u) ∨
      ∃ u ∈ rootGroup σ hσ n (Pi.single k 1), ∃ h ∈ levelTorus σ k,
        ∃ v ∈ rootGroup σ hσ n (Pi.single k 1), g = u * levelWeyl hσ ζ k * h * v := by
  have hpq := lowIdx_ne_succ (n := n) hk
  refine bruhat_of_fixCol (p := lowIdx k) le_sup_left (levelWeyl_mem_rankOne hσ ζ k) ?_ ?_ g hg
  ·
    intro g hg hfc
    have hrow := sum_mat_mul_mat g (lowIdx k) (Fin.rev (lowIdx k))
    rw [Finset.sum_eq_single (lowIdx k) (fun s _ hs => by rw [hfc s hs, map_zero, zero_mul])
      (by simp), ite_eq_left rfl] at hrow
    obtain ⟨t, ht⟩ : ∃ t, mat σ n g (lowIdx k) (lowIdx k) = t := ⟨_, rfl⟩
    rw [ht] at hrow
    have ht0 : t ≠ 0 := fun h => by
      rw [h, map_zero, zero_mul] at hrow
      exact zero_ne_one hrow
    have hh := shortTorus_mem_levelTorus hσ hk (Units.mk0 t ht0)
    rw [Units.val_mk0] at hh
    have hhL := levelTorus_le_rankOne hσ hζ hnorm k hh
    have hmat : mat σ n (shortTorus σ hσ hpq (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) t) =
        diagonal (shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) t) :=
      coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) ht0
    have hd0 := tFun_ne_zero (σ := σ) k ht0
    unfold tFun at hd0
    rw [dite_eq_left hk] at hd0
    have hinv := diagonal_inv_eq hd0 hmat
    set h := shortTorus σ hσ hpq (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) t with hhdef
    have huL : h⁻¹ * g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k :=
      mul_mem (inv_mem hhL) hg
    have hucol : ∀ a, mat σ n (h⁻¹ * g) a (lowIdx k) =
        (1 : Matrix (Fin n) (Fin n) F) a (lowIdx k) := by
      intro a
      rw [map_mul, hinv, diagonal_mul]
      by_cases ha : a = lowIdx k
      · rw [ha, shortTorusFun_left, one_apply_eq, ht, inv_mul_cancel₀ ht0]
      · rw [hfc a ha, mul_zero, one_apply_ne ha]
    obtain ⟨-, hdet⟩ := isBlk_short_of_mem hk huL
    have hqq : mat σ n (h⁻¹ * g) (lowIdx ⟨k.val + 1, hk⟩) (lowIdx ⟨k.val + 1, hk⟩) = 1 := by
      rw [toBlock, Matrix.det_fin_two_of, hucol, hucol, one_apply_eq, one_apply_ne hpq.symm]
        at hdet
      linear_combination hdet
    obtain ⟨β, hβ⟩ : ∃ β, mat σ n (h⁻¹ * g) (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) = β := ⟨_, rfl⟩
    have hx := rootHom_mem hσ hpq (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _)
      (toStd_short hk).symm (Multiplicative.ofAdd β)
    have hux : h⁻¹ * g = rootHom σ hσ hpq (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _)
        (Multiplicative.ofAdd β) := by
      refine eq_of_toBlock_short hk huL (le_sup_left (a := rootGroup σ hσ n (Pi.single k 1)) hx) ?_
      rw [toBlock_of_mem_pos hk hx, mat_apply (rootHom _ _ _ _ _ _), coe_rootHom, toAdd_ofAdd,
        rootMatrix_apply_pq hpq (lowIdx_ne_rev _ _)]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [toBlock, hucol, hqq, hβ, one_apply_ne hpq.symm]
    exact ⟨h, hh, _, hx, by rw [← hux, mul_inv_cancel_left]⟩
  ·
    intro g hg hnfc
    obtain ⟨hblk, -⟩ := isBlk_short_of_mem hk hg
    have hsupp : ∀ r, r ≠ lowIdx k → r ≠ lowIdx ⟨k.val + 1, hk⟩ →
        mat σ n g r (lowIdx k) = 0 := by
      intro r h1 h2
      rw [hblk r (lowIdx k) (fun h => ?_), one_apply_ne h1]
      rw [blkShort_lowIdx] at h
      exact ((blkShort_eq_one_iff hk r).mp h.1).elim h1 h2
    have hqp : mat σ n g (lowIdx ⟨k.val + 1, hk⟩) (lowIdx k) ≠ 0 := by
      intro h0
      apply hnfc
      intro r hr
      by_cases hrq : r = lowIdx ⟨k.val + 1, hk⟩
      · rw [hrq, h0]
      · exact hsupp r hr hrq
    obtain ⟨c, hc⟩ : ∃ c, c * mat σ n g (lowIdx ⟨k.val + 1, hk⟩) (lowIdx k) =
        -mat σ n g (lowIdx k) (lowIdx k) := ⟨_, div_mul_cancel₀ _ hqp⟩
    have hx := rootHom_mem hσ hpq (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _)
      (toStd_short hk).symm (Multiplicative.ofAdd c)
    refine ⟨_, inv_mem hx, ?_⟩
    rw [inv_inv, mul_assoc]
    refine fixCol_inv_mul (neg_ne_zero.mpr one_ne_zero) (levelWeyl_col_short hk hζ)
      fun r hr => ?_
    rw [map_mul, mat_apply (rootHom _ _ _ _ _ _), coe_rootHom, toAdd_ofAdd, rootMatrix,
      Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.add_apply]
    by_cases hrp : r = lowIdx k
    · rw [hrp, single_mul_apply_same,
        single_mul_apply_of_ne (h := lowIdx_ne_rev (n := n) k ⟨k.val + 1, hk⟩), hc]
      ring
    · rw [single_mul_apply_of_ne (h := hrp)]
      by_cases hrq' : r = Fin.rev (lowIdx ⟨k.val + 1, hk⟩)
      · rw [hrq', single_mul_apply_same,
          hsupp (Fin.rev (lowIdx k)) (lowIdx_ne_rev k k).symm (lowIdx_ne_rev _ _).symm,
          hsupp _ (lowIdx_ne_rev _ _).symm (lowIdx_ne_rev _ _).symm]
        ring
      · rw [single_mul_apply_of_ne (h := hrq'), hsupp r hrp hr]
        ring

include hk in
theorem eq_one_of_mem_normalizer_short (u : SU σ n) (hu : u ∈ rootGroup σ hσ n (Pi.single k 1))
    (hn : u ∈ Subgroup.normalizer (rootGroup σ hσ n (-Pi.single k 1) : Set (SU σ n))) :
    u = 1 := by
  have hpq := lowIdx_ne_succ (n := n) hk
  have hy := rootHom_mem hσ hpq.symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _)
    (toStd_short_neg hk).symm (Multiplicative.ofAdd (1 : F))
  have hz := (Subgroup.mem_normalizer_iff.mp hn _).mp hy
  have hzpp := mat_apply_self_of_mem_rootGroup hσ (toStd_short_neg_ne_zero hk) hz (lowIdx k)
  have hUV : mat σ n u * mat σ n u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hY : rootMatrix σ (lowIdx ⟨k.val + 1, hk⟩) (lowIdx k) (1 : F) =
      1 + (single (lowIdx ⟨k.val + 1, hk⟩) (lowIdx k) 1 +
        single (Fin.rev (lowIdx k)) (Fin.rev (lowIdx ⟨k.val + 1, hk⟩)) (-1)) := by
    rw [rootMatrix, map_one, ← single_neg]
    abel
  rw [map_mul, map_mul, mat_apply (rootHom _ _ _ _ _ _), coe_rootHom, toAdd_ofAdd, hY,
    conj_one_add_apply hUV, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
    mul_single_mul_apply, mul_single_mul_apply, one_apply_eq] at hzpp
  have he := toStd_short_ne_zero hk
  have hUpp : mat σ n u (lowIdx k) (Fin.rev (lowIdx k)) = 0 := by
    rw [mat_apply_of_mem_rootGroup hσ hu, one_apply_ne (lowIdx_ne_rev k k)]
    · rw [toStd_short hk, weight_rev']
      intro h
      apply lowIdx_ne_rev (n := n) ⟨k.val + 1, hk⟩ k
      apply weight_injective
      rw [weight_rev']
      funext c
      have := congrFun h c
      simp only [Pi.sub_apply, Pi.neg_apply] at this ⊢
      linarith
    · rw [toStd_short hk, weight_rev']
      intro h
      apply weight_ne_zero (lowIdx_ne_rev (n := n) ⟨k.val + 1, hk⟩ ⟨k.val + 1, hk⟩)
      funext c
      have := congrFun h c
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat,
        Pi.zero_apply] at this ⊢
      linarith
  have hVpp := mat_apply_self_of_mem_rootGroup hσ he (inv_mem hu) (lowIdx k)
  rw [hUpp, hVpp] at hzpp
  have hc : mat σ n u (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) = 0 := by linear_combination hzpp
  apply eq_one_of_toBlock_short hk (le_sup_left (a := rootGroup σ hσ n (Pi.single k 1)) hu)
  rw [toBlock_of_mem_pos hk hu, hc]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Short


end CFSG.LieType.Universal.Unitary.SUExtras
