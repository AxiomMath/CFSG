module

public import Certificates.Data.Kernel.E27Orth.Orth
public import CFSG.Certificates.Kernel.E27Orth.Sound
public import CFSG.HardMathSupport.Foote.E27.LieTwo.OrthModel

public section

namespace CFSG.KD.E27Orth

open CFSG.KC.Enum CFSG.KC.E27Orth CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec Subgroup Matrix

theorem allBlk_of {b : ℕ} {f : ℕ → Bool} : ∀ {len : ℕ},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (by omega)]
    exact allBlk_of fun l hl => h l (by omega)

theorem rec_sum (f : ℕ → ℕ) : ∀ m, (Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.add acc (f i)) m : ℕ) = ∑ t ∈ Finset.range m, f t
  | 0 => rfl
  | m + 1 => by
    rw [Finset.sum_range_succ, ← rec_sum f m]
    rfl

theorem bit_lt (x k : ℕ) : bit x k < 2 := by
  change (x >>> k) &&& 1 < 2
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem testBit_bit0 (x k : ℕ) : (bit x k).testBit 0 = x.testBit k := by
  change ((x >>> k) &&& 1).testBit 0 = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  simp

theorem testBit_bit (x k j : ℕ) : (bit x k).testBit j = (decide (j = 0) && x.testBit k) := by
  rcases j with _ | j
  · rw [testBit_bit0]
    simp
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (bit_lt x k)
      (by simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.succ_pos j)))]
    simp

theorem eq_iff_bits {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    a = b ↔ ∀ i < n, a.testBit i = b.testBit i := by
  refine ⟨fun h _ _ => h ▸ rfl, fun h => Nat.eq_of_testBit_eq fun i => ?_⟩
  rcases Nat.lt_or_ge i n with hi | hi
  · exact h i hi
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi))]

theorem colF2_eq (n X j : ℕ) : colF2 n X j = ∑ t ∈ Finset.range n, bit X (n * t + j) * 2 ^ t :=
  rec_sum (fun t => bit X (n * t + j) * 2 ^ t) n

theorem colF2_lt (n X j : ℕ) : colF2 n X j < 2 ^ n := by
  have h := blockSum_lt (n := 1) (f := fun t => bit X (n * t + j)) n
    (fun t _ => by simpa using bit_lt X (n * t + j))
  simp only [one_mul] at h
  rw [colF2_eq]
  exact h

theorem testBit_colF2 {n i : ℕ} (X j : ℕ) (hi : i < n) :
    (colF2 n X j).testBit i = X.testBit (n * i + j) := by
  have h := testBit_blockSum (n := 1) (f := fun t => bit X (n * t + j)) n
    (fun t _ => by simpa using bit_lt X (n * t + j)) i 0 Nat.one_pos
  simp only [one_mul, add_zero, testBit_bit0] at h
  rw [colF2_eq, h]
  simp [hi]

theorem trF2_eq (n X : ℕ) : trF2 n X = ∑ t ∈ Finset.range n, colF2 n X t * 2 ^ (n * t) :=
  rec_sum (fun t => colF2 n X t * 2 ^ (n * t)) n

theorem testBit_trF2 {n i j : ℕ} (X : ℕ) (hi : i < n) (hj : j < n) :
    (trF2 n X).testBit (n * i + j) = X.testBit (n * j + i) := by
  rw [trF2_eq, testBit_blockSum n (fun t _ => colF2_lt n X t) i j hj, testBit_colF2 X i hj]
  simp [hi]

theorem pkMat_trF2 (n X : ℕ) : pkMat n (trF2 n X) = (pkMat n X).transpose := by
  ext i j
  simp only [pkMat, Matrix.of_apply, Matrix.transpose_apply, testBit_trF2 X i.isLt j.isLt]

theorem pkMat_xor (n a b : ℕ) : pkMat n (Nat.xor a b) = pkMat n a + pkMat n b := by
  ext i j
  simp only [pkMat, Matrix.of_apply, Matrix.add_apply]
  change (if (a ^^^ b).testBit _ then (1 : ZMod 2) else 0) = _
  rw [Nat.testBit_xor]
  cases a.testBit (n * i.val + j.val) <;> cases b.testBit (n * i.val + j.val) <;> decide

theorem testBit_oneF2 {n i : ℕ} (hi : i < n) : (oneF2 n).testBit (n * i + i) = true := by
  have h := congrFun (congrFun (pkMat_oneF2 n) ⟨i, hi⟩) ⟨i, hi⟩
  simp only [pkMat, Matrix.of_apply, Matrix.one_apply_eq] at h
  by_contra hc
  simp [hc] at h

theorem diag_of_land {n M : ℕ} (h : Nat.land M (oneF2 n) = 0) (i : Fin n) :
    pkMat n M i i = 0 := by
  have h2 := congrArg (fun x => Nat.testBit x (n * i.val + i.val)) h
  change (M &&& oneF2 n).testBit _ = (0 : ℕ).testBit _ at h2
  rw [Nat.testBit_and, testBit_oneF2 i.isLt, Nat.zero_testBit, Bool.and_true] at h2
  simp [pkMat, h2]

@[expose] def qf {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) : ZMod 2 :=
  v ⬝ᵥ (U *ᵥ v)

theorem qf_alt {n : ℕ} {M : Matrix (Fin n) (Fin n) (ZMod 2)} (hd : ∀ i, M i i = 0)
    (hs : M.transpose = M) (v : Fin n → ZMod 2) : qf M v = 0 := by
  unfold qf
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_
    (fun _ _ => Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩) (fun _ _ => rfl)
  · rintro ⟨i, j⟩ _
    have hji : M j i = M i j := congrFun (congrFun hs i) j
    simp only
    rw [hji]
    have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
    convert h2 (v i * (M i j * v j)) using 2
    ring
  · rintro ⟨i, j⟩ _ hne heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact hne (by simp [hd])

theorem qf_mulVec {n : ℕ} (U X : Matrix (Fin n) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    qf U (X *ᵥ v) = qf (X.transpose * U * X) v := by
  unfold qf
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v X.transpose,
    Matrix.vecMul_transpose]

theorem qf_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    qf (A + B) v = qf A v + qf B v := by
  unfold qf
  rw [Matrix.add_mulVec, dotProduct_add]

theorem qOK_spec {n U X : ℕ} (h : qOK n U X = true) (v : Fin n → ZMod 2) :
    qf (pkMat n U) (pkMat n X *ᵥ v) = qf (pkMat n U) v := by
  unfold qOK at h
  rw [sB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hM : pkMat n (Nat.xor (mulF2 n (mulF2 n (trF2 n X) U) X) U) =
      (pkMat n X).transpose * pkMat n U * pkMat n X + pkMat n U := by
    rw [pkMat_xor, pkMat_mulF2, pkMat_mulF2, pkMat_trF2]
  have hd := diag_of_land ((beq_iff _ _).1 h1)
  have hs : (pkMat n (Nat.xor (mulF2 n (mulF2 n (trF2 n X) U) X) U)).transpose =
      pkMat n (Nat.xor (mulF2 n (mulF2 n (trF2 n X) U) X) U) := by
    rw [← pkMat_trF2, (beq_iff _ _).1 h2]
  have h0 := qf_alt hd hs v
  rw [hM, qf_add] at h0
  rw [qf_mulVec]
  have h2' : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact h2' _ _ h0

section Orth

open CFSG.HardMathSupport.Foote.E27 CFSG.Assembly.LowTwoRank

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2) {n : ℕ}
  (e : ι ≃ Fin n)

theorem orth_sound {U X Xi : ℕ} (hQ : ∀ v, Q v = qf (pkMat n U) (v ∘ e.symm))
    (h : orthI n U X Xi = true) : ∃ x : OrthN Q, matO Q e x = pkMat n X := by
  unfold orthI at h
  rw [sB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  refine exists_of_orth Q e (Xi := pkMat n Xi) ?_ ?_ ?_
  · rw [← pkMat_mulF2, (beq_iff _ _).1 h1, pkMat_oneF2]
  · rw [← pkMat_mulF2, (beq_iff _ _).1 h2, pkMat_oneF2]
  · intro v
    rw [hQ, hQ, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id]
    exact qOK_spec h3 _

theorem pow8_eq {M : Type*} [Monoid M] (a : M) : a ^ 8 = a * a * (a * a) * (a * a * (a * a)) := by
  have h8 : (8 : ℕ) = 2 * 2 * 2 := rfl
  rw [h8, pow_mul, pow_mul]
  simp only [sq]

theorem om_sound {U x y yi : ℕ} (hQ : ∀ v, Q v = qf (pkMat n U) (v ∘ e.symm))
    (h : omI n U x y yi = true) :
    ∃ x' : OrthN Q, matO Q e x' = pkMat n x ∧ (x' : GL ι (ZMod 2)) ∈ StatedOmega Q := by
  unfold omI at h
  simp only [sB_eq] at h
  obtain ⟨hx, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hy, hrel⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
  obtain ⟨x', hx'⟩ := orth_sound Q e hQ hx
  obtain ⟨y', hy'⟩ := orth_sound Q e hQ hy
  have h8 : pkMat n (mulF2 n (mulF2 n (mulF2 n x x) (mulF2 n x x))
      (mulF2 n (mulF2 n x x) (mulF2 n x x))) = pkMat n x ^ 8 := by
    simp only [pkMat_mulF2]
    rw [pow8_eq]
  have hinv : pkMat n x * pkMat n x ^ 8 = 1 := by
    unfold orthI at hx
    rw [sB_eq] at hx
    rw [← h8, ← pkMat_mulF2, (beq_iff _ _).1 ((CFSG.KS.bAnd_iff _ _).1 hx).1, pkMat_oneF2]
  have hx9 : x' ^ 9 = 1 := by
    apply matO_injective Q e
    rw [map_pow, map_one, hx', pow_succ']
    exact hinv
  have hyx : y' * x' = x' ^ 8 * y' := by
    apply matO_injective Q e
    rw [map_mul, map_mul, map_pow, hy', hx', ← h8, ← pkMat_mulF2, ← pkMat_mulF2,
      (beq_iff _ _).1 hrel]
  refine ⟨x', hx', ?_⟩
  have hxN : (x' : GL ι (ZMod 2)) ∈ OrthN Q := x'.2
  have hyN : (y' : GL ι (ZMod 2)) ∈ OrthN Q := y'.2
  have hx9' : (x' : GL ι (ZMod 2)) ^ 9 = 1 := by
    have := congrArg Subtype.val hx9
    simpa using this
  have hyx' : (y' : GL ι (ZMod 2)) * (x' : GL ι (ZMod 2)) * (y' : GL ι (ZMod 2))⁻¹ =
      (x' : GL ι (ZMod 2))⁻¹ := by
    have h1 : (y' : GL ι (ZMod 2)) * (x' : GL ι (ZMod 2)) =
        (x' : GL ι (ZMod 2)) ^ 8 * (y' : GL ι (ZMod 2)) := by
      have := congrArg Subtype.val hyx
      simpa using this
    rw [h1]
    have h2 : (x' : GL ι (ZMod 2)) ^ 8 = (x' : GL ι (ZMod 2))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]
      exact hx9'
    rw [h2]
    group
  exact mem_statedOmega_of_inv Q hxN hyN hx9' hyx'

end Orth

@[expose] def vecB {n : ℕ} (k : ℕ) : Fin n → ZMod 2 := fun i => if k.testBit i then 1 else 0

theorem spreadF2_eq (n k : ℕ) : spreadF2 n k = ∑ t ∈ Finset.range n, bit k t * 2 ^ (n * t) :=
  rec_sum (fun t => bit k t * 2 ^ (n * t)) n

theorem pkMat_spread {n : ℕ} (hn : 0 < n) (k : ℕ) :
    pkMat n (spreadF2 n k) = Matrix.of fun i j => if j.val = 0 then (vecB k i : ZMod 2) else 0 := by
  have hf : ∀ t < n, bit k t < 2 ^ n := fun t _ =>
    lt_of_lt_of_le (bit_lt k t) (by simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) hn)
  ext i j
  simp only [pkMat, Matrix.of_apply, vecB]
  rw [spreadF2_eq, testBit_blockSum n hf i j j.isLt, testBit_bit]
  by_cases hj : j.val = 0 <;> simp [hj, i.isLt]

theorem mulVec_entry {n : ℕ} (hn : 0 < n) (X k : ℕ) (i : Fin n) :
    (pkMat n X *ᵥ vecB k) i =
      if (mulF2 n X (spreadF2 n k)).testBit (n * i.val) then 1 else 0 := by
  have h := congrFun (congrFun (pkMat_mulF2 n X (spreadF2 n k)) i) ⟨0, hn⟩
  rw [pkMat_spread hn, Matrix.mul_apply] at h
  simp only [Matrix.of_apply, if_true, mul_zero] at h
  rw [Matrix.mulVec, dotProduct, ← h]
  simp [pkMat]

theorem test_iff {n X k : ℕ} (hn : 0 < n) (hk : k < 2 ^ n) :
    Nat.beq (colF2 n (mulF2 n X (spreadF2 n k)) 0) k = true ↔
      pkMat n X *ᵥ vecB k = vecB k := by
  rw [beq_iff, eq_iff_bits (colF2_lt _ _ _) hk]
  constructor
  · intro h
    funext i
    have h1 := h i.val i.isLt
    rw [testBit_colF2 _ _ i.isLt, add_zero] at h1
    rw [mulVec_entry hn, h1]
    rfl
  · intro h i hi
    have h1 := congrFun h ⟨i, hi⟩
    rw [mulVec_entry hn] at h1
    rw [testBit_colF2 _ _ hi, add_zero]
    simp only [vecB] at h1
    revert h1
    cases (mulF2 n X (spreadF2 n k)).testBit (n * i) <;> cases k.testBit i <;> decide

theorem fixK_eq {n : ℕ} (hn : 0 < n) (X : ℕ) :
    fixK n X = Nat.card {v : Fin n → ZMod 2 // pkMat n X *ᵥ v = v} := by
  have e : fixK n X = ∑ k ∈ Finset.range (2 ^ n),
      nIf(Nat.beq (colF2 n (mulF2 n X (spreadF2 n k)) (nat_lit 0)) k, nat_lit 1, nat_lit 0) :=
    rec_sum (fun k => nIf(Nat.beq (colF2 n (mulF2 n X (spreadF2 n k)) (nat_lit 0)) k,
      nat_lit 1, nat_lit 0)) (2 ^ n)
  have e2 : fixK n X = ((Finset.range (2 ^ n)).filter fun k =>
      pkMat n X *ᵥ vecB k = vecB k).card := by
    rw [e, Finset.card_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    by_cases hp : pkMat n X *ᵥ vecB k = vecB k
    · rw [if_pos hp, (test_iff hn hk').2 hp]
    · have hb : Nat.beq (colF2 n (mulF2 n X (spreadF2 n k)) (nat_lit 0)) k = false := by
        rw [Bool.eq_false_iff]
        exact fun h => hp ((test_iff hn hk').1 h)
      rw [if_neg hp, hb]
  rw [e2, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij (fun k _ => vecB k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.2
  · intro a ha b hb hab
    have ha' := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
    have hb' := Finset.mem_range.1 (Finset.mem_filter.1 hb).1
    refine (eq_iff_bits ha' hb').2 fun i hi => ?_
    have h1 := congrFun hab ⟨i, hi⟩
    simp only [vecB] at h1
    revert h1
    cases a.testBit i <;> cases b.testBit i <;> decide
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    let f : ℕ → ℕ := fun t => if h : t < n then (v ⟨t, h⟩).val else 0
    have hf : ∀ t < n, f t < 2 ^ 1 := by
      intro t ht
      simp only [f, dif_pos ht, pow_one]
      exact ZMod.val_lt _
    have hlt := blockSum_lt n hf
    have hv' : vecB (∑ t ∈ Finset.range n, f t * 2 ^ (1 * t)) = v := by
      funext i
      have h1 := testBit_blockSum n hf i.val 0 Nat.one_pos
      simp only [one_mul, add_zero] at h1
      simp only [vecB, one_mul]
      rw [h1]
      simp only [i.isLt, decide_true, Bool.true_and, f, dif_pos i.isLt]
      generalize v i = a
      revert a
      decide
    refine ⟨_, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by simpa using hlt), ?_⟩, hv'⟩
    rw [hv']
    exact hv

section Tab

variable {H : Type*} [Group H] {n : ℕ} {ρ : H →* Matrix (Fin n) (Fin n) (ZMod 2)}

@[expose] noncomputable def fixG (ρ : H →* Matrix (Fin n) (Fin n) (ZMod 2)) (x : H) : ℕ :=
  Nat.card {v : Fin n → ZMod 2 // ρ x *ᵥ v = v}

theorem eqN {n a b : ℕ} (ha : cnF2 n a = true) (hb : cnF2 n b = true)
    (h : pkMat n a = pkMat n b) : a = b :=
  pkMat_inj ((cnF2_iff _ _).1 ha) ((cnF2_iff _ _).1 hb) h

variable {one N : ℕ} {E : ℕ → ℕ} {T : Subgroup H} {X : ℕ → H}

theorem beq_one_false (hρ : Function.Injective ρ) (hone : pkMat n one = 1) {x : H} {a : ℕ}
    (hx : ρ x = pkMat n a) (h1 : x ≠ 1) : Nat.beq a one = false := by
  rw [Bool.eq_false_iff]
  intro e
  apply h1
  apply hρ
  rw [hx, (beq_iff _ _).1 e, hone, map_one]

theorem cen_sound (hn : 0 < n) (hρ : Function.Injective ρ) (hone : pkMat n one = 1)
    {g : ℕ → H} {m c0 : ℕ} {G : ℕ → ℕ}
    (hX : ∀ i < N, X i ∈ T ∧ ρ (X i) = pkMat n (E i)) (hsurj : ∀ x ∈ T, ∃ i < N, X i = x)
    (hg : ∀ j < m, g j ∈ T ∧ ρ (g j) = pkMat n (G j))
    (hcen : ∀ i < N, cenI n one m c0 G E i = true) :
    ∀ c ∈ T, c ≠ 1 → (∀ s ∈ T, s * c = c * s) → fixG ρ c = c0 := by
  intro c hc h1 hcom
  obtain ⟨i, hi, rfl⟩ := hsurj c hc
  have h := hcen i hi
  unfold cenI at h
  rw [sB_eq] at h
  obtain ⟨hcn, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hcn' := CFSG.KS.allN_spec hcn
  have hcomm : allBlk (nat_lit 0) (fun j => Nat.beq (mulF2 n (G j) (E i))
      (mulF2 n (E i) (G j))) m = true := by
    apply allBlk_of
    intro j hj
    obtain ⟨c1, c2⟩ := (CFSG.KS.bAnd_iff _ _).1 (hcn' j hj)
    have e0 : Nat.add 0 j = j := Nat.zero_add j
    rw [e0]
    apply (beq_iff _ _).2
    apply eqN c1 c2
    rw [pkMat_mulF2, pkMat_mulF2, ← (hg j hj).2, ← (hX i hi).2, ← map_mul, ← map_mul,
      hcom _ (hg j hj).1]
  rw [hcomm] at h2
  dsimp only at h2
  rw [beq_one_false hρ hone (hX i hi).2 h1] at h2
  dsimp only at h2
  unfold fixG
  rw [(hX i hi).2, ← fixK_eq hn]
  exact (beq_iff _ _).1 h2

variable {c0 nF : ℕ} {F Fm : ℕ → ℕ}

theorem fs_mem (hn : 0 < n) (hρ : Function.Injective ρ) (hone : pkMat n one = 1)
    (hcone : cnF2 n one = true)
    (hX : ∀ i < N, X i ∈ T ∧ ρ (X i) = pkMat n (E i)) (hsurj : ∀ x ∈ T, ∃ i < N, X i = x)
    (hfs : ∀ i < N, fsI n one c0 nF E F Fm i = true) :
    ∀ x ∈ T, x ^ 3 = 1 → x ≠ 1 → fixG ρ x = c0 → ∃ s < nF, ∃ i < N, F s = i ∧ X i = x := by
  intro x hx h3 h1 hf
  obtain ⟨i, hi, rfl⟩ := hsurj x hx
  have h := hfs i hi
  unfold fsI at h
  simp only [sB_eq] at h
  cases hf0 : Nat.beq (Fm i) (nat_lit 0)
  · rw [hf0] at h
    dsimp only at h
    obtain ⟨hs, hF⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    exact ⟨_, (blt_iff _ _).1 hs, i, hi, (beq_iff _ _).1 hF, rfl⟩
  · rw [hf0] at h
    dsimp only at h
    exfalso
    rw [beq_one_false hρ hone (hX i hi).2 h1] at h
    dsimp only at h
    cases hy : Nat.beq (mulF2 n (E i) (mulF2 n (E i) (E i))) one
    · rw [hy] at h
      dsimp only at h
      obtain ⟨c2, c3⟩ := (CFSG.KS.bAnd_iff _ _).1 h
      have : Nat.beq (mulF2 n (E i) (mulF2 n (E i) (E i))) one = true := by
        apply (beq_iff _ _).2
        apply eqN c3 hcone
        rw [pkMat_mulF2, pkMat_mulF2, hone, ← (hX i hi).2, ← map_mul, ← map_mul, ← pow_three,
          h3, map_one]
      rw [hy] at this
      exact Bool.false_ne_true this
    · rw [hy] at h
      dsimp only at h
      have : Nat.beq (fixK n (E i)) c0 = true := by
        apply (beq_iff _ _).2
        rw [fixK_eq hn, ← (hX i hi).2]
        exact hf
      rw [this] at h
      exact Bool.false_ne_true h

theorem pkMat_pw3 (hone : pkMat n one = 1) (a i : ℕ) :
    ∃ k : ℕ, pkMat n (pw3 n one a i) = pkMat n a ^ k := by
  rcases i with _ | _ | i
  · exact ⟨0, by rw [pow_zero, ← hone]; rfl⟩
  · exact ⟨1, by rw [pow_one]; rfl⟩
  · refine ⟨2, ?_⟩
    change pkMat n (mulF2 n a a) = _
    rw [pkMat_mulF2, sq]

theorem pair_sound (hn : 0 < n) (hρ : Function.Injective ρ) (hone : pkMat n one = 1)
    (hcone : cnF2 n one = true) (hcnE : ∀ i < N, cnF2 n (E i) = true) {Pw : ℕ → ℕ}
    (hX : ∀ i < N, X i ∈ T ∧ ρ (X i) = pkMat n (E i)) (hsurj : ∀ x ∈ T, ∃ i < N, X i = x)
    (hfs : ∀ i < N, fsI n one c0 nF E F Fm i = true)
    (hpair : ∀ q < nF * nF, pairI n one c0 nF E F Pw q = true) :
    ∀ a ∈ T, ∀ b ∈ T, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∉ zpowers a →
      ∃ i j : ℕ, a ^ i * b ^ j ≠ 1 ∧ fixG ρ (a ^ i * b ^ j) ≠ c0 := by
  intro a ha b hb ha3 hb3 hab ha1 hbz
  have hb1 : b ≠ 1 := fun e => hbz (e ▸ one_mem _)
  by_cases hfa : fixG ρ a = c0
  swap
  · exact ⟨1, 0, by simpa using ha1, by simpa using hfa⟩
  by_cases hfb : fixG ρ b = c0
  swap
  · exact ⟨0, 1, by simpa using hb1, by simpa using hfb⟩
  obtain ⟨s, hs, ia, hia, hFs, rfl⟩ := fs_mem hn hρ hone hcone hX hsurj hfs a ha ha3 ha1 hfa
  obtain ⟨t, ht, ib, hib, hFt, rfl⟩ := fs_mem hn hρ hone hcone hX hsurj hfs b hb hb3 hb1 hfb
  have hF0 : 0 < nF := by omega
  have hq : nF * s + t < nF * nF := by
    have := Nat.mul_le_mul_left nF (by omega : s + 1 ≤ nF)
    rw [Nat.mul_succ] at this
    omega
  have e1 : Nat.div (nF * s + t) nF = s := by
    change (nF * s + t) / nF = s
    rw [Nat.mul_add_div hF0, Nat.div_eq_of_lt ht, Nat.add_zero]
  have e2 : Nat.mod (nF * s + t) nF = t := by
    change (nF * s + t) % nF = t
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
  have h := hpair _ hq
  unfold pairI at h
  rw [e1, e2, hFs, hFt] at h
  simp only [sB_eq] at h
  have hρa := (hX ia hia).2
  have hρb := (hX ib hib).2
  cases hc : Nat.beq (mulF2 n (E ia) (E ib)) (mulF2 n (E ib) (E ia))
  · rw [hc] at h
    dsimp only at h
    obtain ⟨c1, c2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    have : Nat.beq (mulF2 n (E ia) (E ib)) (mulF2 n (E ib) (E ia)) = true := by
      apply (beq_iff _ _).2
      apply eqN c1 c2
      rw [pkMat_mulF2, pkMat_mulF2, ← hρa, ← hρb, ← map_mul, ← map_mul, hab]
    rw [hc] at this
    exact absurd this Bool.false_ne_true
  rw [hc] at h
  dsimp only at h
  rw [beq_one_false hρ hone hρb hb1] at h
  dsimp only at h
  have hba : Nat.beq (E ib) (E ia) = false := by
    rw [Bool.eq_false_iff]
    intro e
    apply hbz
    have : X ib = X ia := hρ (by rw [hρa, hρb, (beq_iff _ _).1 e])
    rw [this]
    exact mem_zpowers _
  rw [hba] at h
  dsimp only at h
  have hba2 : Nat.beq (E ib) (mulF2 n (E ia) (E ia)) = false := by
    rw [Bool.eq_false_iff]
    intro e
    apply hbz
    have : X ib = X ia ^ 2 := hρ (by rw [hρb, (beq_iff _ _).1 e, pkMat_mulF2, map_pow, hρa, sq])
    rw [this]
    exact npow_mem_zpowers _ 2
  rw [hba2] at h
  dsimp only at h
  obtain ⟨hcp, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hp1, hpf⟩ := (CFSG.KS.bAnd_iff _ _).1 h3
  obtain ⟨k1, hk1⟩ := pkMat_pw3 hone (E ia) (Nat.div (Pw (nF * s + t)) (nat_lit 3))
  obtain ⟨k2, hk2⟩ := pkMat_pw3 hone (E ib) (Nat.mod (Pw (nF * s + t)) (nat_lit 3))
  have hρp : ρ (X ia ^ k1 * X ib ^ k2) = pkMat n (mulF2 n
      (pw3 n one (E ia) (Nat.div (Pw (nF * s + t)) (nat_lit 3)))
      (pw3 n one (E ib) (Nat.mod (Pw (nF * s + t)) (nat_lit 3)))) := by
    rw [pkMat_mulF2, hk1, hk2, map_mul, map_pow, map_pow, hρa, hρb]
  refine ⟨k1, k2, fun e => ?_, fun e => ?_⟩
  · have : Nat.beq (mulF2 n (pw3 n one (E ia) (Nat.div (Pw (nF * s + t)) (nat_lit 3)))
        (pw3 n one (E ib) (Nat.mod (Pw (nF * s + t)) (nat_lit 3)))) one = true := by
      apply (beq_iff _ _).2
      apply eqN hcp hcone
      rw [← hρp, e, map_one, hone]
    rw [this] at hp1
    exact absurd hp1 Bool.false_ne_true
  · have : Nat.beq (fixK n (mulF2 n (pw3 n one (E ia) (Nat.div (Pw (nF * s + t)) (nat_lit 3)))
        (pw3 n one (E ib) (Nat.mod (Pw (nF * s + t)) (nat_lit 3))))) c0 = true := by
      apply (beq_iff _ _).2
      rw [fixK_eq hn, ← hρp]
      exact e
    rw [this] at hpf
    exact absurd hpf Bool.false_ne_true

theorem cover_sound (hρ : Function.Injective ρ) (hone : pkMat n one = 1)
    (hcone : cnF2 n one = true) {NB nW : ℕ} {EB Wg Cv : ℕ → ℕ} {B : Subgroup H} {XB : ℕ → H}
    (hX : ∀ i < N, X i ∈ T ∧ ρ (X i) = pkMat n (E i)) (hsurj : ∀ x ∈ T, ∃ i < N, X i = x)
    (hXB : ∀ b < NB, XB b ∈ B ∧ ρ (XB b) = pkMat n (EB b))
    (hW : ∀ w < nW, ∃ x : H, ρ x = pkMat n (Wg w))
    (hcov : ∀ i < N, coverI n one NB nW E EB Wg Cv i = true) :
    ∀ s ∈ T, s ^ 3 = 1 → s ≠ 1 → ∃ x : H, x * s * x⁻¹ ∈ B := by
  intro s hs h3 h1
  obtain ⟨i, hi, rfl⟩ := hsurj s hs
  have h := hcov i hi
  unfold coverI at h
  simp only [sB_eq] at h
  rw [beq_one_false hρ hone (hX i hi).2 h1] at h
  dsimp only at h
  cases hy : Nat.beq (mulF2 n (E i) (mulF2 n (E i) (E i))) one
  · rw [hy] at h
    dsimp only at h
    obtain ⟨c2, c3⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    have : Nat.beq (mulF2 n (E i) (mulF2 n (E i) (E i))) one = true := by
      apply (beq_iff _ _).2
      apply eqN c3 hcone
      rw [pkMat_mulF2, pkMat_mulF2, hone, ← (hX i hi).2, ← map_mul, ← map_mul, ← pow_three,
        h3, map_one]
    rw [hy] at this
    exact absurd this Bool.false_ne_true
  rw [hy] at h
  dsimp only at h
  obtain ⟨hw, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hb, he⟩ := (CFSG.KS.bAnd_iff _ _).1 h4
  obtain ⟨x, hx⟩ := hW _ ((blt_iff _ _).1 hw)
  have hb' := hXB _ ((blt_iff _ _).1 hb)
  refine ⟨x, ?_⟩
  have hc : x * X i = XB (Nat.land (Cv i) (nat_lit 65535)) * x := by
    apply hρ
    rw [map_mul, map_mul, hx, (hX i hi).2, hb'.2, ← pkMat_mulF2, ← pkMat_mulF2, (beq_iff _ _).1 he]
  rw [hc, mul_inv_cancel_right]
  exact hb'.1

theorem comm_sound (hρ : Function.Injective ρ) {m : ℕ} {g : ℕ → H} {G : ℕ → ℕ}
    (hg : ∀ j < m, ρ (g j) = pkMat n (G j)) (h : ∀ q < m * m, commI n m G q = true) :
    ∀ x ∈ gS m g, ∀ y ∈ gS m g, x * y = y * x := by
  have hk : ∀ a ∈ {x | ∃ j < m, g j = x}, ∀ b ∈ {x | ∃ j < m, g j = x}, a * b = b * a := by
    rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
    have hm0 : 0 < m := by omega
    have hq : m * j + k < m * m := by
      have := Nat.mul_le_mul_left m (by omega : j + 1 ≤ m)
      rw [Nat.mul_succ] at this
      omega
    have hc := h _ hq
    unfold commI at hc
    have e1 : Nat.div (m * j + k) m = j := by
      change (m * j + k) / m = j
      rw [Nat.mul_add_div hm0, Nat.div_eq_of_lt hk, Nat.add_zero]
    have e2 : Nat.mod (m * j + k) m = k := by
      change (m * j + k) % m = k
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
    rw [e1, e2] at hc
    simp only [sB_eq] at hc
    apply hρ
    rw [map_mul, map_mul, hg j hj, hg k hk, ← pkMat_mulF2, ← pkMat_mulF2, (beq_iff _ _).1 hc]
  have h1 : gS m g ≤ centralizer {x | ∃ j < m, g j = x} := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro b hb
    exact hk b hb a ha
  have h2 : gS m g ≤ centralizer (gS m g : Set H) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro b hb
    exact ((mem_centralizer_iff.1 (h1 hb)) a ha).symm
  intro x hx y hy
  exact (mem_centralizer_iff.1 (h2 hy)) x hx

end Tab

end CFSG.KD.E27Orth

end
