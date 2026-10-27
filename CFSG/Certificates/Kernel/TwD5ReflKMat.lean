module

public import CFSG.Certificates.Kernel.TwD5ReflKDec
public import CFSG.Certificates.Kernel.TwD5ReflKSound
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Coxeter

public section

namespace CFSG.KC.TwD5R

open scoped Matrix
open CFSG.StandardType.FrameRoute.FS81

theorem reflK_canonKey {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    reflK (canonKey a b) = 1 + Matrix.vecMulVec (decV a) (decV b) := by
  unfold reflK
  cases hc : canon a
  · have e : canonKey a b = negV a * 729 + negV b := by
      unfold canonKey
      rw [hc]
      rfl
    have h1 := negV_lt a
    have h2 := negV_lt b
    rw [e, show (negV a * 729 + negV b) / 729 = negV a by omega,
      show (negV a * 729 + negV b) % 729 = negV b by omega, decV_negV, decV_negV,
      vecMulVec_neg_neg]
  · have e : canonKey a b = a * 729 + b := by
      unfold canonKey
      rw [hc]
      rfl
    rw [e, show (a * 729 + b) / 729 = a by omega, show (a * 729 + b) % 729 = b by omega]

theorem canon_negV_false : ∀ x, x < 729 → canon x = true → canon (negV x) = false := by
  decide +kernel

theorem decV_inj {x y : ℕ} (hx : x < 729) (hy : y < 729) (h : decV x = decV y) : x = y := by
  rw [← encV_decV hx, ← encV_decV hy, h]

theorem vecMulVec_mulVec' (a b y : Fin 6 → ZMod 3) :
    Matrix.vecMulVec a b *ᵥ y = (b ⬝ᵥ y) • a := by
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]

theorem zmod3_cases : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = -1 := by decide

theorem reflK_inj {k k' : ℕ} (hk : keyOK k = true) (hk' : keyOK k' = true)
    (h : reflK k = reflK k') : k = k' := by
  obtain ⟨hk1, hc, hd⟩ := keyOK_iff.mp hk
  obtain ⟨hk1', hc', hd'⟩ := keyOK_iff.mp hk'
  have hfv := dot_eq_one.mp hd
  have hM : Matrix.vecMulVec (decV (k / 729)) (decV (k % 729)) =
      Matrix.vecMulVec (decV (k' / 729)) (decV (k' % 729)) := add_left_cancel h
  have hlt : k / 729 < 729 := by omega
  have hlt' : k' / 729 < 729 := by omega
  have e1 : decV (k / 729) = (decV (k' % 729) ⬝ᵥ decV (k / 729)) • decV (k' / 729) := by
    have h2 := congrArg (· *ᵥ decV (k / 729)) hM
    simp only [vecMulVec_mulVec', hfv, one_smul] at h2
    exact h2
  have hv0 : decV (k / 729) ≠ 0 := by
    intro h0
    rw [h0, dotProduct_zero] at hfv
    exact absurd hfv (by decide)
  have hvv : decV (k / 729) = decV (k' / 729) := by
    rcases zmod3_cases (decV (k' % 729) ⬝ᵥ decV (k / 729)) with h0 | h1 | h2
    · rw [h0, zero_smul] at e1
      exact absurd e1 hv0
    · rw [h1, one_smul] at e1
      exact e1
    · exfalso
      rw [h2, neg_one_smul, ← decV_negV] at e1
      have e2 : k / 729 = negV (k' / 729) := decV_inj hlt (negV_lt _) e1
      have e3 := canon_negV_false (k' / 729) hlt' hc'
      rw [← e2, hc] at e3
      exact absurd e3 (by decide)
  have hff : decV (k % 729) = decV (k' % 729) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : decV (k / 729) i ≠ 0 := hi
    funext j
    have h3 := congrFun (congrFun hM i) j
    rw [Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, ← hvv] at h3
    exact mul_left_cancel₀ hi' h3
  have h1 : k / 729 = k' / 729 := decV_inj hlt hlt' hvv
  have h2 : k % 729 = k' % 729 :=
    decV_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hff
  omega

theorem reflK_fix_iff {k : ℕ} (hk : keyOK k = true) (y : Fin 6 → ZMod 3) :
    reflK k *ᵥ y = y ↔ dot (encV y) (k % 729) = 0 := by
  obtain ⟨-, -, hd⟩ := keyOK_iff.mp hk
  have hfv := dot_eq_one.mp hd
  have hv0 : decV (k / 729) ≠ 0 := by
    intro h0
    rw [h0, dotProduct_zero] at hfv
    exact absurd hfv (by decide)
  rw [dot_eq_zero, decV_encV]
  unfold reflK
  rw [Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec']
  constructor
  · intro h
    have h2 : (decV (k % 729) ⬝ᵥ y) • decV (k / 729) = 0 := by
      have h3 := congrArg (fun z => z - y) h
      simpa using h3
    rcases smul_eq_zero.mp h2 with h4 | h4
    · exact h4
    · exact absurd h4 hv0
  · intro h
    rw [h, zero_smul, add_zero]

@[expose] def sgn (b : ℕ) : ZMod 3 := if b = 1 then -1 else 1

theorem tb_lor (x y b : ℕ) : Nat.testBit (Nat.lor x y) b = (Nat.testBit x b || Nat.testBit y b) :=
  Nat.testBit_lor x y b

theorem tb_shl (a b : ℕ) : Nat.testBit (Nat.shiftLeft 1 a) b = decide (a = b) := by
  change Nat.testBit (1 <<< a) b = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem shl_eq (a k : ℕ) : Nat.shiftLeft a k = a * 2 ^ k := Nat.shiftLeft_eq a k

theorem lane_eq (hc j : ℕ) : lane hc j = hc / 2 ^ (3 * j) % 8 := by
  change (hc >>> (3 * j)) &&& (2 ^ 3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem sbit_eq (hc j : ℕ) : sbit hc j = hc / 2 ^ (18 + j) % 2 := by
  change (hc >>> (18 + j)) &&& (2 ^ 1 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_one]

theorem sbit_lt (hc j : ℕ) : sbit hc j < 2 := by
  rw [sbit_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem or63_iff (l0 l1 l2 l3 l4 l5 : ℕ) :
    Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft 1 l0) (Nat.shiftLeft 1 l1))
      (Nat.lor (Nat.shiftLeft 1 l2) (Nat.shiftLeft 1 l3)))
      (Nat.lor (Nat.shiftLeft 1 l4) (Nat.shiftLeft 1 l5)) = 63 ↔
    ∀ b, (l0 = b ∨ l1 = b ∨ l2 = b ∨ l3 = b ∨ l4 = b ∨ l5 = b) ↔ b < 6 := by
  have h63 : ∀ b, Nat.testBit 63 b = decide (b < 6) := fun b => by
    rw [show (63 : ℕ) = 2 ^ 6 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  have hX : ∀ b, Nat.testBit (Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft 1 l0)
      (Nat.shiftLeft 1 l1)) (Nat.lor (Nat.shiftLeft 1 l2) (Nat.shiftLeft 1 l3)))
      (Nat.lor (Nat.shiftLeft 1 l4) (Nat.shiftLeft 1 l5))) b =
      decide (l0 = b ∨ l1 = b ∨ l2 = b ∨ l3 = b ∨ l4 = b ∨ l5 = b) := by
    intro b
    simp only [tb_lor, tb_shl]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    tauto
  constructor
  · intro h b
    have h2 := congrArg (fun x => Nat.testBit x b) h
    rw [hX, h63] at h2
    exact decide_eq_decide.mp h2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro b
    rw [hX, h63]
    exact decide_eq_decide.mpr (h b)

theorem par_iff {hc : ℕ} (h : hc < 16777216) :
    Nat.land (Nat.shiftRight PAR64 (Nat.shiftRight hc 18)) 1 = 0 ↔
      ∏ j : Fin 6, sgn (sbit hc j) = 1 := by
  have hs : ∀ j : ℕ, sbit hc j = Nat.land (Nat.shiftRight (Nat.shiftRight hc 18) j) 1 := by
    intro j
    change (hc >>> (18 + j)) &&& 1 = ((hc >>> 18) >>> j) &&& 1
    rw [Nat.shiftRight_add]
  have hm : Nat.shiftRight hc 18 < 64 := by
    change hc >>> 18 < 64
    rw [Nat.shiftRight_eq_div_pow]
    omega
  simp only [hs, Fin.prod_univ_six]
  generalize Nat.shiftRight hc 18 = m at hm ⊢
  revert m
  decide +kernel

theorem validH_iff {fx : Bool} {hc : ℕ} :
    validH fx hc = true ↔ hc < 16777216 ∧ lane hc 0 = 0 ∧
      (∀ b, (lane hc 0 = b ∨ lane hc 1 = b ∨ lane hc 2 = b ∨ lane hc 3 = b ∨ lane hc 4 = b ∨
        lane hc 5 = b) ↔ b < 6) ∧ (∏ j : Fin 6, sgn (sbit hc j)) = 1 ∧
      (fx = true → sbit hc 0 = 0) := by
  unfold validH
  simp only [andB_eq_true, Nat.blt_eq, Nat.beq_eq, or63_iff, orB_eq_true, notB_eq_true]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, (par_iff h1).mp h4, fun hf => ?_⟩
    rcases h5 with h | h
    · rw [hf] at h
      cases h
    · exact h
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, (par_iff h1).mpr h4, ?_⟩
    cases fx
    · exact Or.inl rfl
    · exact Or.inr (h5 rfl)

theorem sgn_cases (b : ℕ) : sgn b = 1 ∨ sgn b = -1 := by
  unfold sgn
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

@[expose] def HS (fx : Bool) : Set (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
  cond fx (evenFix0 5) (evenAll0 5)

theorem mem_HS {fx : Bool} {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} :
    M ∈ HS fx ↔ ∃ σ : Equiv.Perm (Fin 6), ∃ s : Fin 6 → ZMod 3, IsSign s ∧ σ 0 = 0 ∧
      (∏ i, s i) = 1 ∧ (fx = true → s 0 = 1) ∧ M = spMat σ s := by
  cases fx
  · change M ∈ evenAll0 5 ↔ _
    constructor
    · rintro ⟨σ, s, hs, ⟨h0, hp⟩, rfl⟩
      exact ⟨σ, s, hs, h0, hp, fun h => absurd h (by decide), rfl⟩
    · rintro ⟨σ, s, hs, h0, hp, -, rfl⟩
      exact ⟨σ, s, hs, ⟨h0, hp⟩, rfl⟩
  · change M ∈ evenFix0 5 ↔ _
    constructor
    · rintro ⟨σ, s, hs, ⟨h0, hs0, hp⟩, rfl⟩
      refine ⟨σ, s, hs, h0, ?_, fun _ => hs0, rfl⟩
      rw [Fin.prod_univ_succ, hs0, hp, one_mul]
    · rintro ⟨σ, s, hs, h0, hp, hs0, rfl⟩
      refine ⟨σ, s, hs, ⟨h0, hs0 rfl, ?_⟩, rfl⟩
      rw [Fin.prod_univ_succ, hs0 rfl, one_mul] at hp
      exact hp

theorem sign_mul {a b : ZMod 3} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem sign_sq {a : ZMod 3} (ha : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases ha with rfl | rfl <;> decide

theorem HS_mul {fx : Bool} {A B : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hA : A ∈ HS fx)
    (hB : B ∈ HS fx) : A * B ∈ HS fx := by
  obtain ⟨σ, s, hs, h0, hp, hf, rfl⟩ := mem_HS.mp hA
  obtain ⟨τ, t, ht, h0', hp', hf', rfl⟩ := mem_HS.mp hB
  rw [spMat_mul]
  refine mem_HS.mpr ⟨σ * τ, _, fun j => sign_mul (hs _) (ht j), ?_, ?_, ?_, rfl⟩
  · rw [Equiv.Perm.mul_apply, h0', h0]
  · rw [Finset.prod_mul_distrib, Equiv.prod_comp τ s, hp, hp', one_mul]
  · intro hfx
    rw [h0', hf hfx, hf' hfx, one_mul]

theorem HS_inv {fx : Bool} {A : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hA : A ∈ HS fx) :
    ∃ A' ∈ HS fx, A' * A = 1 ∧ A * A' = 1 := by
  obtain ⟨σ, s, hs, h0, hp, hf, rfl⟩ := mem_HS.mp hA
  have h0' : σ.symm 0 = 0 := by
    rw [Equiv.symm_apply_eq]
    exact h0.symm
  refine ⟨spMat σ.symm (fun j => s (σ.symm j)), mem_HS.mpr ⟨σ.symm, _, fun j => hs _, h0',
    ?_, ?_, rfl⟩, ?_, ?_⟩
  · rw [Equiv.prod_comp σ.symm s, hp]
  · intro hfx
    rw [h0', hf hfx]
  · rw [spMat_mul, ← spMat_one]
    congr 1
    · ext x
      simp [Equiv.Perm.mul_apply]
    · funext j
      rw [Equiv.symm_apply_apply]
      exact sign_sq (hs j)
  · rw [spMat_mul, ← spMat_one]
    congr 1
    · ext x
      simp [Equiv.Perm.mul_apply]
    · funext j
      exact sign_sq (hs _)

theorem vecMul_spMat_mulVec {σ : Equiv.Perm (Fin 6)} {s : Fin 6 → ZMod 3} (hs : IsSign s)
    (f : Fin 6 → ZMod 3) : (spMat σ s *ᵥ f) ᵥ* spMat σ s = f := by
  rw [spMat_mulVec]
  funext j
  simp only [Matrix.vecMul, dotProduct, spMat_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Equiv.symm_apply_apply]
  rw [mul_comm (s j) (f j), mul_assoc, sign_sq (hs j), mul_one]

@[expose] noncomputable def hcMat (hc : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  fun i j => if i.val = lane hc j.val then sgn (sbit hc j.val) else 0

theorem hcMat_spec {fx : Bool} {hc : ℕ} (h : validH fx hc = true) :
    ∃ σ : Equiv.Perm (Fin 6), (∀ j : Fin 6, (σ j).val = lane hc j) ∧ σ 0 = 0 ∧
      hcMat hc = spMat σ (fun j => sgn (sbit hc j)) := by
  obtain ⟨-, h2, h3, -, -⟩ := validH_iff.mp h
  have hlt : ∀ j : Fin 6, lane hc j < 6 := by
    intro j
    apply (h3 (lane hc j)).mp
    fin_cases j <;> simp
  let f : Fin 6 → Fin 6 := fun j => ⟨lane hc j, hlt j⟩
  have hs : Function.Surjective f := by
    intro i
    rcases (h3 i).mpr i.isLt with e | e | e | e | e | e
    · exact ⟨0, Fin.ext e⟩
    · exact ⟨1, Fin.ext e⟩
    · exact ⟨2, Fin.ext e⟩
    · exact ⟨3, Fin.ext e⟩
    · exact ⟨4, Fin.ext e⟩
    · exact ⟨5, Fin.ext e⟩
  have hb : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  refine ⟨Equiv.ofBijective f hb, fun j => rfl, Fin.ext h2, ?_⟩
  ext i j
  change (if i.val = lane hc j.val then _ else _) = (if i = f j then _ else _)
  have e : i = f j ↔ i.val = lane hc j.val := Fin.ext_iff
  by_cases hij : i.val = lane hc j.val
  · rw [if_pos hij, if_pos (e.mpr hij)]
  · rw [if_neg hij, if_neg (fun h => hij (e.mp h))]

theorem hcMat_mem {fx : Bool} {hc : ℕ} (h : validH fx hc = true) : hcMat hc ∈ HS fx := by
  obtain ⟨σ, -, h0, he⟩ := hcMat_spec h
  obtain ⟨-, -, -, hp, hf⟩ := validH_iff.mp h
  refine mem_HS.mpr ⟨σ, _, fun j => sgn_cases _, h0, hp, fun hfx => ?_, he⟩
  change sgn (sbit hc 0) = 1
  rw [hf hfx]
  rfl

theorem dg_sum_fin (c : Fin 6 → ℕ) (hc : ∀ i, c i < 3) (i : Fin 6) :
    dg (∑ k : Fin 6, c k * 3 ^ k.val) i.val = c i := by
  have e : (∑ k : Fin 6, c k * 3 ^ k.val) =
      c 0 + 3 * c 1 + 9 * c 2 + 27 * c 3 + 81 * c 4 + 243 * c 5 := by
    rw [Fin.sum_univ_six]
    change c 0 * 3 ^ 0 + c 1 * 3 ^ 1 + c 2 * 3 ^ 2 + c 3 * 3 ^ 3 + c 4 * 3 ^ 4 + c 5 * 3 ^ 5 = _
    ring
  rw [e, dg_sum (hc 0) (hc 1) (hc 2) (hc 3) (hc 4) (hc 5) i]
  fin_cases i <;> rfl

theorem cast_sgn (a b : ℕ) (hb : b < 2) :
    (((a * (1 + b)) % 3 : ℕ) : ZMod 3) = (a : ZMod 3) * sgn b := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  interval_cases b
  · rw [show sgn 0 = 1 from rfl, ZMod.natCast_mod]
    push_cast
    ring
  · rw [show sgn 1 = -1 from rfl, ZMod.natCast_mod]
    push_cast
    linear_combination (a : ZMod 3) * h3

theorem act_spec {fx : Bool} {hc : ℕ} (h : validH fx hc = true) (x : ℕ) :
    act hc x < 729 ∧ decV (act hc x) = hcMat hc *ᵥ decV x := by
  obtain ⟨σ, hσ, -, he⟩ := hcMat_spec h
  let c : Fin 6 → ℕ := fun j => (dg x j * (1 + sbit hc j)) % 3
  have hc3 : ∀ j, c j < 3 := fun j => Nat.mod_lt _ (by norm_num)
  let T : Fin 6 → ℕ := fun j => (dg x j * (1 + sbit hc j)) % 3 * 3 ^ lane hc j
  have e0 : act hc x = T 0 + T 1 + (T 2 + T 3) + (T 4 + T 5) := rfl
  have e1 : act hc x = ∑ j : Fin 6, c j * 3 ^ (σ j).val := by
    rw [e0, Fin.sum_univ_six]
    simp only [T, c, ← hσ]
    ring
  have e2 : act hc x = ∑ i : Fin 6, c (σ.symm i) * 3 ^ i.val := by
    rw [e1, ← Equiv.sum_comp σ (fun i => c (σ.symm i) * 3 ^ i.val)]
    simp only [Equiv.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · rw [e2, Fin.sum_univ_six]
    have := hc3 (σ.symm 0)
    have := hc3 (σ.symm 1)
    have := hc3 (σ.symm 2)
    have := hc3 (σ.symm 3)
    have := hc3 (σ.symm 4)
    have := hc3 (σ.symm 5)
    change c (σ.symm 0) * 3 ^ 0 + c (σ.symm 1) * 3 ^ 1 + c (σ.symm 2) * 3 ^ 2 +
      c (σ.symm 3) * 3 ^ 3 + c (σ.symm 4) * 3 ^ 4 + c (σ.symm 5) * 3 ^ 5 < 729
    omega
  · rw [he, spMat_mulVec]
    funext i
    unfold decV
    rw [e2, dg_sum_fin (fun i => c (σ.symm i)) (fun i => hc3 _) i]
    change (((dg x (σ.symm i) * (1 + sbit hc (σ.symm i))) % 3 : ℕ) : ZMod 3) = _
    rw [cast_sgn _ _ (sbit_lt _ _), mul_comm]

theorem hcMat_conj {fx : Bool} {hc : ℕ} (h : validH fx hc = true) (k : ℕ) :
    hcMat hc * reflK k = reflK (canonKey (act hc (k / 729)) (act hc (k % 729))) * hcMat hc := by
  obtain ⟨σ, -, -, he⟩ := hcMat_spec h
  obtain ⟨hv, ev⟩ := act_spec h (k / 729)
  obtain ⟨hf, ef⟩ := act_spec h (k % 729)
  rw [reflK_canonKey hv hf, ev, ef]
  unfold reflK
  rw [he, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, vecMul_spMat_mulVec (fun j => sgn_cases _)]

@[expose] def codeN (u b : ℕ → ℕ) : ℕ :=
  u 0 + 8 * u 1 + 64 * u 2 + 512 * u 3 + 4096 * u 4 + 32768 * u 5 +
    262144 * (b 0 + 2 * b 1 + 4 * b 2 + 8 * b 3 + 16 * b 4 + 32 * b 5)

theorem codeN_spec {u b : ℕ → ℕ} (hu : ∀ j, j < 6 → u j < 8) (hb : ∀ j, j < 6 → b j < 2) :
    codeN u b < 16777216 ∧ ∀ j, j < 6 → lane (codeN u b) j = u j ∧ sbit (codeN u b) j = b j := by
  have := hu 0 (by norm_num)
  have := hu 1 (by norm_num)
  have := hu 2 (by norm_num)
  have := hu 3 (by norm_num)
  have := hu 4 (by norm_num)
  have := hu 5 (by norm_num)
  have := hb 0 (by norm_num)
  have := hb 1 (by norm_num)
  have := hb 2 (by norm_num)
  have := hb 3 (by norm_num)
  have := hb 4 (by norm_num)
  have := hb 5 (by norm_num)
  refine ⟨by unfold codeN; omega, fun j hj => ?_⟩
  rw [lane_eq, sbit_eq]
  unfold codeN
  interval_cases j <;> simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reducePow] <;> omega

theorem colsCode_eq (col : ℕ → ℕ) :
    colsCode col = codeN (fun j => uk (col j)) (fun j => us (col j)) := by
  have e : colsCode col = 0 + (Nat.shiftLeft (uk (col 0)) 0 + Nat.shiftLeft (us (col 0)) 18) +
      (Nat.shiftLeft (uk (col 1)) 3 + Nat.shiftLeft (us (col 1)) 19) +
      (Nat.shiftLeft (uk (col 2)) 6 + Nat.shiftLeft (us (col 2)) 20) +
      (Nat.shiftLeft (uk (col 3)) 9 + Nat.shiftLeft (us (col 3)) 21) +
      (Nat.shiftLeft (uk (col 4)) 12 + Nat.shiftLeft (us (col 4)) 22) +
      (Nat.shiftLeft (uk (col 5)) 15 + Nat.shiftLeft (us (col 5)) 23) := rfl
  rw [e]
  simp only [shl_eq, codeN]
  ring

theorem uk_us_lt : ∀ c, c < 729 → uk c < 8 ∧ us c < 2 := by decide +kernel

theorem decV_of_uk : ∀ c, c < 729 → uk c < 6 → ∀ i : Fin 6,
    decV c i = if i.val = uk c then sgn (us c) else 0 := by
  decide +kernel

theorem uk_us_single : ∀ k : Fin 6, ∀ e : ZMod 3, (e = 1 ∨ e = -1) →
    uk (encV (fun i => if i = k then e else 0)) = k.val ∧
      sgn (us (encV (fun i => if i = k then e else 0))) = e := by
  decide +kernel

@[expose] noncomputable def colMat (col : ℕ → ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  fun i j => decV (col j.val) i

theorem inHCols_iff {fx : Bool} {col : ℕ → ℕ} (hc : ∀ j, j < 6 → col j < 729) :
    inHCols fx col = true ↔ colMat col ∈ HS fx := by
  have hub := fun j hj => uk_us_lt (col j) (hc j hj)
  obtain ⟨hN, hl⟩ := codeN_spec (u := fun j => uk (col j)) (b := fun j => us (col j))
    (fun j hj => (hub j hj).1) (fun j hj => (hub j hj).2)
  unfold inHCols
  rw [colsCode_eq]
  constructor
  · intro h
    have hm := hcMat_mem h
    suffices e : hcMat (codeN (fun j => uk (col j)) (fun j => us (col j))) = colMat col by
      rw [← e]
      exact hm
    obtain ⟨-, -, h3, -, -⟩ := validH_iff.mp h
    ext i j
    have hj := hl j.val j.isLt
    have hlt : uk (col j.val) < 6 := by
      rw [← hj.1]
      apply (h3 _).mp
      fin_cases j <;> simp
    unfold hcMat colMat
    rw [hj.1, hj.2, decV_of_uk _ (hc j.val j.isLt) hlt i]
  · intro h
    obtain ⟨σ, s, hs, h0, hp, hf, he⟩ := mem_HS.mp h
    have hcol : ∀ j : Fin 6, uk (col j) = (σ j).val ∧ sgn (us (col j)) = s j := by
      intro j
      have e : decV (col j) = fun i => if i = σ j then s j else 0 := by
        funext i
        have := congrFun (congrFun he i) j
        exact this
      have e2 : col j = encV (fun i => if i = σ j then s j else 0) := by
        rw [← e, encV_decV (hc j j.isLt)]
      rw [e2]
      exact uk_us_single (σ j) (s j) (hs j)
    have hlane : ∀ j : Fin 6, lane (codeN (fun j => uk (col j)) (fun j => us (col j))) j =
        (σ j).val := fun j => ((hl j j.isLt).1).trans (hcol j).1
    have hsb : ∀ j : Fin 6, sgn (sbit (codeN (fun j => uk (col j)) (fun j => us (col j))) j) =
        s j := fun j => by rw [(hl j j.isLt).2]; exact (hcol j).2
    have l0 : lane (codeN (fun j => uk (col j)) (fun j => us (col j))) 0 = (σ 0).val := hlane 0
    have l1 : lane (codeN (fun j => uk (col j)) (fun j => us (col j))) 1 = (σ 1).val := hlane 1
    have l2 : lane (codeN (fun j => uk (col j)) (fun j => us (col j))) 2 = (σ 2).val := hlane 2
    have l3 : lane (codeN (fun j => uk (col j)) (fun j => us (col j))) 3 = (σ 3).val := hlane 3
    have l4 : lane (codeN (fun j => uk (col j)) (fun j => us (col j))) 4 = (σ 4).val := hlane 4
    have l5 : lane (codeN (fun j => uk (col j)) (fun j => us (col j))) 5 = (σ 5).val := hlane 5
    refine validH_iff.mpr ⟨hN, ?_, ?_, ?_, ?_⟩
    · rw [l0, h0]
      rfl
    · intro b
      rw [l0, l1, l2, l3, l4, l5]
      constructor
      · rintro (e | e | e | e | e | e) <;> rw [← e] <;> exact (σ _).isLt
      · intro hb
        obtain ⟨j, hj⟩ := σ.surjective ⟨b, hb⟩
        have hj' : (σ j).val = b := by rw [hj]
        fin_cases j
        · exact Or.inl hj'
        · exact Or.inr (Or.inl hj')
        · exact Or.inr (Or.inr (Or.inl hj'))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hj')))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hj'))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hj'))))
    · rw [Finset.prod_congr rfl (fun j _ => hsb j)]
      exact hp
    · intro hfx
      have h1 := hsb 0
      rw [hf hfx] at h1
      have h2 := sbit_lt (codeN (fun j => uk (col j)) (fun j => us (col j))) 0
      change sgn (sbit (codeN (fun j => uk (col j)) (fun j => us (col j))) 0) = 1 at h1
      interval_cases hsb0 : sbit (codeN (fun j => uk (col j)) (fun j => us (col j))) 0
      · rfl
      · exact absurd h1 (by decide)

theorem decV_pow3 : ∀ j : Fin 6, decV (3 ^ j.val) = Pi.single j 1 := by decide +kernel

theorem mulVec_single_one (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) (j : Fin 6) :
    M *ᵥ Pi.single j 1 = fun i => M i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem reflInH_iff {fx : Bool} {k : ℕ} : reflInH fx k = true ↔ reflK k ∈ HS fx := by
  have e : colMat (fun j => reflV k (3 ^ j)) = reflK k := by
    ext i j
    unfold colMat
    rw [decV_reflV, decV_pow3 j, mulVec_single_one]
  change inHCols fx (fun j => reflV k (3 ^ j)) = true ↔ _
  rw [inHCols_iff (fun j _ => reflV_lt _ _), e]

@[expose] noncomputable def gensOf (fx : Bool) : List ℕ := cond fx gensFix gensAll

@[expose] noncomputable def GS (fx : Bool) : Submonoid (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
  Submonoid.closure {M | ∃ g ∈ gensOf fx, M = hcMat g}

@[expose] def pmat (σ : Equiv.Perm (Fin 6)) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  spMat σ (fun _ => 1)

@[expose] def dmat (d : Fin 6 → ZMod 3) : Matrix (Fin 6) (Fin 6) (ZMod 3) := spMat 1 d

theorem pmat_mul (σ τ : Equiv.Perm (Fin 6)) : pmat σ * pmat τ = pmat (σ * τ) := by
  unfold pmat
  rw [spMat_mul]
  simp only [mul_one]

theorem dmat_mul (a b : Fin 6 → ZMod 3) : dmat a * dmat b = dmat (a * b) := by
  unfold dmat
  rw [spMat_mul, mul_one]
  rfl

theorem dmat_one : dmat 1 = 1 := spMat_one

@[expose] def spHom : Equiv.Perm (Fin 5) →* Matrix (Fin 6) (Fin 6) (ZMod 3) where
  toFun e := pmat (succPerm e)
  map_one' := by
    rw [succPerm_one]
    exact spMat_one
  map_mul' a b := by rw [succPerm_mul, pmat_mul]

theorem adj_gens : ∀ fx : Bool, ∀ i : Fin 4, ∃ g ∈ gensOf fx,
    hcMat g = pmat (Equiv.swap (Fin.succ i.castSucc) (Fin.succ i.succ)) := by
  decide +kernel

theorem pmat_mem {fx : Bool} {σ : Equiv.Perm (Fin 6)} (h0 : σ 0 = 0) : pmat σ ∈ GS fx := by
  obtain ⟨e, rfl⟩ := eq_succPerm_of_apply_zero (k := 5) h0
  have hle : Submonoid.closure (Set.range fun i : Fin 4 => Equiv.swap i.castSucc i.succ) ≤
      Submonoid.comap spHom (GS fx) := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    change pmat (succPerm (Equiv.swap i.castSucc i.succ)) ∈ GS fx
    rw [succPerm_swap_castSucc i]
    obtain ⟨g, hg, he⟩ := adj_gens fx i
    exact Submonoid.subset_closure ⟨g, hg, he.symm⟩
  have he : e ∈ Submonoid.closure (Set.range fun i : Fin 4 => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  exact hle he

@[expose] def fvec (k : Fin 6) : Fin 6 → ZMod 3 := fun i => if i = k ∨ i = 5 then -1 else 1

@[expose] def f01 : Fin 6 → ZMod 3 := fun i => if i = 0 ∨ i = 1 then -1 else 1

@[expose] def eF (a : ZMod 3) (v : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 := if a = -1 then v else 1

theorem sign_decomp : ∀ a0 a1 a2 a3 a4 a5 : ZMod 3, (a0 = 1 ∨ a0 = -1) → (a1 = 1 ∨ a1 = -1) →
    (a2 = 1 ∨ a2 = -1) → (a3 = 1 ∨ a3 = -1) → (a4 = 1 ∨ a4 = -1) → (a5 = 1 ∨ a5 = -1) →
    a0 * a1 * a2 * a3 * a4 * a5 = 1 → ∀ i : Fin 6,
    (![a0, a1, a2, a3, a4, a5] : Fin 6 → ZMod 3) i =
      eF a0 f01 i * eF (a0 * a1) (fvec 1) i * eF a2 (fvec 2) i * eF a3 (fvec 3) i *
        eF a4 (fvec 4) i := by
  decide +kernel

theorem fvec_eq : dmat (fvec 4) = hcMat 153224 * hcMat 12736136 ∧
    dmat (fvec 1) = pmat (Equiv.swap 1 4) * dmat (fvec 4) * pmat (Equiv.swap 1 4) ∧
    dmat (fvec 2) = pmat (Equiv.swap 2 4) * dmat (fvec 4) * pmat (Equiv.swap 2 4) ∧
    dmat (fvec 3) = pmat (Equiv.swap 3 4) * dmat (fvec 4) * pmat (Equiv.swap 3 4) ∧
    dmat f01 = hcMat 968328 := by
  decide +kernel

theorem fvec_mem {fx : Bool} : dmat (fvec 1) ∈ GS fx ∧ dmat (fvec 2) ∈ GS fx ∧
    dmat (fvec 3) ∈ GS fx ∧ dmat (fvec 4) ∈ GS fx := by
  obtain ⟨e4, e1, e2, e3, -⟩ := fvec_eq
  have h4 : dmat (fvec 4) ∈ GS fx := by
    rw [e4]
    refine Submonoid.mul_mem _ (Submonoid.subset_closure ⟨153224, ?_, rfl⟩)
      (Submonoid.subset_closure ⟨12736136, ?_, rfl⟩) <;> cases fx <;> decide
  have hp : ∀ a : Fin 6, a ≠ 0 → pmat (Equiv.swap a 4) ∈ GS fx := fun a ha =>
    pmat_mem (by rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (by decide)])
  refine ⟨?_, ?_, ?_, h4⟩
  · rw [e1]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hp 1 (by decide)) h4) (hp 1 (by decide))
  · rw [e2]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hp 2 (by decide)) h4) (hp 2 (by decide))
  · rw [e3]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hp 3 (by decide)) h4) (hp 3 (by decide))

theorem eF_mem {fx : Bool} {a : ZMod 3} {v : Fin 6 → ZMod 3} (hv : a = -1 → dmat v ∈ GS fx) :
    dmat (eF a v) ∈ GS fx := by
  unfold eF
  split_ifs with h
  · exact hv h
  · rw [dmat_one]
    exact Submonoid.one_mem _

theorem dmat_mem {fx : Bool} {d : Fin 6 → ZMod 3} (hs : IsSign d) (hp : ∏ i, d i = 1)
    (hf : fx = true → d 0 = 1) : dmat d ∈ GS fx := by
  have hd : d = ![d 0, d 1, d 2, d 3, d 4, d 5] := by
    funext i
    fin_cases i <;> rfl
  rw [Fin.prod_univ_six] at hp
  have e : (![d 0, d 1, d 2, d 3, d 4, d 5] : Fin 6 → ZMod 3) =
      eF (d 0) f01 * eF (d 0 * d 1) (fvec 1) * eF (d 2) (fvec 2) * eF (d 3) (fvec 3) *
        eF (d 4) (fvec 4) :=
    funext (sign_decomp _ _ _ _ _ _ (hs 0) (hs 1) (hs 2) (hs 3) (hs 4) (hs 5) hp)
  obtain ⟨m1, m2, m3, m4⟩ := fvec_mem (fx := fx)
  rw [hd, e, ← dmat_mul, ← dmat_mul, ← dmat_mul, ← dmat_mul]
  refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
    (eF_mem fun h => ?_) (eF_mem fun _ => m1)) (eF_mem fun _ => m2)) (eF_mem fun _ => m3))
    (eF_mem fun _ => m4)
  cases fx
  · rw [fvec_eq.2.2.2.2]
    exact Submonoid.subset_closure ⟨968328, by decide, rfl⟩
  · rw [hf rfl] at h
    exact absurd h (by decide)

theorem HS_le_GS {fx : Bool} {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : M ∈ HS fx) :
    M ∈ GS fx := by
  obtain ⟨σ, s, hs, h0, hp, hf, rfl⟩ := mem_HS.mp hM
  have h0' : σ.symm 0 = 0 := by
    rw [Equiv.symm_apply_eq]
    exact h0.symm
  have e : dmat (fun i => s (σ.symm i)) * pmat σ = spMat σ s := by
    unfold dmat pmat
    rw [spMat_mul, one_mul]
    congr 1
    funext j
    rw [Equiv.symm_apply_apply, mul_one]
  rw [← e]
  refine Submonoid.mul_mem _ (dmat_mem (fun i => hs _) ?_ ?_) (pmat_mem h0)
  · rw [Equiv.prod_comp σ.symm s]
    exact hp
  · intro hfx
    change s (σ.symm 0) = 1
    rw [h0', hf hfx]

end CFSG.KC.TwD5R

end
