module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod

public noncomputable section

namespace CFSG.EvenSporadicStandard.Wong77.Module

abbrev Word : Type := Fin 23 → ZMod 2

@[expose] def wordOfNat (x : ℕ) : Word := fun i => if x.testBit i then 1 else 0

theorem wordOfNat_xor (x y : ℕ) : wordOfNat (x ^^^ y) = wordOfNat x + wordOfNat y := by
  funext i
  simp only [wordOfNat, Nat.testBit_xor, Pi.add_apply]
  cases x.testBit i <;> cases y.testBit i <;> decide

theorem wordOfNat_zero : wordOfNat 0 = 0 := by
  funext i
  simp [wordOfNat]

def popCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x => Nat.land (Nat.shiftRight x n) 1 + popCount n x

theorem popCount_eq (n x : ℕ) :
    popCount n x = ((Finset.range n).filter fun i => x.testBit i).card := by
  induction n with
  | zero => simp [popCount]
  | succ n ih =>
    rw [popCount, ih, Finset.range_add_one, Finset.filter_insert]
    have : Nat.land (Nat.shiftRight x n) 1 = if x.testBit n then 1 else 0 := by
      change (x >>> n) &&& 1 = _
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ n) with h | h <;> simp [h]
    rw [this]
    by_cases h : x.testBit n = true
    · simp [h, Finset.card_insert_of_notMem, add_comm]
    · simp [h]

theorem hammingNorm_wordOfNat (x : ℕ) : hammingNorm (wordOfNat x) = popCount 23 x := by
  rw [popCount_eq, Finset.card_filter, hammingNorm, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if x.testBit i then 1 else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [wordOfNat]

def spanCheck : (n : ℕ) → (Fin n → ℕ) → ℕ → (ℕ → Bool) → Bool
  | 0, _, acc, P => P acc
  | n + 1, r, acc, P =>
      spanCheck n (fun i => r i.succ) acc P &&
        spanCheck n (fun i => r i.succ) (Nat.xor acc (r 0)) P

theorem spanCheck_sound : ∀ (n : ℕ) (r : Fin n → ℕ) (acc : ℕ) (P : ℕ → Bool),
    spanCheck n r acc P = true → ∀ m : Fin n → ZMod 2,
      ∃ x, P x = true ∧ wordOfNat x = wordOfNat acc + ∑ k, m k • wordOfNat (r k) := by
  intro n
  induction n with
  | zero =>
    intro r acc P h m
    exact ⟨acc, h, by simp⟩
  | succ n ih =>
    intro r acc P h m
    rw [spanCheck, Bool.and_eq_true] at h
    obtain ⟨h0, h1⟩ := h
    rw [Fin.sum_univ_succ]
    have hm : m 0 = 0 ∨ m 0 = 1 := by
      generalize m 0 = t
      revert t
      decide
    rcases hm with hm | hm
    · obtain ⟨x, hx, hxe⟩ := ih _ acc P h0 (fun i => m i.succ)
      exact ⟨x, hx, by rw [hxe, hm]; simp⟩
    · obtain ⟨x, hx, hxe⟩ := ih _ (Nat.xor acc (r 0)) P h1 (fun i => m i.succ)
      refine ⟨x, hx, ?_⟩
      rw [hxe, hm]
      change wordOfNat (acc ^^^ r 0) + _ = _
      rw [wordOfNat_xor]
      simp only [one_smul]
      abel

@[expose] def golayMask : Fin 12 → ℕ :=
  ![7684609, 3817986, 3113476, 6062600, 5742608, 2580512, 3252800, 5137024, 4440832, 6988800,
    5859328, 3993600]

@[expose] def golayPivot : Fin 12 → Fin 23 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12]

@[expose] def golayRow (k : Fin 12) : Word := wordOfNat (golayMask k)

@[expose] def golayCode : Submodule (ZMod 2) Word :=
  Submodule.span (ZMod 2) (Set.range golayRow)

theorem golayRow_pivot (j k : Fin 12) : golayRow j (golayPivot k) = if j = k then 1 else 0 := by
  revert j k
  decide

theorem golayRow_linearIndependent : LinearIndependent (ZMod 2) golayRow := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  simpa [Finset.sum_apply, golayRow_pivot] using congrFun hg (golayPivot j)

theorem finrank_golayCode : Module.finrank (ZMod 2) golayCode = 12 := by
  rw [golayCode, finrank_span_eq_card golayRow_linearIndependent]
  simp

theorem natCard_golayCode : Nat.card golayCode = 2 ^ 12 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_golayCode, Nat.card_zmod]

theorem mem_golayCode_iff (v : Word) :
    v ∈ golayCode ↔ ∀ i, v i = ∑ j, v (golayPivot j) * golayRow j i := by
  constructor
  · intro hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k, rfl⟩ i
      simp [golayRow_pivot]
    · intro i
      simp
    · intro x y _ _ hx hy i
      simp [add_mul, Finset.sum_add_distrib, ← hx i, ← hy i]
    · intro a x _ hx i
      simp [mul_assoc, ← Finset.mul_sum, ← hx i]
  · intro h
    have : v = ∑ j, v (golayPivot j) • golayRow j := by
      funext i
      simp [Finset.sum_apply, h i]
    rw [this]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

def weightOK (w : ℕ) : Bool :=
  Nat.beq w 7 || Nat.beq w 8 || Nat.beq w 11 || Nat.beq w 12 || Nat.beq w 15 || Nat.beq w 16 ||
    Nat.beq w 23

private theorem golayWeightCheck :
    spanCheck 12 golayMask 0 (fun x => Nat.beq x 0 || weightOK (popCount 23 x)) = true := by
  decide

theorem golayCode_weight (c : Word) (hc : c ∈ golayCode) (h0 : c ≠ 0) :
    hammingNorm c = 7 ∨ hammingNorm c = 8 ∨ hammingNorm c = 11 ∨ hammingNorm c = 12 ∨
      hammingNorm c = 15 ∨ hammingNorm c = 16 ∨ hammingNorm c = 23 := by
  obtain ⟨m, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hc
  obtain ⟨x, hx, hxe⟩ := spanCheck_sound 12 golayMask 0 _ golayWeightCheck m
  have hc : (∑ k, m k • golayRow k) = wordOfNat x := by
    rw [hxe, wordOfNat_zero, zero_add]
    rfl
  rw [hc] at h0 ⊢
  have hx0 : x ≠ 0 := fun h => h0 (by rw [h, wordOfNat_zero])
  rw [hammingNorm_wordOfNat]
  simp only [Nat.beq_eq, hx0, false_or, weightOK, Bool.or_eq_true] at hx
  omega

theorem le_hammingNorm_of_mem_golayCode (c : Word) (hc : c ∈ golayCode) (h0 : c ≠ 0) :
    7 ≤ hammingNorm c := by
  rcases golayCode_weight c hc h0 with h | h | h | h | h | h | h <;> omega

def coordSum : Word →ₗ[ZMod 2] ZMod 2 := ∑ i, LinearMap.proj i

theorem coordSum_apply (v : Word) : coordSum v = ∑ i, v i := by
  simp [coordSum, LinearMap.sum_apply]

@[expose] def golayEven : Submodule (ZMod 2) Word := golayCode ⊓ LinearMap.ker coordSum

theorem mem_golayEven_iff (v : Word) : v ∈ golayEven ↔ v ∈ golayCode ∧ ∑ i, v i = 0 := by
  simp [golayEven, coordSum_apply]

theorem hammingNorm_cast (v : Word) : (hammingNorm v : ZMod 2) = ∑ i, v i := by
  rw [hammingNorm, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : v i = 0 ∨ v i = 1 := by
    generalize v i = t
    revert t
    decide
  rcases h with h | h <;> simp [h]

theorem mem_golayEven_iff_even (v : Word) :
    v ∈ golayEven ↔ v ∈ golayCode ∧ Even (hammingNorm v) := by
  rw [mem_golayEven_iff, ← hammingNorm_cast, ZMod.natCast_eq_zero_iff_even]

@[expose] def allOnes : Word := fun _ => 1

theorem allOnes_mem_golayCode : allOnes ∈ golayCode :=
  (mem_golayCode_iff _).2 (by decide)

theorem coordSum_allOnes : coordSum allOnes = 1 := by
  rw [coordSum_apply]
  decide

private theorem coordSum_surjective : Function.Surjective coordSum := by
  intro t
  refine ⟨t • Pi.single 0 1, ?_⟩
  simp [coordSum_apply, Finset.sum_pi_single']

private theorem finrank_ker_coordSum : Module.finrank (ZMod 2) (LinearMap.ker coordSum) = 22 := by
  have h := LinearMap.finrank_range_add_finrank_ker coordSum
  rw [LinearMap.range_eq_top.2 coordSum_surjective, finrank_top] at h
  simp at h
  omega

private theorem golayCode_sup_ker : golayCode ⊔ LinearMap.ker coordSum = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have h : v - allOnes ∈ LinearMap.ker coordSum ∨ v ∈ LinearMap.ker coordSum := by
    rw [LinearMap.mem_ker, LinearMap.mem_ker, map_sub, coordSum_allOnes]
    generalize coordSum v = t
    revert t
    decide
  rcases h with h | h
  · have := Submodule.add_mem_sup allOnes_mem_golayCode h
    simpa [add_comm] using this
  · exact Submodule.mem_sup_right h

theorem finrank_golayEven : Module.finrank (ZMod 2) golayEven = 11 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq golayCode (LinearMap.ker coordSum)
  rw [golayCode_sup_ker, finrank_top, finrank_golayCode, finrank_ker_coordSum] at h
  simp at h
  change Module.finrank (ZMod 2) ↥(golayCode ⊓ LinearMap.ker coordSum) = 11
  omega

theorem natCard_golayEven : Nat.card golayEven = 2 ^ 11 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_golayEven, Nat.card_zmod]

theorem golayEven_weight (c : Word) (hc : c ∈ golayEven) (h0 : c ≠ 0) :
    hammingNorm c = 8 ∨ hammingNorm c = 12 ∨ hammingNorm c = 16 := by
  rw [mem_golayEven_iff_even] at hc
  rcases golayCode_weight c hc.1 h0 with h | h | h | h | h | h | h <;>
    rcases hc.2 with ⟨r, hr⟩ <;> omega

end CFSG.EvenSporadicStandard.Wong77.Module
