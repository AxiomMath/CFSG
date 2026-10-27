module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoMask
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoPlane

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open scoped MatrixGroups
open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Balance

@[expose] def tvMask (p : Fin 6 × Fin 6) : List ℕ :=
  (List.finRange 6).map fun r => 2 ^ (r : ℕ) ^^^ (if p.1 ≠ p.2 ∧ r = p.1 then 2 ^ (p.2 : ℕ) else 0)

@[expose] def wordMask (w : List (Fin 6 × Fin 6)) : List ℕ :=
  w.foldr (fun p A => mmul (tvMask p) A) mone

theorem testBit_tvMask : ∀ (i j a b : Fin 6),
    ((tvMask (i, j)).getD a 0).testBit b =
      xor (decide (a = b)) (decide (i ≠ j ∧ a = i ∧ b = j)) := by
  decide

theorem length_wordMask (w : List (Fin 6 × Fin 6)) : (wordMask w).length = 6 := by
  induction w with
  | nil => rfl
  | cons p w ih => rw [wordMask, List.foldr_cons, length_mmul]; simp [tvMask]

section Ring

variable {R : Type*} [CommRing R] [CharP R 2]

theorem real_tvMask (p : Fin 6 × Fin 6) : real R (tvMask p) = tvMat p := by
  obtain ⟨i, j⟩ := p
  ext a b
  simp only [real, Matrix.of_apply, testBit_tvMask, ind_xor]
  unfold tvMat
  by_cases hij : i = j
  · subst hij
    simp [ind, Matrix.one_apply]
  · simp only [hij, ↓reduceIte, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, ind, ne_eq, not_false_eq_true, true_and, decide_eq_true_eq]
    rcases eq_or_ne a i with rfl | h1
    · rcases eq_or_ne b j with rfl | h2
      · simp
      · simp [h2, Ne.symm h2]
    · simp [h1, Ne.symm h1]

theorem real_wordMask (w : List (Fin 6 × Fin 6)) : real R (wordMask w) = tvMatWord w := by
  induction w with
  | nil => exact real_mone
  | cons p w ih =>
    rw [wordMask, List.foldr_cons, ← wordMask, real_mmul _ _ (length_wordMask w), ih,
      real_tvMask]
    rfl

end Ring

theorem mrow_lt (a : ℕ) : ∀ B : List ℕ, (∀ b ∈ B, b < 64) → mrow a B < 64
  | [], _ => by simp [mrow]
  | b :: bs, h => by
    rw [mrow]
    have hb : b < 2 ^ 6 := h b List.mem_cons_self
    have hbs : mrow (a / 2) bs < 2 ^ 6 := mrow_lt _ bs fun c hc => h c (List.mem_cons_of_mem _ hc)
    refine Nat.xor_lt_two_pow ?_ hbs
    split_ifs
    · exact hb
    · norm_num

theorem mmul_lt (A B : List ℕ) (hB : ∀ b ∈ B, b < 64) : ∀ a ∈ mmul A B, a < 64 := by
  intro a ha
  simp only [mmul, List.mem_map] at ha
  obtain ⟨a', -, rfl⟩ := ha
  exact mrow_lt _ _ hB

@[expose] def comb (z : ℕ) (a b : Fin 6) (x y : ℕ) : ℕ :=
  (if z.testBit a then x else 0) ^^^ (if z.testBit b then y else 0)

theorem testBit_ite (p : Prop) [Decidable p] (x j : ℕ) :
    (if p then x else 0).testBit j = (decide p && x.testBit j) := by
  split_ifs with h <;> simp [h]

theorem mrow_eq_comb {z : ℕ} {a b : Fin 6} (hab : a ≠ b)
    (hz : ∀ k : Fin 6, k ≠ a → k ≠ b → z.testBit k = false) {M : List ℕ} (hM : M.length = 6) :
    mrow z M = comb z a b (M.getD a 0) (M.getD b 0) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  have key := ind_testBit_mrow (R := ZMod 2) z M j
  rw [hM, ← Fin.sum_univ_eq_sum_range, Finset.sum_eq_add (a := a) (b := b) hab (fun k _ hk => by
    rw [hz k hk.1 hk.2]
    simp [ind]) (by simp) (by simp)] at key
  rw [comb, Nat.testBit_xor, testBit_ite, testBit_ite]
  have hind : ∀ p q : Bool, ind (ZMod 2) p = ind (ZMod 2) q → p = q := by decide
  refine hind _ _ (key.trans ?_)
  rw [ind_xor, ind_and, ind_and]
  simp [ind]

@[expose] def rowsOK (Zm : List ℕ) (a b : Fin 6) (x y : ℕ) : Bool :=
  mrow x Zm == comb (Zm.getD a 0) a b x y && mrow y Zm == comb (Zm.getD b 0) a b x y

@[expose] def pairs64 : List (ℕ × ℕ) :=
  (List.range 64).flatMap fun x => (List.range 64).map fun y => (x, y)

@[expose] def pl (Zs : List (List ℕ)) (a b : Fin 6) : List (ℕ × ℕ) :=
  pairs64.filter fun xy => Zs.all fun Zm => rowsOK Zm a b xy.1 xy.2

@[expose] def asm3 (x35 x02 x41 : ℕ × ℕ) : List ℕ :=
  [x02.1, x41.2, x02.2, x35.1, x41.1, x35.2]

@[expose] def p2 (M : List ℕ) : List ℕ := mmul M M

@[expose] def p30 (M : List ℕ) : List ℕ :=
  mmul (mmul (mmul (p2 (p2 (p2 (p2 M)))) (p2 (p2 (p2 M)))) (p2 (p2 M))) (p2 M)

@[expose] def p29 (M : List ℕ) : List ℕ :=
  mmul (mmul (mmul (p2 (p2 (p2 (p2 M)))) (p2 (p2 (p2 M)))) (p2 (p2 M))) M

@[expose] def p10 (M : List ℕ) : List ℕ := mmul (p2 (p2 (p2 M))) (p2 M)

@[expose] def p9 (M : List ℕ) : List ℕ := mmul (p2 (p2 (p2 M))) M

@[expose] def p3 (M : List ℕ) : List ℕ := mmul (p2 M) M

@[expose] def okW (Zs : List (List ℕ)) (M g : List ℕ) : Bool :=
  g.length == 6 && g.all (fun a => decide (a < 64)) &&
    Zs.all (fun Zm => mmul g Zm == mmul Zm g) && p30 g == mone &&
    (p3 (mmul (mmul (mmul M g) (p9 M)) (p29 g)) == mone &&
      !(mmul (mmul (mmul M g) (p9 M)) (p29 g) == mone))

@[expose] def certM (Zs : List (List ℕ)) (W : List (List ℕ)) (M : List ℕ) : Bool :=
  mmul (p30 M) (p30 M) == p30 M && (!(p10 M == mone) || M == mone || W.any (okW Zs M))

@[expose] def dCert (Zs : List (List ℕ)) (W : List (List ℕ)) : Bool :=
  (pl Zs 3 5).all fun x35 => (pl Zs 0 2).all fun x02 => (pl Zs 4 1).all fun x41 =>
    certM Zs W (asm3 x35 x02 x41)

@[expose] def blockOK (Zm : List ℕ) (a b : Fin 6) : Bool :=
  (List.finRange 6).all fun k => (k == a || k == b) ||
    (!(Zm.getD a 0).testBit k && !(Zm.getD b 0).testBit k)

@[expose] def bdiag (Zm : List ℕ) : Bool :=
  blockOK Zm 3 5 && blockOK Zm 0 2 && blockOK Zm 4 1

theorem testBit_eq_false_of_blockOK {Zm : List ℕ} {a b : Fin 6} (h : blockOK Zm a b = true)
    (k : Fin 6) (hka : k ≠ a) (hkb : k ≠ b) :
    (Zm.getD a 0).testBit k = false ∧ (Zm.getD b 0).testBit k = false := by
  simp only [blockOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h k with (h1 | h1) | h1
  · exact absurd h1 hka
  · exact absurd h1 hkb
  · exact h1

theorem rowsOK_of_comm {Zm M : List ℕ} {a b : Fin 6} (hab : a ≠ b) (hZ : blockOK Zm a b = true)
    (hM : M.length = 6) (hc : mmul M Zm = mmul Zm M) :
    rowsOK Zm a b (M.getD a 0) (M.getD b 0) = true := by
  have hza : mrow (Zm.getD a 0) M = comb (Zm.getD a 0) a b (M.getD a 0) (M.getD b 0) :=
    mrow_eq_comb hab (fun k hka hkb => (testBit_eq_false_of_blockOK hZ k hka hkb).1) hM
  have hzb : mrow (Zm.getD b 0) M = comb (Zm.getD b 0) a b (M.getD a 0) (M.getD b 0) :=
    mrow_eq_comb hab (fun k hka hkb => (testBit_eq_false_of_blockOK hZ k hka hkb).2) hM
  have ea := congrArg (fun L : List ℕ => L.getD a 0) hc
  have eb := congrArg (fun L : List ℕ => L.getD b 0) hc
  simp only [getD_mmul] at ea eb
  simp only [rowsOK, Bool.and_eq_true, beq_iff_eq]
  exact ⟨ea.trans hza, eb.trans hzb⟩

theorem mem_pairs64 {x y : ℕ} (hx : x < 64) (hy : y < 64) : (x, y) ∈ pairs64 := by
  simp only [pairs64, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  exact ⟨x, hx, y, hy, rfl, rfl⟩

theorem getD_lt {M : List ℕ} (hM' : ∀ a ∈ M, a < 64) (i : ℕ) : M.getD i 0 < 64 := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : M[i]? with _ | a
  · simp
  · exact hM' a (List.mem_of_getElem? h)

theorem mem_pl {Zs : List (List ℕ)} {M : List ℕ} {a b : Fin 6} (hab : a ≠ b)
    (hZ : ∀ Zm ∈ Zs, blockOK Zm a b = true) (hM : M.length = 6) (hM' : ∀ a ∈ M, a < 64)
    (hc : ∀ Zm ∈ Zs, mmul M Zm = mmul Zm M) : (M.getD a 0, M.getD b 0) ∈ pl Zs a b := by
  simp only [pl, List.mem_filter, List.all_eq_true]
  exact ⟨mem_pairs64 (getD_lt hM' a) (getD_lt hM' b),
    fun Zm hZm => rowsOK_of_comm hab (hZ Zm hZm) hM (hc Zm hZm)⟩

theorem asm3_getD {M : List ℕ} (hM : M.length = 6) :
    asm3 (M.getD ((3 : Fin 6) : ℕ) 0, M.getD ((5 : Fin 6) : ℕ) 0)
      (M.getD ((0 : Fin 6) : ℕ) 0, M.getD ((2 : Fin 6) : ℕ) 0)
      (M.getD ((4 : Fin 6) : ℕ) 0, M.getD ((1 : Fin 6) : ℕ) 0) = M := by
  match M, hM with
  | [m0, m1, m2, m3, m4, m5], _ => rfl

theorem certM_of_dCert {Zs W : List (List ℕ)} (hcert : dCert Zs W = true)
    (hZ : ∀ Zm ∈ Zs, bdiag Zm = true) {M : List ℕ} (hM : M.length = 6) (hM' : ∀ a ∈ M, a < 64)
    (hc : ∀ Zm ∈ Zs, mmul M Zm = mmul Zm M) : certM Zs W M = true := by
  have hZ' : ∀ Zm ∈ Zs, blockOK Zm 3 5 = true ∧ blockOK Zm 0 2 = true ∧
      blockOK Zm 4 1 = true := by
    intro Zm hZm
    have h := hZ Zm hZm
    simp only [bdiag, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have h35 := mem_pl (a := 3) (b := 5) (by decide) (fun Zm h => (hZ' Zm h).1) hM hM' hc
  have h02 := mem_pl (a := 0) (b := 2) (by decide) (fun Zm h => (hZ' Zm h).2.1) hM hM' hc
  have h41 := mem_pl (a := 4) (b := 1) (by decide) (fun Zm h => (hZ' Zm h).2.2) hM hM' hc
  simp only [dCert, List.all_eq_true] at hcert
  have := hcert _ h35 _ h02 _ h41
  rwa [asm3_getD hM] at this

section Pow

variable {R : Type*} [CommRing R] [CharP R 2]

theorem length_p2 {M : List ℕ} (hM : M.length = 6) : (p2 M).length = 6 := by
  rw [p2, length_mmul, hM]

theorem real_p2 {M : List ℕ} (hM : M.length = 6) : real R (p2 M) = real R M ^ 2 := by
  rw [p2, real_mmul _ _ hM, pow_two]

theorem real_mmul_pow {M : List ℕ} (A B : List ℕ) {a b : ℕ} (hB : B.length = 6)
    (hA' : real R A = real R M ^ a) (hB' : real R B = real R M ^ b) :
    real R (mmul A B) = real R M ^ (a + b) := by
  rw [real_mmul _ _ hB, hA', hB', pow_add]

theorem real_p30 {M : List ℕ} (hM : M.length = 6) : real R (p30 M) = real R M ^ 30 := by
  have h2 := real_p2 (R := R) hM
  have l2 := length_p2 hM
  have h4 : real R (p2 (p2 M)) = real R M ^ 4 := by rw [real_p2 l2, h2, ← pow_mul]
  have l4 := length_p2 l2
  have h8 : real R (p2 (p2 (p2 M))) = real R M ^ 8 := by rw [real_p2 l4, h4, ← pow_mul]
  have l8 := length_p2 l4
  have h16 : real R (p2 (p2 (p2 (p2 M)))) = real R M ^ 16 := by rw [real_p2 l8, h8, ← pow_mul]
  rw [p30, real_mmul_pow _ _ l2 (real_mmul_pow _ _ l4 (real_mmul_pow _ _ l8 h16 h8) h4) h2]

theorem real_p29 {M : List ℕ} (hM : M.length = 6) : real R (p29 M) = real R M ^ 29 := by
  have h2 := real_p2 (R := R) hM
  have l2 := length_p2 hM
  have h4 : real R (p2 (p2 M)) = real R M ^ 4 := by rw [real_p2 l2, h2, ← pow_mul]
  have l4 := length_p2 l2
  have h8 : real R (p2 (p2 (p2 M))) = real R M ^ 8 := by rw [real_p2 l4, h4, ← pow_mul]
  have l8 := length_p2 l4
  have h16 : real R (p2 (p2 (p2 (p2 M)))) = real R M ^ 16 := by rw [real_p2 l8, h8, ← pow_mul]
  rw [p29, real_mmul_pow _ _ hM (real_mmul_pow _ _ l4 (real_mmul_pow _ _ l8 h16 h8) h4)
    (pow_one _).symm]

theorem real_p10 {M : List ℕ} (hM : M.length = 6) : real R (p10 M) = real R M ^ 10 := by
  have h2 := real_p2 (R := R) hM
  have l2 := length_p2 hM
  have h4 : real R (p2 (p2 M)) = real R M ^ 4 := by rw [real_p2 l2, h2, ← pow_mul]
  have l4 := length_p2 l2
  have h8 : real R (p2 (p2 (p2 M))) = real R M ^ 8 := by rw [real_p2 l4, h4, ← pow_mul]
  rw [p10, real_mmul_pow _ _ l2 h8 h2]

theorem real_p9 {M : List ℕ} (hM : M.length = 6) : real R (p9 M) = real R M ^ 9 := by
  have h2 := real_p2 (R := R) hM
  have l2 := length_p2 hM
  have h4 : real R (p2 (p2 M)) = real R M ^ 4 := by rw [real_p2 l2, h2, ← pow_mul]
  have l4 := length_p2 l2
  have h8 : real R (p2 (p2 (p2 M))) = real R M ^ 8 := by rw [real_p2 l4, h4, ← pow_mul]
  rw [p9, real_mmul_pow _ _ hM h8 (pow_one _).symm]

theorem real_p3 {M : List ℕ} (hM : M.length = 6) : real R (p3 M) = real R M ^ 3 := by
  rw [p3, real_mmul_pow _ _ hM (real_p2 hM) (pow_one _).symm]

theorem length_p30 {M : List ℕ} (hM : M.length = 6) : (p30 M).length = 6 := by
  simp [p30, length_mmul, p2, hM]

theorem length_p10 {M : List ℕ} (hM : M.length = 6) : (p10 M).length = 6 := by
  simp [p10, length_mmul, p2, hM]

theorem length_p3 {M : List ℕ} (hM : M.length = 6) : (p3 M).length = 6 := by
  simp [p3, length_mmul, p2, hM]

end Pow

theorem mone_lt : ∀ a ∈ mone, a < 64 := by decide

theorem mpow_lt {A : List ℕ} (hA : ∀ a ∈ A, a < 64) : ∀ n, ∀ a ∈ mpow A n, a < 64
  | 0 => mone_lt
  | n + 1 => mmul_lt A (mpow A n) (mpow_lt hA n)

theorem length_mone : mone.length = 6 := rfl

section Main

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

theorem eq_zero_or_one_of_card_two (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 hu).1
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 c hc) 1)

theorem real_maskOf_SL (hK : Nat.card K = 2) (x : SL(6, K)) :
    real K (maskOf (x : Matrix (Fin 6) (Fin 6) K)) = x :=
  real_maskOf (eq_zero_or_one_of_card_two hK) _

theorem mmul_comm_of_commute (hK : Nat.card K = 2) {x Z : SL(6, K)} {Zm : List ℕ}
    (hZ : (Z : Matrix (Fin 6) (Fin 6) K) = real K Zm) (hl : Zm.length = 6)
    (hb : ∀ a ∈ Zm, a < 64) (hxZ : x * Z = Z * x) :
    mmul (maskOf (x : Matrix (Fin 6) (Fin 6) K)) Zm =
      mmul Zm (maskOf (x : Matrix (Fin 6) (Fin 6) K)) := by
  set A := maskOf (x : Matrix (Fin 6) (Fin 6) K) with hA
  have hAl : A.length = 6 := length_maskOf _
  refine real_injective (R := K) (by rw [length_mmul, hAl]) (by rw [length_mmul, hl])
    (mmul_lt _ _ hb) (mmul_lt _ _ (maskOf_lt _)) ?_
  rw [real_mmul _ _ hl, real_mmul _ _ hAl, ← hZ, hA, real_maskOf_SL hK,
    ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hxZ]

theorem gLAPPrimeCoreOf_centralizer_pair_eq_bot (hK : Nat.card K = 2) {Z₁ Z₂ : SL(6, K)}
    {Zm₁ Zm₂ : List ℕ} (h₁ : (Z₁ : Matrix (Fin 6) (Fin 6) K) = real K Zm₁)
    (h₂ : (Z₂ : Matrix (Fin 6) (Fin 6) K) = real K Zm₂) (hl₁ : Zm₁.length = 6)
    (hl₂ : Zm₂.length = 6) (hb₁ : ∀ a ∈ Zm₁, a < 64) (hb₂ : ∀ a ∈ Zm₂, a < 64)
    (hd₁ : bdiag Zm₁ = true) (hd₂ : bdiag Zm₂ = true) {W : List (List ℕ)}
    (hcert : dCert [Zm₁, Zm₂] W = true) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({Z₁, Z₂} : Set SL(6, K))) = ⊥ := by
  set C := Subgroup.centralizer ({Z₁, Z₂} : Set SL(6, K)) with hC
  set N := GLAPPrimeCoreOf 3 C with hN
  have hcop : Nat.Coprime 3 (Nat.card N) := coprime_card_gLAPPrimeCoreOf' Nat.prime_three C
  have memC : ∀ g : SL(6, K), g * Z₁ = Z₁ * g → g * Z₂ = Z₂ * g → g ∈ C := by
    intro g h1 h2
    rw [hC, Subgroup.mem_centralizer_iff]
    rintro h (rfl | rfl)
    · exact h1.symm
    · exact h2.symm
  have hmemC : ∀ g ∈ C, g * Z₁ = Z₁ * g ∧ g * Z₂ = Z₂ * g := by
    intro g hg
    rw [hC, Subgroup.mem_centralizer_iff] at hg
    exact ⟨(hg Z₁ (Set.mem_insert _ _)).symm, (hg Z₂ (by simp)).symm⟩
  have hrealpow : ∀ (g : SL(6, K)) (n : ℕ),
      ((g ^ n : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = (g : Matrix (Fin 6) (Fin 6) K) ^ n :=
    fun g n => Matrix.SpecialLinearGroup.coe_pow g n
  have hinjmask : ∀ {A B : List ℕ}, A.length = 6 → B.length = 6 → (∀ a ∈ A, a < 64) →
      (∀ b ∈ B, b < 64) → real K A = real K B → A = B :=
    fun hA hB hA' hB' h => real_injective hA hB hA' hB' h
  refine eq_bot_iff.2 fun x hx => ?_
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxC : x ∈ C := gLAPPrimeCoreOf_le_self' C hx
  obtain ⟨hx₁, hx₂⟩ := hmemC x hxC
  set A := maskOf (x : Matrix (Fin 6) (Fin 6) K) with hAdef
  have hAl : A.length = 6 := length_maskOf _
  have hAb : ∀ a ∈ A, a < 64 := maskOf_lt _
  have hAx : real K A = x := real_maskOf_SL hK x
  have hc : ∀ Zm ∈ [Zm₁, Zm₂], mmul A Zm = mmul Zm A := by
    intro Zm hZm
    rcases List.mem_pair.1 hZm with rfl | rfl
    · exact mmul_comm_of_commute hK h₁ hl₁ hb₁ hx₁
    · exact mmul_comm_of_commute hK h₂ hl₂ hb₂ hx₂
  have hd : ∀ Zm ∈ [Zm₁, Zm₂], bdiag Zm = true := by
    intro Zm hZm
    rcases List.mem_pair.1 hZm with rfl | rfl
    · exact hd₁
    · exact hd₂
  have hcM := certM_of_dCert hcert hd hAl hAb hc
  simp only [certM, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, List.any_eq_true] at hcM
  obtain ⟨hidem, hrest⟩ := hcM
  have hx30 : x ^ 30 = 1 := by
    have e := congrArg (real K) hidem
    rw [real_mmul _ _ (length_p30 hAl), real_p30 hAl, hAx] at e
    have e' : x ^ 30 * x ^ 30 = x ^ 30 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, hrealpow]
      exact e)
    exact mul_eq_left.1 e'
  have hord3 : Nat.Coprime 3 (orderOf x) := by
    have hdvd : orderOf x ∣ Nat.card N := by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_right hdvd hcop
  have hx10 : x ^ 10 = 1 := by
    have h30 : orderOf x ∣ 10 * 3 := orderOf_dvd_of_pow_eq_one hx30
    exact orderOf_dvd_iff_pow_eq_one.1 (Nat.Coprime.dvd_of_dvd_mul_right hord3.symm h30)
  have hp10 : p10 A = mone := by
    refine hinjmask (length_p10 hAl) length_mone (mmul_lt _ _ (mmul_lt _ _ hAb)) mone_lt ?_
    rw [real_p10 hAl, hAx, real_mone, ← hrealpow, hx10, Matrix.SpecialLinearGroup.coe_one]
  have hA1 : A ≠ mone := by
    intro h
    apply hx1
    refine Subtype.ext ?_
    rw [← hAx, h, real_mone, Matrix.SpecialLinearGroup.coe_one]
  rcases hrest with (h | h) | ⟨g, -, hg⟩
  · exact h hp10
  · exact hA1 h
  simp only [okW, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hg
  obtain ⟨⟨⟨⟨hgl, hgb⟩, hgZ⟩, hg30⟩, hc3, hc1⟩ := hg
  have hg30' : real K g ^ 30 = 1 := by rw [← real_p30 hgl, hg30, real_mone]
  have hdet : (real K g).det = 1 := by
    have hu : IsUnit (real K g) := by
      refine ⟨⟨real K g, real K g ^ 29, ?_, ?_⟩, rfl⟩
      · rw [← pow_succ', hg30']
      · rw [← pow_succ, hg30']
    have hd0 : (real K g).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 hu |>.ne_zero
    rcases eq_zero_or_one_of_card_two hK (real K g).det with h | h
    · exact absurd h hd0
    · exact h
  set gK : SL(6, K) := ⟨real K g, hdet⟩ with hgK
  have hgKZ : ∀ {Z : SL(6, K)} {Zm : List ℕ}, (Z : Matrix (Fin 6) (Fin 6) K) = real K Zm →
      Zm.length = 6 → Zm ∈ [Zm₁, Zm₂] → gK * Z = Z * gK := by
    intro Z Zm hZ hl hZm
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hZ]
    change real K g * real K Zm = real K Zm * real K g
    rw [← real_mmul _ _ hl, ← real_mmul _ _ hgl, hgZ Zm hZm]
  have hgC : gK ∈ C := memC gK (hgKZ h₁ hl₁ (by simp)) (hgKZ h₂ hl₂ (by simp))
  set cK := x * gK * x⁻¹ * gK⁻¹ with hcK
  have hcN : cK ∈ N := by
    have h1 : gK * x⁻¹ * gK⁻¹ ∈ N := gLAPPrimeCoreOf_conj_mem' gK hgC x⁻¹ (N.inv_mem hx)
    have h2 := N.mul_mem hx h1
    rw [hcK]
    simpa [mul_assoc] using h2
  have hxinv : x⁻¹ = x ^ 9 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx10]
  have hginv : gK⁻¹ = gK ^ 29 := by
    have hgK30 : gK ^ 30 = 1 := Subtype.ext (by
      rw [hrealpow]
      exact hg30')
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hgK30]
  set c := mmul (mmul (mmul A g) (p9 A)) (p29 g) with hcdef
  have hcl : c.length = 6 := by simp [hcdef, length_mmul, hAl]
  have hcreal : real K c = cK := by
    rw [hcK, hxinv, hginv, hcdef, real_mmul _ _ (by simp [p29, length_mmul, p2, hgl]),
      real_mmul _ _ (by simp [p9, length_mmul, p2, hAl]), real_mmul _ _ hgl, real_p9 hAl,
      real_p29 hgl, hAx]
    simp only [Matrix.SpecialLinearGroup.coe_mul, hrealpow]
    rfl
  have hc3' : cK ^ 3 = 1 := Subtype.ext (by
    rw [hrealpow, ← hcreal, ← real_p3 hcl, hc3, real_mone, Matrix.SpecialLinearGroup.coe_one])
  have hc1' : cK ≠ 1 := by
    intro h
    apply hc1
    refine hinjmask hcl length_mone ?_ mone_lt ?_
    · exact mmul_lt _ _ (by
        intro a ha
        simp only [p29, mmul, List.mem_map] at ha
        obtain ⟨a', -, rfl⟩ := ha
        exact mrow_lt _ _ hgb)
    · rw [hcreal, h, real_mone, Matrix.SpecialLinearGroup.coe_one]
  have hcord : orderOf cK = 3 := orderOf_eq_prime hc3' hc1'
  have h3 : 3 ∣ Nat.card N := by
    rw [← hcord, ← Subgroup.orderOf_mk cK hcN]
    exact orderOf_dvd_natCard _
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)

end Main

@[expose] def zword (v : Fin 3 → ℕ) : List (Fin 6 × Fin 6) :=
  (List.replicate (v 0) [(3, 5), (5, 3)]).flatten ++
    (List.replicate (v 1) [(0, 2), (2, 0)]).flatten ++
      (List.replicate (v 2) [(4, 1), (1, 4)]).flatten

section Torus

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

@[expose] noncomputable def zSL (v : Fin 3 → ℕ) : SL(6, K) := tvSLWord (zword v)

theorem coe_tvSLWord_eq_real (w : List (Fin 6 × Fin 6)) :
    ((tvSLWord w : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = real K (wordMask w) := by
  rw [coe_tvSLWord, real_wordMask]

theorem wordMask_lt (w : List (Fin 6 × Fin 6)) : ∀ a ∈ wordMask w, a < 64 := by
  induction w with
  | nil => exact mone_lt
  | cons p w ih =>
    rw [wordMask, List.foldr_cons, ← wordMask]
    exact mmul_lt _ _ ih

@[expose] def zFacts (z e₁ e₂ : Fin 3 → ℕ) : Bool :=
  let Zm := wordMask (zword z)
  let A := wordMask (zword e₁)
  let B := wordMask (zword e₂)
  mmul A Zm == mmul Zm A && mmul B Zm == mmul Zm B && mmul A B == mmul B A &&
    mpow A 3 == mone && mpow B 3 == mone &&
    ((List.range 3).all fun i => (List.range 3).all fun j =>
      (i == 0 && j == 0) || !(mmul (mpow A i) (mpow B j) == mone)) &&
    bdiag Zm && bdiag A && bdiag B && bdiag (wordMask (zword e₁ ++ zword e₂)) &&
    bdiag (wordMask (zword e₁ ++ zword e₂ ++ zword e₂))

theorem centralizer_singleton_inf_singleton {G : Type*} [Group G] (a b : G) :
    Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {b} =
      Subgroup.centralizer ({a, b} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    Set.mem_insert_iff, forall_eq_or_imp, forall_eq]

theorem gLAPPrimeCoreOf_centralizer_zSL_eq_bot (hK : Nat.card K = 2) (z e₁ e₂ : Fin 3 → ℕ)
    (hf : zFacts z e₁ e₂ = true) {W₁ W₂ W₃ W₄ : List (List ℕ)}
    (c₁ : dCert [wordMask (zword z), wordMask (zword e₁)] W₁ = true)
    (c₂ : dCert [wordMask (zword z), wordMask (zword e₂)] W₂ = true)
    (c₃ : dCert [wordMask (zword z), wordMask (zword e₁ ++ zword e₂)] W₃ = true)
    (c₄ : dCert [wordMask (zword z), wordMask (zword e₁ ++ zword e₂ ++ zword e₂)] W₄ = true) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({zSL z} : Set SL(6, K))) = ⊥ := by
  simp only [zFacts, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAZ, hBZ⟩, hAB⟩, hA3⟩, hB3⟩, hinjm⟩, hdZ⟩, hdA⟩, hdB⟩, hdAB⟩, hdABB⟩ := hf
  set Zm := wordMask (zword z) with hZm
  set A := wordMask (zword e₁) with hA
  set B := wordMask (zword e₂) with hB
  have hZl : Zm.length = 6 := length_wordMask _
  have hAl : A.length = 6 := length_wordMask _
  have hBl : B.length = 6 := length_wordMask _
  have hrZ : ((zSL z : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = real K Zm :=
    coe_tvSLWord_eq_real _
  have hrA : ((zSL e₁ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = real K A :=
    coe_tvSLWord_eq_real _
  have hrB : ((zSL e₂ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = real K B :=
    coe_tvSLWord_eq_real _
  have commOf : ∀ {g h : SL(6, K)} {gm hm : List ℕ},
      ((g : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = real K gm →
      ((h : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = real K hm → gm.length = 6 →
      hm.length = 6 → mmul gm hm = mmul hm gm → g * h = h * g := by
    intro g h gm hm hg hh hgl hhl hc
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg, hh,
      ← real_mmul _ _ hhl, ← real_mmul _ _ hgl, hc]
  have powOf : ∀ {g : SL(6, K)} {gm : List ℕ},
      ((g : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = real K gm → gm.length = 6 → ∀ n,
      ((g ^ n : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = real K (mpow gm n) := by
    intro g gm hg hgl n
    rw [Matrix.SpecialLinearGroup.coe_pow, hg, real_mpow _ hgl]
  have hα : zSL e₁ ∈ Subgroup.centralizer ({zSL z} : Set SL(6, K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commOf hrA hrZ hAl hZl hAZ
  have hβ : zSL e₂ ∈ Subgroup.centralizer ({zSL z} : Set SL(6, K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commOf hrB hrZ hBl hZl hBZ
  have hαβ : (zSL e₁ : SL(6, K)) * zSL e₂ = zSL e₂ * zSL e₁ := commOf hrA hrB hAl hBl hAB
  have hpow3 : ∀ {g : SL(6, K)} {gm : List ℕ},
      ((g : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = real K gm → gm.length = 6 →
      mpow gm 3 = mone → g ^ 3 = 1 := by
    intro g gm hg hgl h3
    refine Subtype.ext ?_
    rw [powOf hg hgl, h3, real_mone, Matrix.SpecialLinearGroup.coe_one]
  have hinj : ∀ a b : ZMod 3, (zSL e₁ : SL(6, K)) ^ a.val * zSL e₂ ^ b.val = 1 →
      a = 0 ∧ b = 0 := by
    intro a b hab
    have hm : mmul (mpow A a.val) (mpow B b.val) = mone := by
      refine real_injective (R := K) (by rw [length_mmul, length_mpow _ hAl]) length_mone
        (mmul_lt _ _ (mpow_lt (wordMask_lt _) _)) mone_lt ?_
      rw [real_mmul _ _ (length_mpow _ hBl _), ← powOf hrA hAl, ← powOf hrB hBl,
        ← Matrix.SpecialLinearGroup.coe_mul, hab, Matrix.SpecialLinearGroup.coe_one, real_mone]
    rcases hinjm a.val (ZMod.val_lt a) b.val (ZMod.val_lt b) with h | h
    · exact ⟨(ZMod.val_eq_zero a).1 h.1, (ZMod.val_eq_zero b).1 h.2⟩
    · exact absurd hm h
  have hpair : ∀ {y : SL(6, K)} {w : List (Fin 6 × Fin 6)} {W : List (List ℕ)},
      y = tvSLWord w → bdiag (wordMask w) = true → dCert [Zm, wordMask w] W = true →
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({zSL z} : Set SL(6, K)) ⊓
        Subgroup.centralizer {y}) = ⊥ := by
    intro y w W hy hd hc
    rw [centralizer_singleton_inf_singleton, hy]
    exact gLAPPrimeCoreOf_centralizer_pair_eq_bot hK hrZ (coe_tvSLWord_eq_real w) hZl
      (length_wordMask w) (wordMask_lt _) (wordMask_lt w) hdZ hd hc
  refine gLAPPrimeCoreOf_eq_bot_of_four hα hβ hαβ (hpow3 hrA hAl hA3) (hpow3 hrB hBl hB3) hinj
    (hpair rfl hdA c₁) (hpair rfl hdB c₂) (hpair (tvSLWord_append _ _).symm hdAB c₃) ?_
  refine hpair ?_ hdABB c₄
  rw [pow_two, ← mul_assoc, tvSLWord_append, tvSLWord_append]
  rfl

end Torus

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
