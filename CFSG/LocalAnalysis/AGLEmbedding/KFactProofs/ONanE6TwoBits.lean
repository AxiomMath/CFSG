module

public import CFSG.Monster.B.E6.StdF4LeviRank

public section

namespace CFSG.AGLEmbedding.E6Two

open CFSG.Blueprint.Chevalley CFSG.Monster.B.Classical.E6Adjoint

@[expose] def colE (A q : ℕ) : ℕ :=
  A / 2 ^ (78 * q) % 2 ^ 78

@[expose] def slotsE : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ (78 * n) * 1 + slotsE n

@[expose] def mulAuxE (A B : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (colE A n * (B / 2 ^ n &&& slotsE 78)) ^^^ mulAuxE A B n

@[expose] def mulE (A B : ℕ) : ℕ :=
  mulAuxE A B 78

@[expose] def packE : List ℕ → ℕ
  | [] => 0
  | a :: L => 2 ^ 78 * packE L + a % 2 ^ 78

@[expose] def oneE : ℕ :=
  packE ((List.range 78).map (2 ^ ·))

@[expose] def applyEAux (A m : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => applyEAux A m n ^^^ (if m.testBit n then colE A n else 0)

@[expose] def applyE (A m : ℕ) : ℕ :=
  applyEAux A m 78

theorem slotsE_lt : ∀ n, slotsE n < 2 ^ (78 * n)
  | 0 => by simp [slotsE]
  | n + 1 => by
    have h := slotsE_lt n
    have h1 : 2 ^ (78 * n) * 2 ≤ 2 ^ (78 * (n + 1)) := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [slotsE]
    omega

theorem testBit_slotsE : ∀ n k : ℕ,
    (slotsE n).testBit k = (decide (k < 78 * n) && decide (k % 78 = 0))
  | 0, k => by simp [slotsE]
  | n + 1, k => by
    rw [slotsE, Nat.testBit_two_pow_mul_add _ (slotsE_lt n), testBit_slotsE n k]
    split_ifs with hk
    · rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    · rw [Bool.eq_iff_iff, Nat.testBit_one_eq_true_iff_self_eq_zero]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega

theorem mod_eq_of_spreadE {S : ℕ} (hS : ∀ k, S.testBit k = true → k % 78 = 0) :
    S % 2 ^ 78 = if S.testBit 0 then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · cases h : S.testBit 0 <;> simp
  · have h1 : (if S.testBit 0 then 1 else 0 : ℕ).testBit i = false := by
      split_ifs
      · exact Nat.testBit_lt_two_pow (by
          calc (1 : ℕ) < 2 ^ 1 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi)
      · simp
    rw [h1]
    by_cases h2 : i < 78
    · have h3 : S.testBit i = false := by
        by_contra h
        have := hS i (by simpa using h)
        omega
      simp [h3]
    · simp [h2]

theorem mul_eq_of_spreadE (a S : ℕ) :
    a * S = 2 ^ 78 * (a * (S / 2 ^ 78)) + a * (S % 2 ^ 78) := by
  conv_lhs => rw [← Nat.div_add_mod S (2 ^ 78)]
  ring

theorem testBit_mul_of_spreadE {a : ℕ} (ha : a < 2 ^ 78) {p : ℕ} (hp : p < 78) :
    ∀ (c : ℕ) {S : ℕ}, (∀ k, S.testBit k = true → k % 78 = 0) →
      (a * S).testBit (78 * c + p) = (S.testBit (78 * c) && a.testBit p) := by
  intro c
  induction c with
  | zero =>
    intro S hS
    have hlt : a * (S % 2 ^ 78) < 2 ^ 78 := by
      rw [mod_eq_of_spreadE hS]
      split_ifs <;> omega
    rw [mul_eq_of_spreadE, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_left (by omega),
      mod_eq_of_spreadE hS]
    simp only [Nat.mul_zero, Nat.zero_add]
    split_ifs with h <;> simp [h]
  | succ c ih =>
    intro S hS
    have hlt : a * (S % 2 ^ 78) < 2 ^ 78 := by
      rw [mod_eq_of_spreadE hS]
      split_ifs <;> omega
    have hS' : ∀ k, (S / 2 ^ 78).testBit k = true → k % 78 = 0 := by
      intro k hk
      rw [Nat.testBit_div_two_pow] at hk
      have := hS _ hk
      omega
    rw [mul_eq_of_spreadE, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_right (by omega),
      show 78 * (c + 1) + p - 78 = 78 * c + p by omega, ih hS', Nat.testBit_div_two_pow,
      show 78 * c + 78 = 78 * (c + 1) by ring]

theorem testBit_spreadE (B q k : ℕ) :
    (B / 2 ^ q &&& slotsE 78).testBit k =
      (B.testBit (k + q) && decide (k < 78 * 78) && decide (k % 78 = 0)) := by
  rw [Nat.testBit_land, Nat.testBit_div_two_pow, testBit_slotsE, Bool.and_assoc]

theorem spread_specE (B q : ℕ) :
    ∀ k, (B / 2 ^ q &&& slotsE 78).testBit k = true → k % 78 = 0 := by
  intro k hk
  rw [testBit_spreadE] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  exact hk.2

theorem col_ltE (A q : ℕ) : colE A q < 2 ^ 78 :=
  Nat.mod_lt _ (Nat.two_pow_pos 78)

theorem testBit_colE (A q : ℕ) {p : ℕ} (hp : p < 78) :
    (colE A q).testBit p = A.testBit (78 * q + p) := by
  rw [colE, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true hp, Bool.true_and,
    Nat.add_comm]

theorem testBit_packE : ∀ (L : List ℕ) (c : ℕ) {p : ℕ}, p < 78 →
    (packE L).testBit (78 * c + p) = (L.getD c 0).testBit p
  | [], c, p, _ => by simp [packE]
  | a :: L, c, p, hp => by
    rw [packE, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt a (Nat.two_pow_pos 78))]
    rcases c with _ | c
    · rw [ite_eq_left (by omega), Nat.testBit_mod_two_pow]
      simp [hp]
    · rw [ite_eq_right (by omega), show 78 * (c + 1) + p - 78 = 78 * c + p by omega,
        testBit_packE L c hp]
      simp

theorem colE_packE (L : List ℕ) (c : ℕ) : colE (packE L) c = L.getD c 0 % 2 ^ 78 := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 78
  · rw [testBit_colE _ _ hp, testBit_packE _ _ hp, Nat.testBit_mod_two_pow]
    simp [hp]
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_lt_two_pow (col_ltE _ _ |>.trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [hp]

theorem testBit_mulAuxE (A B : ℕ) {c p : ℕ} (hc : c < 78) (hp : p < 78) :
    ∀ n, (mulAuxE A B n).testBit (78 * c + p) =
      (List.range n).foldl (fun acc q => acc ^^ (B.testBit (78 * c + q) && A.testBit (78 * q + p)))
        false
  | 0 => by simp [mulAuxE]
  | n + 1 => by
    have hX : (colE A n * (B / 2 ^ n &&& slotsE 78)).testBit (78 * c + p) =
        (B.testBit (78 * c + n) && A.testBit (78 * n + p)) := by
      rw [testBit_mul_of_spreadE (col_ltE A n) hp c (spread_specE B n), testBit_spreadE,
        testBit_colE A n hp]
      have h1 : decide (78 * c < 78 * 78) = true := decide_eq_true (by omega)
      have h2 : decide (78 * c % 78 = 0) = true := decide_eq_true (by omega)
      rw [h1, h2, Bool.and_true, Bool.and_true]
    rw [mulAuxE, Nat.testBit_xor, hX, testBit_mulAuxE A B hc hp n, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil, Bool.xor_comm]

theorem testBit_applyEAux (A m : ℕ) {p : ℕ} (hp : p < 78) :
    ∀ n, (applyEAux A m n).testBit p =
      (List.range n).foldl (fun acc q => acc ^^ (m.testBit q && A.testBit (78 * q + p))) false
  | 0 => by simp [applyEAux]
  | n + 1 => by
    have hX : (if m.testBit n then colE A n else 0).testBit p =
        (m.testBit n && A.testBit (78 * n + p)) := by
      split_ifs with h
      · rw [testBit_colE A n hp, h, Bool.true_and]
      · simp [h]
    rw [applyEAux, Nat.testBit_xor, hX, testBit_applyEAux A m hp n, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil, Bool.xor_comm]

theorem applyEAux_lt (A m : ℕ) : ∀ n, applyEAux A m n < 2 ^ 78
  | 0 => by simp [applyEAux]
  | n + 1 => by
    rw [applyEAux]
    refine Nat.xor_lt_two_pow (applyEAux_lt A m n) ?_
    split_ifs
    · exact col_ltE A n
    · exact Nat.two_pow_pos 78

theorem applyE_lt (A m : ℕ) : applyE A m < 2 ^ 78 :=
  applyEAux_lt A m 78

theorem colE_mulE (A B : ℕ) {c : ℕ} (hc : c < 78) :
    colE (mulE A B) c = applyE A (colE B c) := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 78
  · rw [testBit_colE _ _ hp, mulE, testBit_mulAuxE A B hc hp, applyE, testBit_applyEAux _ _ hp]
    refine List.foldl_ext _ _ _ fun acc q hq => ?_
    have hq' : q < 78 := List.mem_range.1 hq
    rw [testBit_colE B c hq']
  · rw [Nat.testBit_lt_two_pow (col_ltE _ _ |>.trans_le (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow ((applyE_lt _ _).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]

section Rep

variable {K : Type} [Field K]

@[expose] def RepE (f : Module.End K (RootModule Tag.E6 K))
    (A : ℕ) : Prop :=
  ∀ k : Fin 78, f (toVec K (1 <<< (k : ℕ))) = toVec K (colE A k)

theorem toVec_eq_sum (m : ℕ) :
    toVec K m = ∑ k : Fin 78, if m.testBit k then toVec K (1 <<< (k : ℕ)) else 0 := by
  rw [show toVec K m = ∑ k : Fin 78, if m.testBit k then Finsupp.single (lab k) (1 : K) else 0
    from rfl]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [toVec_one_shiftLeft]

theorem toVec_mod (m : ℕ) : toVec K (m % 2 ^ 78) = toVec K m := by
  rw [toVec_eq_sum, toVec_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℕ) < 78 := k.2
  rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and]

theorem toVec_applyEAux [CharP K 2] (A m : ℕ) (n : ℕ) :
    toVec K (applyEAux A m n) =
      ∑ k ∈ Finset.range n, if m.testBit k then toVec K (colE A k) else 0 := by
  induction n with
  | zero => simp [applyEAux, toVec_zero]
  | succ n ih =>
    rw [applyEAux, toVec_xor, ih, Finset.sum_range_succ]
    split_ifs <;> simp [toVec_zero]

theorem toVec_applyE [CharP K 2] (A m : ℕ) :
    toVec K (applyE A m) = ∑ k : Fin 78, if m.testBit k then toVec K (colE A k) else 0 := by
  rw [applyE, toVec_applyEAux, Finset.sum_range]

theorem RepE.apply [CharP K 2]
    {f : Module.End K (RootModule Tag.E6 K)} {A : ℕ} (h : RepE f A) (m : ℕ) :
    f (toVec K m) = toVec K (applyE A m) := by
  rw [toVec_eq_sum, map_sum, toVec_applyE]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · exact h k
  · exact map_zero f

theorem RepE.mul [CharP K 2]
    {f g : Module.End K (RootModule Tag.E6 K)} {A B : ℕ} (hf : RepE f A) (hg : RepE g B) :
    RepE (f * g) (mulE A B) := by
  intro k
  rw [Module.End.mul_apply, hg k, hf.apply, colE_mulE A B k.2]

theorem repE_one :
    RepE (1 : Module.End K (RootModule Tag.E6 K)) oneE := by
  intro k
  have hk : (k : ℕ) < 78 := k.2
  rw [Module.End.one_apply, oneE, colE_packE, List.getD_eq_getElem _ _ (by simp),
    List.getElem_map, List.getElem_range, ← Nat.one_shiftLeft, toVec_mod]

theorem RepE.ext {f g : Module.End K (RootModule Tag.E6 K)}
    {A : ℕ} (hf : RepE f A) (hg : RepE g A) : f = g := by
  refine ext_single fun x => ?_
  obtain ⟨k, rfl⟩ := lab_surjective x
  rw [← toVec_one_shiftLeft, hf k, hg k]

theorem toVec_inj {m n : ℕ} (hm : m < 2 ^ 78) (hn : n < 2 ^ 78)
    (h : toVec K m = toVec K n) : m = n := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hq : q < 78
  · have := congrArg (fun v => v (lab ⟨q, hq⟩)) h
    simp only [CFSG.Monster.B.E6.StdF4.toVec_apply_lab] at this
    by_cases h1 : m.testBit q <;> by_cases h2 : n.testBit q <;> simp_all
  · rw [Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (hn.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem RepE.eq_iff [CharP K 2]
    {f g : Module.End K (RootModule Tag.E6 K)} {A B : ℕ} (hf : RepE f A) (hg : RepE g B) :
    f = g ↔ A % 2 ^ 6084 = B % 2 ^ 6084 := by
  constructor
  · rintro rfl
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hk : k < 6084
    · have hc : k / 78 < 78 := by omega
      have hp : k % 78 < 78 := by omega
      have hcol := toVec_inj (col_ltE A (k / 78)) (col_ltE B (k / 78))
        ((hf ⟨k / 78, hc⟩).symm.trans (hg ⟨k / 78, hc⟩))
      have e : k = 78 * (k / 78) + k % 78 := (Nat.div_add_mod k 78).symm
      have h1 := testBit_colE A (k / 78) hp
      have h2 := testBit_colE B (k / 78) hp
      rw [hcol, h2, ← e] at h1
      rw [← h1]
    · simp [hk]
  · intro h
    have hcol : ∀ k : Fin 78, colE A k = colE B k := by
      intro k
      apply Nat.eq_of_testBit_eq
      intro p
      by_cases hp : p < 78
      · rw [testBit_colE _ _ hp, testBit_colE _ _ hp]
        have h1 := congrArg (fun n => n.testBit (78 * k + p)) h
        simp only [Nat.testBit_mod_two_pow] at h1
        have hlt : 78 * (k : ℕ) + p < 6084 := by have := k.2; omega
        rwa [decide_eq_true hlt, Bool.true_and, Bool.true_and] at h1
      · rw [Nat.testBit_lt_two_pow ((col_ltE A k).trans_le
          (Nat.pow_le_pow_right (by norm_num) (by omega))),
          Nat.testBit_lt_two_pow ((col_ltE B k).trans_le
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    exact RepE.ext hf (fun k => (hg k).trans (by rw [hcol k]))

end Rep

@[expose] def rootCols (a : ℕ) : List ℕ :=
  (List.range 78).map fun k => (1 <<< k) ^^^ brMask a k ^^^ (if fbit a k then 1 <<< a else 0)

@[expose] def letterIdx (l : ℕ) : ℕ :=
  if l % 12 < 6 then 6 + l % 12 else 12 + 2 * (l % 12 - 6)

@[expose] def letterE (l : ℕ) : ℕ :=
  packE (rootCols (letterIdx l))

@[expose] def evalE (w : List ℕ) : ℕ :=
  w.foldl (fun acc l => mulE acc (letterE l)) oneE

theorem getD_rootCols (a : ℕ) (k : Fin 78) :
    (rootCols a).getD k 0 =
      (1 <<< (k : ℕ)) ^^^ brMask a k ^^^ (if fbit a k then 1 <<< a else 0) := by
  have hk : (k : ℕ) < 78 := k.2
  simp [rootCols, List.getD_eq_getElem?_getD, hk]

@[expose] def e6node (n : ℕ) (h : n < 6) : Fin Tag.E6.rank := ⟨n, by simpa [Tag.rank] using h⟩

theorem certRoot_neg_simple :
    ∀ i : Fin Tag.E6.rank, e6Certificate.root (6 + 2 * i) = -Pi.single i 1 := by
  decide

theorem twelve_add_lt (i : Fin Tag.E6.rank) : 12 + 2 * (i : ℕ) < 78 := by
  have := CFSG.Monster.B.E6.StdF4.val_lt_six i
  omega

theorem rootVec_neg_single {K : Type} [Field K]
    (i : Fin Tag.E6.rank) :
    rootVec Tag.E6 K (-Pi.single i 1) = Finsupp.single (lab ⟨12 + 2 * i, twelve_add_lt i⟩) 1 := by
  rw [rootVec_eq_single (isRoot_neg_single Tag.E6 i),
    lab_of_ge (by simp only [not_lt]; omega)]
  congr 3
  rw [show (12 + 2 * (i : ℕ)) - 6 = 6 + 2 * i by omega, certRoot_neg_simple]

section Letters

variable {K : Type} [Field K] [CharP K 2]

theorem repE_rootOp (a : Fin 78) :
    RepE (1 + (1 : K) • ad K (Finsupp.single (lab a) 1) +
      (1 : K) ^ 2 • formTensor K (Finsupp.single (lab a) 1)) (packE (rootCols a)) := by
  intro k
  rw [rootOp_apply, toVec_one_shiftLeft k, bracket_lab, form_lab, colE_packE, toVec_mod,
    getD_rootCols, toVec_xor, toVec_xor, toVec_one_shiftLeft k, one_smul, one_pow, one_smul]
  by_cases hf : fbit a k
  · simp [hf, toVec_one_shiftLeft a]
  · simp [hf, toVec_zero]

noncomputable def letterEnd (K : Type) [Field K] (l : ℕ) :
    Module.End K (RootModule Tag.E6 K) :=
  if h : l % 12 < 6 then xOp Tag.E6 K (e6node (l % 12) h) 1
  else yOp Tag.E6 K (e6node (l % 12 - 6) (by omega)) 1

theorem repE_letter (l : ℕ) : RepE (letterEnd K l) (letterE l) := by
  unfold letterEnd letterE
  split_ifs with h
  · rw [xOp_eq, CFSG.Monster.B.E6.StdF4.rootVec_single]
    have hi := repE_rootOp (K := K)
      ⟨6 + l % 12, CFSG.Monster.B.E6.StdF4.six_add_lt (e6node (l % 12) h)⟩
    simpa [letterIdx, h, e6node] using hi
  · rw [yOp_eq, rootVec_neg_single]
    have hi := repE_rootOp (K := K)
      ⟨12 + 2 * (l % 12 - 6), twelve_add_lt (e6node (l % 12 - 6) (by omega))⟩
    simpa [letterIdx, h, e6node] using hi

end Letters

section Group

variable (K : Type) [Field K]

noncomputable def letterElt (l : ℕ) :
    adjointGroup Tag.E6 K :=
  if h : l % 12 < 6 then ⟨xUnit Tag.E6 K (e6node (l % 12) h) 1, xUnit_mem_adjointGroup _ _⟩
  else ⟨yUnit Tag.E6 K (e6node (l % 12 - 6) (by omega)) 1, yUnit_mem_adjointGroup _ _⟩

noncomputable def evalG
    (w : List ℕ) : adjointGroup Tag.E6 K :=
  (w.map (letterElt K)).prod

variable {K}

@[expose] def HasBitsE (g : adjointGroup Tag.E6 K) (A : ℕ) : Prop :=
  RepE ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) A

theorem HasBitsE.mul [CharP K 2] {g h : adjointGroup Tag.E6 K}
    {A B : ℕ} (hg : HasBitsE g A) (hh : HasBitsE h B) : HasBitsE (g * h) (mulE A B) :=
  RepE.mul hg hh

theorem hasBitsE_one : HasBitsE (1 : adjointGroup Tag.E6 K) oneE :=
  repE_one

theorem HasBitsE.eq_iff [CharP K 2] {g h : adjointGroup Tag.E6 K}
    {A B : ℕ} (hg : HasBitsE g A) (hh : HasBitsE h B) : g = h ↔ A % 2 ^ 6084 = B % 2 ^ 6084 := by
  rw [← RepE.eq_iff hg hh, Subtype.ext_iff, Units.ext_iff]

theorem hasBitsE_letter [CharP K 2]
    (l : ℕ) : HasBitsE (letterElt K l) (letterE l) := by
  have := repE_letter (K := K) l
  unfold letterElt letterEnd at *
  split_ifs at this ⊢ with h
  · exact this
  · exact this

theorem hasBitsE_evalG [CharP K 2]
    (w : List ℕ) : HasBitsE (evalG K w) (evalE w) := by
  have key : ∀ (w : List ℕ) (acc : ℕ) (a : adjointGroup Tag.E6 K), HasBitsE a acc →
      HasBitsE (a * (w.map (letterElt K)).prod)
        (w.foldl (fun acc l => mulE acc (letterE l)) acc) := by
    intro w
    induction w with
    | nil => intro acc a h; simpa using h
    | cons l w ih =>
      intro acc a h
      rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
      exact ih _ _ (h.mul (hasBitsE_letter l))
  have := key w oneE 1 hasBitsE_one
  rwa [one_mul] at this

theorem letterElt_mul_self [CharP K 2]
    (l : ℕ) : letterElt K l * letterElt K l = 1 := by
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  unfold letterElt
  split_ifs with h
  · refine Subtype.ext (Units.ext ?_)
    have := (xUnit Tag.E6 K (e6node (l % 12) h) 1).val_inv
    simp only [xUnit, hneg] at this
    exact this
  · refine Subtype.ext (Units.ext ?_)
    have := (yUnit Tag.E6 K (e6node (l % 12 - 6) (by omega)) 1).val_inv
    simp only [yUnit, hneg] at this
    exact this

theorem evalG_inv [CharP K 2] :
    ∀ w : List ℕ, (evalG K w)⁻¹ = evalG K w.reverse
  | [] => by simp [evalG]
  | l :: w => by
    have hl : (letterElt K l)⁻¹ = letterElt K l :=
      inv_eq_of_mul_eq_one_right (letterElt_mul_self l)
    have ih := evalG_inv w
    unfold evalG at ih ⊢
    rw [List.map_cons, List.prod_cons, mul_inv_rev, ih, hl, List.reverse_cons, List.map_append,
      List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem evalG_nil :
    evalG K [] = 1 := by
  simp [evalG]

theorem evalG_append
    (w w' : List ℕ) : evalG K (w ++ w') = evalG K w * evalG K w' := by
  simp [evalG]

end Group

end CFSG.AGLEmbedding.E6Two
