
module

public import Certificates.Data.Kernel.IdxFourChainK
public import CFSG.GF2Type.Smith1979.GammaU.Bits
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KC.IF4C

open CFSG.GF2Type.Smith1979.GammaU

theorem nthD_eq {α : Type} (d : α) (l : List α) (k : Nat) : nthD d l k = l.getD k d := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => cases k with
    | zero => rfl
    | succ k => exact ih k

theorem dropN_eq {α : Type} (k : Nat) (l : List α) : dropN k l = l.drop k := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => cases l with
    | nil => rfl
    | cons a l => exact ih l

theorem takeN_eq {α : Type} (k : Nat) (l : List α) : takeN k l = l.take k := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih => cases l with
    | nil => rfl
    | cons a l => exact congrArg (a :: ·) (ih l)

theorem lenN_eq {α : Type} (l : List α) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg Nat.succ ih

theorem memN_iff (k : Nat) (l : List Nat) : memN k l = true ↔ k ∈ l := by
  induction l with
  | nil => simp [memN]
  | cons a l ih =>
    change (Nat.beq a k || memN k l) = true ↔ _
    rw [Bool.or_eq_true, ih, Nat.beq_eq, List.mem_cons]
    exact ⟨fun h => h.elim (fun h => Or.inl h.symm) Or.inr,
      fun h => h.elim (fun h => Or.inl h.symm) Or.inr⟩

theorem allBelow_iff (n : Nat) (f : Nat → Bool) : allBelow n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    change (f n && allBelow n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
      · exact h2 k h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

@[expose] noncomputable def rowsP (m : Nat) : Array ℕ := ((List.range 12).map (fld m)).toArray

@[expose] noncomputable def linP (m : Nat) : V12 →ₗ[ZMod 2] V12 := linOfRows (rowsP m)

theorem rowsP_get (m : Nat) (j : Fin 12) : (rowsP m)[(j : ℕ)]! = fld m j := by
  simp [rowsP, getElem!_pos, j.2]

theorem linP_eq_of_rowsP {m : Nat} {r : Array ℕ} (h : rowsP m = r) (v : V12) :
    linP m v = linOfRows r v := by
  rw [linP, h]

theorem linP_apply (m : Nat) (v : V12) : linP m v = ∑ j : Fin 12, v j • vecOf (fld m j) := by
  simp only [linP, linOfRows_apply, rowsP_get]

@[expose] noncomputable def ap12k (k m x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih m x => Nat.xor (bif Nat.beq (Nat.land x 1) 1 then Nat.land m 4095 else 0)
      (ih (Nat.shiftRight m 12) (Nat.shiftRight x 1))) k m x

theorem fld_shiftRight (m j : Nat) : fld (m >>> 12) j = fld m (j + 1) := by
  change ((m >>> 12) >>> (12 * j)) &&& 4095 = (m >>> (12 * (j + 1))) &&& 4095
  have h : 12 * (j + 1) = 12 + 12 * j := by ring
  rw [← Nat.shiftRight_add, h]

theorem vecOf_bif (x a : Nat) :
    vecOf (bif Nat.beq (Nat.land x 1) 1 then a else 0) =
      (if x.testBit 0 then (1 : ZMod 2) else 0) • vecOf a := by
  have : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
  rw [this, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem vecOf_ap12k (k m x : Nat) :
    vecOf (ap12k k m x) =
      ∑ j ∈ Finset.range k, (if x.testBit j then (1 : ZMod 2) else 0) • vecOf (fld m j) := by
  induction k generalizing m x with
  | zero => simp [ap12k]
  | succ k ih =>
    change vecOf ((bif Nat.beq (Nat.land x 1) 1 then Nat.land m 4095 else 0) ^^^
      ap12k k (m >>> 12) (x >>> 1)) = _
    rw [vecOf_xor, vecOf_bif, ih, Finset.sum_range_succ', add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.testBit_shiftRight, fld_shiftRight, Nat.add_comm 1 j]

theorem vecOf_ap12 (m x : Nat) : vecOf (ap12 m x) = linP m (vecOf x) := by
  have h : ap12 m x = ap12k 12 m x := rfl
  rw [h, vecOf_ap12k, linP_apply,
    Finset.sum_range (fun j => (if x.testBit j then (1 : ZMod 2) else 0) • vecOf (fld m j))]
  rfl

theorem ap12k_lt (k m x : Nat) : ap12k k m x < 4096 := by
  induction k generalizing m x with
  | zero => simp [ap12k]
  | succ k ih =>
    change (bif Nat.beq (Nat.land x 1) 1 then Nat.land m 4095 else 0) ^^^
      ap12k k (m >>> 12) (x >>> 1) < 2 ^ 12
    refine Nat.xor_lt_two_pow ?_ (ih _ _)
    cases Nat.beq (Nat.land x 1) 1
    · simp
    · exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by norm_num)

theorem ap12_lt (m x : Nat) : ap12 m x < 4096 := ap12k_lt 12 m x

@[expose] noncomputable def mulPk (k g h : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih h => Nat.lor (ap12 g (Nat.land h 4095)) (Nat.shiftLeft (ih (Nat.shiftRight h 12)) 12))
    k h

theorem or_shiftLeft_land {a : Nat} (ha : a < 2 ^ 12) (X : Nat) :
    (a ||| X <<< 12) &&& 4095 = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h4095 : (4095 : Nat) = 2 ^ 12 - 1 := rfl
  rw [h4095, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 12
  · simp [hi]
  · simp [hi, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega)
      (Nat.le_of_not_lt hi)))]

theorem or_shiftLeft_shiftRight {a : Nat} (ha : a < 2 ^ 12) (X : Nat) :
    (a ||| X <<< 12) >>> 12 = X := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega)
      (by omega : 12 ≤ 12 + i)))]
  simp

theorem fld_mulPk (k g h : Nat) : ∀ j < k, fld (mulPk k g h) j = ap12 g (fld h j) := by
  induction k generalizing h with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    change fld (ap12 g (h &&& 4095) ||| mulPk k g (h >>> 12) <<< 12) j = _
    cases j with
    | zero =>
      change ((ap12 g (h &&& 4095) ||| mulPk k g (h >>> 12) <<< 12) >>> 0) &&& 4095 =
        ap12 g ((h >>> 0) &&& 4095)
      rw [Nat.shiftRight_zero, Nat.shiftRight_zero, or_shiftLeft_land (ap12_lt _ _)]
    | succ j =>
      rw [← fld_shiftRight, ← fld_shiftRight h, or_shiftLeft_shiftRight (ap12_lt _ _)]
      exact ih (h >>> 12) j (by omega)

theorem fld_mulP (g h : Nat) (j : Fin 12) : fld (mulP g h) j = ap12 g (fld h j) :=
  fld_mulPk 12 g h j j.2

theorem linP_mulP (g h : Nat) (v : V12) : linP (mulP g h) v = linP g (linP h v) := by
  calc linP (mulP g h) v = ∑ j : Fin 12, linP g (v j • vecOf (fld h j)) := by
        rw [linP_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [fld_mulP, vecOf_ap12, map_smul]
    _ = linP g (linP h v) := by rw [← map_sum, ← linP_apply]

theorem vecOf_fld_idP (j : Fin 12) : vecOf (fld idP j) = Pi.single j 1 := by
  revert j
  decide +kernel

theorem linP_idP (v : V12) : linP idP v = v := by
  rw [linP_apply]
  simp only [vecOf_fld_idP]
  conv_rhs => rw [← Finset.univ_sum_single v]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

@[expose] def IsP (U : V12 ≃ₗ[ZMod 2] V12) (m : Nat) : Prop := ∀ v, U v = linP m v

theorem IsP.mul {U V : V12 ≃ₗ[ZMod 2] V12} {g h : Nat} (hU : IsP U g) (hV : IsP V h) :
    IsP (U * V) (mulP g h) := fun v => by
  rw [LinearEquiv.mul_apply, hV, hU, linP_mulP]

theorem IsP.one : IsP 1 idP := fun v => (linP_idP v).symm

theorem IsP.inj {U V : V12 ≃ₗ[ZMod 2] V12} {m : Nat} (hU : IsP U m) (hV : IsP V m) : U = V :=
  LinearEquiv.ext fun v => (hU v).trans (hV v).symm

theorem IsP.inv {U : V12 ≃ₗ[ZMod 2] V12} {g h : Nat} (hU : IsP U g) (hgh : mulP g h = idP) :
    IsP U⁻¹ h := fun v => by
  have h1 : U (linP h v) = v := by rw [hU, ← linP_mulP, hgh, linP_idP]
  calc U⁻¹ v = U⁻¹ (U (linP h v)) := by rw [h1]
    _ = (U⁻¹ * U) (linP h v) := rfl
    _ = linP h v := by rw [inv_mul_cancel]; rfl

theorem IsP.apply_code {U : V12 ≃ₗ[ZMod 2] V12} {m : Nat} (hU : IsP U m) (x : Nat) :
    U (vecOf x) = vecOf (ap12 m x) := by
  rw [hU, vecOf_ap12]

theorem IsP.exists_of_mul {g h : Nat} (hgh : mulP g h = idP) : ∃ U, IsP U g := by
  have hs : Function.Surjective (linP g) := fun v =>
    ⟨linP h v, by rw [← linP_mulP, hgh, linP_idP]⟩
  have hi : Function.Injective (linP g) := LinearMap.injective_iff_surjective.mpr hs
  exact ⟨LinearEquiv.ofBijective (linP g) ⟨hi, hs⟩, fun v => rfl⟩

theorem mem_of_closure {G : Type*} [Group G] [Finite G] {S : Set G} {K : Set G} (h1 : (1 : G) ∈ K)
    (hmul : ∀ s ∈ S, ∀ y ∈ K, s * y ∈ K) {x : G} (hx : x ∈ Subgroup.closure S) : x ∈ K := by
  have hpow : ∀ s ∈ S, ∀ m : ℕ, ∀ y ∈ K, s ^ m * y ∈ K := by
    intro s hs m
    induction m with
    | zero => intro y hy; rwa [pow_zero, one_mul]
    | succ m ih => intro y hy; rw [pow_succ', mul_assoc]; exact hmul s hs _ (ih y hy)
  induction hx using Subgroup.closure_induction_left with
  | one => exact h1
  | mul_left s hs y _ ih => exact hmul s hs y ih
  | inv_mul_cancel s hs y _ ih =>
    have hinv : s⁻¹ = s ^ (orderOf s - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos s),
        pow_orderOf_eq_one]
    rw [hinv]
    exact hpow s hs _ y ih

section Chain

variable (SP SI : Nat) (T O PS B : List Nat) (TL WD : List (List Nat))
  (TR R : List (List (List Nat)))

@[expose] def lvlGrp (i : Nat) : Subgroup (V12 ≃ₗ[ZMod 2] V12) :=
  Subgroup.closure {U | ∃ g ∈ TL.getD i [], IsP U (look SP g)}

structure TreeHyp (k j0 n : Nat) : Prop where
  lenO : O.length = k
  tl0 : TL.getD 0 [] = List.range j0
  tlk : TL.getD k [] = []
  tl : ∀ i, 1 ≤ i → i < k → tlOK SP B TL n i = true
  inv : invOK SP SI n = true
  words : wordsOK SP SI n WD j0 = true
  tree : ∀ i < k, treeOK SP T O TL TR i = true
  pos : ∀ i < k, posOK T O PS B i = true

structure ChainHyp (k j0 n : Nat) : Prop extends TreeHyp SP SI T O PS B TL WD TR k j0 n where
  lenT : T.length = k
  cnt : ∀ i < k, cntOK O TL R i = true
  blk : ∀ i < k, ∀ c, 32 * c < (R.getD i []).length → blkOK SP T O TL R i c = true

theorem recOK_spec {i r : Nat} {rec : List Nat} (h : recOK SP T O TL i r rec = true) :
    ∃ y as, rec = y :: as ∧ y < O.getD i 0 ∧ pathOK (O.drop (i + 1)) as = true ∧
      mulP (look SP ((TL.getD i []).getD (r % (TL.getD i []).length) 0))
        (look (T.getD i 0) (r / (TL.getD i []).length)) =
        mulP (look (T.getD i 0) y) (pathP (T.drop (i + 1)) as) := by
  cases rec with
  | nil => exact absurd (h : false = true) Bool.false_ne_true
  | cons y as =>
    change (Nat.blt y (nthD 0 O i) && pathOK (dropN (Nat.succ i) O) as &&
      Nat.beq
        (mulP (look SP (nthD 0 (nthD [] TL i) (Nat.mod r (lenN (nthD [] TL i)))))
          (look (nthD 0 T i) (Nat.div r (lenN (nthD [] TL i)))))
        (mulP (look (nthD 0 T i) y) (pathP (dropN (Nat.succ i) T) as))) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, nthD_eq, dropN_eq, lenN_eq] at h
    exact ⟨y, as, rfl, h.1.1, h.1.2, h.2⟩

theorem recsOK_spec {i : Nat} : ∀ {rs : List (List Nat)} {r0 : Nat},
    recsOK SP T O TL i rs r0 = true →
      ∀ j < rs.length, recOK SP T O TL i (r0 + j) (rs.getD j []) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | rec :: rs, r0, h, j, hj => by
    change (recOK SP T O TL i r0 rec && recsOK SP T O TL i rs (Nat.succ r0)) = true at h
    rw [Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      have := recsOK_spec h.2 j (by simpa using hj)
      rwa [Nat.succ_add, ← Nat.add_succ] at this

theorem treeRecs_spec {i : Nat} : ∀ {es : List (List Nat)} {x0 : Nat},
    treeRecs SP T TL i es x0 = true → ∀ p < es.length,
      (es.getD p []).getD 0 0 < x0 + p ∧ (es.getD p []).getD 1 0 ∈ TL.getD i [] ∧
        mulP (look SP ((es.getD p []).getD 1 0)) (look (T.getD i 0) ((es.getD p []).getD 0 0)) =
          look (T.getD i 0) (x0 + p)
  | [], _, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | e :: es, x0, h, p, hp => by
    change (Nat.blt (nthD 0 e 0) x0 && memN (nthD 0 e 1) (nthD [] TL i) &&
      Nat.beq (mulP (look SP (nthD 0 e 1)) (look (nthD 0 T i) (nthD 0 e 0)))
        (look (nthD 0 T i) x0) && treeRecs SP T TL i es (Nat.succ x0)) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, nthD_eq, memN_iff] at h
    cases p with
    | zero => exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
    | succ p =>
      have := treeRecs_spec h.2 p (by simpa using hp)
      have hx : x0 + (p + 1) = Nat.succ x0 + p := by omega
      rw [hx]
      simpa only [List.getD_cons_succ] using this

theorem treeOK_spec {i : Nat} (h : treeOK SP T O TL TR i = true) :
    look (T.getD i 0) 0 = idP ∧ (TR.getD i []).length + 1 = O.getD i 0 ∧
      treeRecs SP T TL i (TR.getD i []) 1 = true := by
  change (Nat.beq (look (nthD 0 T i) 0) idP && Nat.beq (Nat.succ (lenN (nthD [] TR i)))
    (nthD 0 O i) && treeRecs SP T TL i (nthD [] TR i) 1) = true at h
  simp only [Bool.and_eq_true, Nat.beq_eq, nthD_eq, lenN_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem posOK_spec {i : Nat} (h : posOK T O PS B i = true) :
    ∀ x < O.getD i 0, fld (PS.getD i 0) (ap12 (look (T.getD i 0) x) (B.getD i 0)) = x := by
  unfold posOK at h
  rw [allBelow_iff] at h
  intro x hx
  have := h x (by rwa [nthD_eq])
  simpa only [Nat.beq_eq, nthD_eq] using this

theorem mem_fixL {n i g : Nat} :
    g ∈ fixL SP B n i ↔ g < n ∧ ∀ q < i, ap12 (look SP g) (B.getD q 0) = B.getD q 0 := by
  simp [fixL, List.mem_filter, List.all_eq_true, List.mem_range]

theorem tlOK_spec {n i : Nat} (h : tlOK SP B TL n i = true) : TL.getD i [] = fixL SP B n i := by
  unfold tlOK at h
  simpa using h

theorem invOK_spec {n : Nat} (h : invOK SP SI n = true) :
    ∀ l < n, mulP (look SP l) (look SI l) = idP := by
  unfold invOK at h
  rw [allBelow_iff] at h
  intro l hl
  simpa only [Nat.beq_eq] using h l hl

theorem wordsOK_spec {n j0 : Nat} (h : wordsOK SP SI n WD j0 = true) :
    j0 + WD.length = n ∧ ∀ p < WD.length, look SP (j0 + p) = wordP SP SI (WD.getD p []) ∧
      ∀ e ∈ WD.getD p [], e / 2 < j0 + p := by
  have key : ∀ (W : List (List Nat)) (j : Nat),
      List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun w _ ih j => Nat.beq (look SP j) (wordP SP SI w) &&
          w.all (fun e => Nat.blt (e / 2) j) && ih (Nat.succ j)) W j = true →
      ∀ p < W.length, look SP (j + p) = wordP SP SI (W.getD p []) ∧
        ∀ e ∈ W.getD p [], e / 2 < j + p := by
    intro W
    induction W with
    | nil => intro j _ p hp; exact absurd hp (Nat.not_lt_zero p)
    | cons w W ih =>
      intro j hj p hp
      change (Nat.beq (look SP j) (wordP SP SI w) && w.all (fun e => Nat.blt (e / 2) j) &&
        List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
          (fun w _ ih j => Nat.beq (look SP j) (wordP SP SI w) &&
            w.all (fun e => Nat.blt (e / 2) j) && ih (Nat.succ j)) W (Nat.succ j)) = true at hj
      simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at hj
      cases p with
      | zero => exact ⟨hj.1.1, hj.1.2⟩
      | succ p =>
        have := ih (Nat.succ j) hj.2 p (by simpa using hp)
        have hx : j + (p + 1) = Nat.succ j + p := by omega
        rw [hx]
        simpa only [List.getD_cons_succ] using this
  unfold wordsOK at h
  rw [Bool.and_eq_true, Nat.beq_eq, lenN_eq] at h
  exact ⟨h.1, key WD j0 h.2⟩

end Chain

end CFSG.KC.IF4C

end
