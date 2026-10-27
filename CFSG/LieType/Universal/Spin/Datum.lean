module

public import CFSG.LieType.Universal.Spin.Chevalley.Odd
public import CFSG.LieType.Universal.RootData
public import CFSG.LieType.Universal.Spin.Roots.TypeB
public import CFSG.LieType.Universal.Spin.Roots.TypeD

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

@[expose] def boolSign (s : Bool) : ℤ := if s then 1 else -1

@[simp] theorem boolSign_true : boolSign true = 1 := rfl

@[simp] theorem boolSign_false : boolSign false = -1 := rfl

theorem boolSign_ne_zero (s : Bool) : boolSign s ≠ 0 := by cases s <;> decide

theorem boolSign_injective : Function.Injective boolSign := by
  intro s t h
  cases s <;> cases t <;> simp_all [boolSign]

theorem boolSign_eq_one_or_eq_neg_one (s : Bool) : boolSign s = 1 ∨ boolSign s = -1 := by
  cases s <;> simp

@[simp] theorem boolSign_not (s : Bool) : boolSign (!s) = -boolSign s := by cases s <;> simp

theorem exists_boolSign_eq {s : ℤ} (hs : s = 1 ∨ s = -1) : ∃ b : Bool, boolSign b = s := by
  rcases hs with rfl | rfl
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

section Single

variable {n : ℕ}

theorem single_add_single_eq_iff {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j')
    {a b a' b' : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Pi.single i a + Pi.single j b : Fin n → ℤ) = Pi.single i' a' + Pi.single j' b' ↔
      (i = i' ∧ a = a' ∧ j = j' ∧ b = b') ∨ (i = j' ∧ a = b' ∧ j = i' ∧ b = a') := by
  have hji := hij.symm
  have hji' := hij'.symm
  constructor
  · intro h
    have hi := congrFun h i
    have hj := congrFun h j
    clear h
    simp only [Pi.add_apply, Pi.single_apply] at hi hj
    by_cases h1 : i = i'
    · subst h1
      by_cases h4 : j = j'
      · subst h4
        left
        refine ⟨rfl, ?_, rfl, ?_⟩ <;> simp_all
      · exfalso
        simp_all
    · by_cases h2 : i = j'
      · subst h2
        by_cases h3 : j = i'
        · subst h3
          right
          refine ⟨rfl, ?_, rfl, ?_⟩ <;> simp_all
        · exfalso
          simp_all
      · exfalso
        simp_all
  · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
    · rfl
    · exact add_comm (Pi.single i a : Fin n → ℤ) (Pi.single j b)

theorem single_ne_single_add_single {i i' j' : Fin n} (hij' : i' ≠ j') {a a' b' : ℤ}
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) :
    (Pi.single i a : Fin n → ℤ) ≠ Pi.single i' a' + Pi.single j' b' := by
  have hji' := hij'.symm
  intro h
  have h1 := congrFun h i'
  have h2 := congrFun h j'
  clear h
  simp only [Pi.add_apply, Pi.single_apply] at h1 h2
  by_cases hi : i' = i
  · subst hi
    simp_all
  · by_cases hj : j' = i
    · subst hj
      simp_all
    · simp_all

theorem single_eq_single_iff' {i i' : Fin n} {a a' : ℤ} (ha : a ≠ 0) :
    (Pi.single i a : Fin n → ℤ) = Pi.single i' a' ↔ i = i' ∧ a = a' := by
  constructor
  · intro h
    have hi := congrFun h i
    rw [Pi.single_eq_same] at hi
    by_cases hii' : i = i'
    · subst hii'
      rw [Pi.single_eq_same] at hi
      exact ⟨rfl, hi⟩
    · rw [Pi.single_apply, ite_eq_right hii'] at hi
      exact absurd hi ha
  · rintro ⟨rfl, rfl⟩
    rfl

end Single

section Frame

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

theorem HypFrame.range_longRoot_swap (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    (F.longRoot hij.symm t s).range = (F.longRoot hij s t).range := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd (-(Multiplicative.toAdd c)), by
      rw [F.longRoot_swap hij s t, neg_neg]
      rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd (-(Multiplicative.toAdd c)), by
      rw [F.longRoot_swap hij.symm t s, neg_neg]
      rfl⟩

@[expose] noncomputable def HypFrame.longRootGroup (F : HypFrame Q n) (v : Fin n → ℤ) :
    Subgroup (spinGroup Q) :=
  ⨆ (i : Fin n) (j : Fin n) (hij : i ≠ j) (s : Bool) (t : Bool)
    (_ : v = Pi.single i (boolSign s) + Pi.single j (boolSign t)), (F.longRoot hij s t).range

theorem HypFrame.longRootGroup_eq (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    F.longRootGroup (Pi.single i (boolSign s) + Pi.single j (boolSign t)) =
      (F.longRoot hij s t).range := by
  refine le_antisymm (iSup_le fun i' => iSup_le fun j' => iSup_le fun hij' => iSup_le fun s' =>
    iSup_le fun t' => iSup_le fun h => ?_) ?_
  · rcases (single_add_single_eq_iff hij hij' (boolSign_ne_zero s) (boolSign_ne_zero t)).mp h with
      ⟨rfl, hs, rfl, ht⟩ | ⟨rfl, hs, rfl, ht⟩
    · obtain rfl := boolSign_injective hs
      obtain rfl := boolSign_injective ht
      exact le_rfl
    · obtain rfl := boolSign_injective hs
      obtain rfl := boolSign_injective ht
      exact (F.range_longRoot_swap hij s t).le
  · exact le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le hij (le_iSup_of_le s
      (le_iSup_of_le t (le_iSup_of_le rfl le_rfl)))))

theorem HypFrame.longRootGroup_single (F : HypFrame Q n) (i : Fin n) {a : ℤ} :
    F.longRootGroup (Pi.single i a) = ⊥ := by
  refine eq_bot_iff.mpr (iSup_le fun i' => iSup_le fun j' => iSup_le fun hij' => iSup_le fun s' =>
    iSup_le fun t' => iSup_le fun h => ?_)
  exact absurd h (single_ne_single_add_single hij' (boolSign_ne_zero s') (boolSign_ne_zero t'))

@[expose] noncomputable def OddFrame.shortRootGroup (F : OddFrame Q n) (v : Fin n → ℤ) :
    Subgroup (spinGroup Q) :=
  ⨆ (i : Fin n) (s : Bool) (_ : v = Pi.single i (boolSign s)), (F.shortRoot i s).range

theorem OddFrame.shortRootGroup_eq (F : OddFrame Q n) (i : Fin n) (s : Bool) :
    F.shortRootGroup (Pi.single i (boolSign s)) = (F.shortRoot i s).range := by
  refine le_antisymm (iSup_le fun i' => iSup_le fun s' => iSup_le fun h => ?_) ?_
  · obtain ⟨rfl, hs⟩ := (single_eq_single_iff' (boolSign_ne_zero s)).mp h
    obtain rfl := boolSign_injective hs
    exact le_rfl
  · exact le_iSup_of_le i (le_iSup_of_le s (le_iSup_of_le rfl le_rfl))

theorem OddFrame.shortRootGroup_add (F : OddFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    F.shortRootGroup (Pi.single i (boolSign s) + Pi.single j (boolSign t)) = ⊥ := by
  refine eq_bot_iff.mpr (iSup_le fun i' => iSup_le fun s' => iSup_le fun h => ?_)
  exact absurd h.symm (single_ne_single_add_single hij (boolSign_ne_zero s) (boolSign_ne_zero t))

end Frame

section Plus

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def plusRootGroup (hn : 3 ≤ n) (γ : Fin n → ℤ) :
    Subgroup (spinGroup (quadPlus n K)) :=
  (plusFrame n K hn).longRootGroup (toStdD n γ)

@[expose] noncomputable def plusDatum (hn : 3 ≤ n) :
    UniversalRootDatum (spinGroup (quadPlus n K)) where
  rank := n
  cartan := cartanD n
  isFiniteType := isFiniteType_cartanD n
  divisible := ∅
  rootGroup := plusRootGroup n K hn

variable {n K}

theorem plusRootGroup_eq (hn : 3 ≤ n) {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (h : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    plusRootGroup n K hn γ = ((plusFrame n K hn).longRoot hij s t).range := by
  rw [plusRootGroup, h, HypFrame.longRootGroup_eq]

theorem plusDatum_roots (hn : 3 ≤ n) :
    (plusDatum n K hn).roots = RootSystem.roots (isFiniteType_cartanD n) ∅ :=
  rfl

theorem exists_plusRootGroup_eq (hn : 3 ≤ n) {γ : Fin n → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanD n) ∅) :
    ∃ (i j : Fin n) (hij : i ≠ j) (s t : Bool),
      toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) ∧
        plusRootGroup n K hn γ = ((plusFrame n K hn).longRoot hij s t).range := by
  rw [rootsD_eq n (by omega)] at hγ
  obtain ⟨i, j, s, t, hij, hs, ht, h⟩ := hγ
  obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
  obtain ⟨t', rfl⟩ := exists_boolSign_eq ht
  exact ⟨i, j, hij, s', t', h, plusRootGroup_eq hn hij s' t' h⟩


theorem toStdD_single_eq (hn : 2 ≤ n) (k : Fin n) :
    toStdD n (Pi.single k 1) = Pi.single (rootIdxD n k) (boolSign true) +
      Pi.single (rootIdxD' n k) (boolSign (rootSignD n k)) := by
  by_cases h : k.val + 1 < n
  · rw [toStdD_single_of_lt n h, rootIdxD_of_lt n h, rootIdxD'_of_lt n h, rootSignD_of_lt n h,
      boolSign_true, boolSign_false, Pi.single_neg, sub_eq_add_neg]
  · have h1 : rootIdxD n k = ⟨n - 2, by omega⟩ := Fin.ext (val_rootIdxD_of_not_lt n h)
    have h2 : rootIdxD' n k = k := Fin.ext (by rw [val_rootIdxD'_of_not_lt n h]; omega)
    rw [toStdD_single_of_not_lt n h hn, h1, h2, rootSignD_of_not_lt n h, boolSign_true]

theorem plusRootGroup_single (hn : 3 ≤ n) (k : Fin n) :
    plusRootGroup n K hn (Pi.single k 1) = (rootD K hn k).range :=
  plusRootGroup_eq hn (rootIdxD_ne n (by omega) k) true (rootSignD n k)
    (toStdD_single_eq (by omega) k)

theorem plusRootGroup_neg_single (hn : 3 ≤ n) (k : Fin n) :
    plusRootGroup n K hn (-Pi.single k 1) = (negRootD K hn k).range := by
  refine plusRootGroup_eq hn (rootIdxD_ne n (by omega) k).symm (!rootSignD n k) false ?_
  rw [toStdD_neg, toStdD_single_eq (by omega) k, boolSign_not, boolSign_false, boolSign_true,
    neg_add, ← Pi.single_neg, ← Pi.single_neg, add_comm]

end Plus

section Odd

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def oddRootGroup (γ : Fin n → ℤ) : Subgroup (spinGroup (quadOdd n K)) :=
  (oddFrame n K).longRootGroup (toStdB n γ) ⊔ (oddFrame n K).shortRootGroup (toStdB n γ)

@[expose] noncomputable def oddDatum : UniversalRootDatum (spinGroup (quadOdd n K)) where
  rank := n
  cartan := cartanB n
  isFiniteType := isFiniteType_cartanB n
  divisible := ∅
  rootGroup := oddRootGroup n K

variable {n K}

theorem oddRootGroup_eq_long {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (h : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    oddRootGroup n K γ = ((oddFrame n K).longRoot hij s t).range := by
  rw [oddRootGroup, h, HypFrame.longRootGroup_eq, OddFrame.shortRootGroup_add _ hij, sup_bot_eq]

theorem oddRootGroup_eq_short {γ : Fin n → ℤ} (i : Fin n) (s : Bool)
    (h : toStdB n γ = Pi.single i (boolSign s)) :
    oddRootGroup n K γ = ((oddFrame n K).shortRoot i s).range := by
  rw [oddRootGroup, h, HypFrame.longRootGroup_single, OddFrame.shortRootGroup_eq, bot_sup_eq]

theorem oddDatum_roots : (oddDatum n K).roots = RootSystem.roots (isFiniteType_cartanB n) ∅ :=
  rfl


theorem oddRootGroup_single (k : Fin n) : oddRootGroup n K (Pi.single k 1) = (rootB K k).range := by
  by_cases h : k.val + 1 < n
  · have hkj : k ≠ ⟨k.val + 1, h⟩ := Fin.ne_of_val_ne (by simp)
    rw [rootB_of_lt K h rfl hkj]
    refine oddRootGroup_eq_long hkj true false ?_
    rw [toStdB_single_of_lt n h, boolSign_true, boolSign_false, Pi.single_neg, sub_eq_add_neg]
  · rw [rootB_of_not_lt K h]
    exact oddRootGroup_eq_short k true (by rw [toStdB_single_of_not_lt n h, boolSign_true])

theorem oddRootGroup_neg_single (k : Fin n) :
    oddRootGroup n K (-Pi.single k 1) = (negRootB K k).range := by
  by_cases h : k.val + 1 < n
  · have hkj : (⟨k.val + 1, h⟩ : Fin n) ≠ k := Fin.ne_of_val_ne (by simp)
    rw [negRootB_of_lt K h rfl hkj]
    refine oddRootGroup_eq_long hkj true false ?_
    rw [toStdB_neg, toStdB_single_of_lt n h, boolSign_true, boolSign_false, neg_sub,
      Pi.single_neg, sub_eq_add_neg]
  · rw [oddRootGroup_eq_short k false (by
      rw [toStdB_neg, toStdB_single_of_not_lt n h, boolSign_false, Pi.single_neg])]
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Multiplicative.ofAdd (-(Multiplicative.toAdd c)), by
        rw [negRootB_of_not_lt K h, neg_neg]
        rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨Multiplicative.ofAdd (-(Multiplicative.toAdd c)),
        (negRootB_of_not_lt K h (Multiplicative.toAdd c)).symm⟩

end Odd

end CFSG.LieType.Universal.Spin
