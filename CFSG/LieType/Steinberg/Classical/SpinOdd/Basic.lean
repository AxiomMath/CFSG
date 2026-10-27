module

public import CFSG.LieType.Steinberg.Classical.SpinOdd.Frame
public import CFSG.LieType.Steinberg.OfCartan
public import CFSG.LieType.Steinberg.Statement

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinOdd

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem

variable (n : ℕ) (K : Type) [Field K]

@[expose] def x (γ : Fin n → ℤ) (c : K) : spinGroup (quadOdd n K) :=
  elt (oddFrame n K) (toStdB n γ) c

abbrev Φ : RootSystem (Fin n) :=
  RootSystem.ofCartan (oddDatum n K).isFiniteType (oddDatum n K).divisible

variable {n K}

theorem Φ_roots : (Φ n K).roots = roots (isFiniteType_cartanB n) ∅ := rfl

theorem mem_roots_iff {γ : Fin n → ℤ} :
    γ ∈ roots (isFiniteType_cartanB n) ∅ ↔ IsRootVec (toStdB n γ) := by
  rw [rootsB_eq, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨i, j, s, t, hij, hs, ht, h⟩ | ⟨i, s, hs, h⟩)
    · obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
      obtain ⟨t', rfl⟩ := exists_boolSign_eq ht
      exact Or.inl ⟨i, j, hij, s', t', h⟩
    · obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
      exact Or.inr ⟨i, s', h⟩
  · rintro (⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩)
    · exact Or.inl ⟨i, j, boolSign s, boolSign t, hij, boolSign_eq_one_or_eq_neg_one s,
        boolSign_eq_one_or_eq_neg_one t, h⟩
    · exact Or.inr ⟨i, boolSign s, boolSign_eq_one_or_eq_neg_one s, h⟩

theorem x_eq_long {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) {s t : Bool}
    (h : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (c : K) :
    x n K γ c = (oddFrame n K).longRoot hij s t (.ofAdd ((repSign i j s t : K) * c)) := by
  rw [x, elt_of_isLong _ (h ▸ isLong_single_add_single hij s t), rootElt_eq _ hij h]

theorem x_eq_short {γ : Fin n → ℤ} {i : Fin n} {s : Bool}
    (h : toStdB n γ = Pi.single i (boolSign s)) (c : K) :
    x n K γ c = (oddFrame n K).shortRoot i s (.ofAdd ((boolSign s : K) * c)) := by
  rw [x, elt_of_isShort _ (h ▸ isShort_single i s), shortElt_eq _ h]

theorem isParametrization :
    IsParametrization (Φ := Φ n K) (oddDatum n K).rootGroup (x n K) := by
  intro γ hγ
  have hγ' := mem_roots_iff.mp hγ
  refine ⟨fun g => ?_, fun c d => elt_add _ _ c d, elt_injective _ hγ'⟩
  change g ∈ oddRootGroup n K γ ↔ _
  rcases hγ' with ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · rw [oddRootGroup_eq_long hij s t h, exists_rootElt_eq_iff _ hij h]
    simp only [x, elt_of_isLong _ (h ▸ isLong_single_add_single hij s t)]
  · rw [oddRootGroup_eq_short i s h, exists_shortElt_eq_iff _ h]
    simp only [x, elt_of_isShort _ (h ▸ isShort_single i s)]

theorem x_mem {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅) (c : K) :
    x n K γ c ∈ oddRootGroup n K γ :=
  ((isParametrization (n := n) (K := K) γ hγ).1 _).2 ⟨c, rfl⟩

theorem x_single (k : Fin n) (c : K) : x n K (Pi.single k 1) c = rootB K k (.ofAdd c) := by
  by_cases h : k.val + 1 < n
  · have hkj : k ≠ ⟨k.val + 1, h⟩ := Fin.ne_of_val_ne (by simp)
    rw [rootB_of_lt K h rfl hkj, x_eq_long hkj (s := true) (t := false) (by
      rw [toStdB_single_of_lt n h, boolSign_true, boolSign_false, Pi.single_neg, sub_eq_add_neg]),
      repSign_of_lt (Fin.lt_def.mpr (by simp)), boolSign_true, Int.cast_one, one_mul]
  · rw [rootB_of_not_lt K h, x_eq_short (s := true) (by
      rw [toStdB_single_of_not_lt n h, boolSign_true]), boolSign_true, Int.cast_one, one_mul]

theorem x_neg_single (k : Fin n) (c : K) :
    x n K (-Pi.single k 1) c = negRootB K k (.ofAdd c) := by
  by_cases h : k.val + 1 < n
  · have hkj : (⟨k.val + 1, h⟩ : Fin n) ≠ k := Fin.ne_of_val_ne (by simp)
    rw [negRootB_of_lt K h rfl hkj, x_eq_long hkj (s := true) (t := false) (by
      rw [toStdB_neg, toStdB_single_of_lt n h, boolSign_true, boolSign_false, neg_sub,
        Pi.single_neg, sub_eq_add_neg]),
      repSign_of_not_lt (by rw [Fin.lt_def]; simp), boolSign_false, neg_neg, Int.cast_one,
      one_mul]
  · rw [negRootB_of_not_lt K h, x_eq_short (s := false) (by
      rw [toStdB_neg, toStdB_single_of_not_lt n h, boolSign_false, Pi.single_neg]),
      boolSign_false, Int.cast_neg, Int.cast_one, neg_one_mul]

end CFSG.LieType.Steinberg.SpinOdd
