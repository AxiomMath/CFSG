module

public import CFSG.LieType.Universal.Spin.PlusCT.Basic
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Weyl
public import CFSG.LieType.Steinberg.OfCartan
public import CFSG.LieType.Steinberg.Statement

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinPlus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem

variable (n : ℕ) (K : Type) [Field K] (hn : 3 ≤ n)

@[expose] def x (γ : Fin n → ℤ) (c : K) : spinGroup (quadPlus n K) :=
  rootElt (plusFrame n K hn) (toStdD n γ) c

abbrev Φ : CFSG.LieType.Steinberg.RootSystem (Fin n) :=
  CFSG.LieType.Steinberg.RootSystem.ofCartan (plusDatum n K hn).isFiniteType
    (plusDatum n K hn).divisible

variable {n K}

theorem Φ_roots : (Φ n K hn).roots = roots (isFiniteType_cartanD n) ∅ := rfl

theorem isLong_toStdD_iff (hn : 2 ≤ n) {γ : Fin n → ℤ} :
    IsLong (toStdD n γ) ↔ γ ∈ roots (isFiniteType_cartanD n) ∅ :=
  ⟨fun ⟨_, _, hij, s, t, h⟩ => mem_rootsD_of_toStdD_eq hij s t h,
    fun h => exists_toStdD_eq_of_mem_rootsD (by omega) h⟩

theorem toStdD_add_ne_zero {α β : Fin n → ℤ} (h : α + β ≠ 0) : toStdD n α + toStdD n β ≠ 0 := by
  rw [← toStdD_add, ← toStdD_zero n]
  exact fun h' => h (toStdD_injective n h')

theorem isParametrization :
    IsParametrization (Φ := Φ n K hn) (plusDatum n K hn).rootGroup (x n K hn) := by
  intro γ hγ
  obtain ⟨i, j, hij, s, t, hγ', hX⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  refine ⟨fun g => ?_, fun c d => rootElt_add _ _ c d,
    rootElt_injective _ ⟨i, j, hij, s, t, hγ'⟩⟩
  change g ∈ plusRootGroup n K hn γ ↔ _
  rw [hX]
  exact exists_rootElt_eq_iff _ hij hγ' g

theorem toStdD_single (hn2 : 2 ≤ n) (k : Fin n) :
    toStdD n (Pi.single k 1) = Pi.single (rootIdxD n k) (boolSign true) +
      Pi.single (rootIdxD' n k) (boolSign (rootSignD n k)) :=
  toStdD_single_eq hn2 k

theorem rootIdxD_lt (hn2 : 2 ≤ n) (k : Fin n) : rootIdxD n k < rootIdxD' n k := by
  rw [Fin.lt_def, val_rootIdxD' n hn2 k]
  exact Nat.lt_succ_self _

theorem x_single (k : Fin n) (c : K) :
    x n K hn (Pi.single k 1) c = rankOneD K hn k (upperSL2 c) :=
  (longSL2_upperSL2_eq_rootElt _ (rootIdxD_lt (by omega) k) _ (toStdD_single (by omega) k) c).symm

theorem x_neg_single (k : Fin n) (c : K) :
    x n K hn (-Pi.single k 1) c = rankOneD K hn k (lowerSL2 c) := by
  rw [x, toStdD_neg]
  exact (longSL2_lowerSL2_eq_rootElt _ (rootIdxD_lt (by omega) k) _
    (toStdD_single (by omega) k) c).symm

end CFSG.LieType.Steinberg.SpinPlus
