module

public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.CurtisTits.Reduction
public import CFSG.LieType.Universal.Spin.Roots

public section

namespace CFSG.LieType.Universal.Spin.PlusCT

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

variable {n : ℕ} {K : Type} [Field K]

theorem mem_plusRootGroup_iff (hn : 3 ≤ n) {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) (h : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    {x : spinGroup (quadPlus n K)} :
    x ∈ plusRootGroup n K hn γ ↔ ∃ c : K, x = (plusFrame n K hn).longRoot hij s t (.ofAdd c) := by
  rw [plusRootGroup_eq hn hij s t h, MonoidHom.mem_range]
  exact ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨_, hc.symm⟩⟩

theorem longRoot_mem_plusRootGroup (hn : 3 ≤ n) {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) (h : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (c : K) :
    (plusFrame n K hn).longRoot hij s t (.ofAdd c) ∈ plusRootGroup n K hn γ :=
  (mem_plusRootGroup_iff hn hij s t h).mpr ⟨c, rfl⟩

theorem rankOne_plusRootGroup (hn : 3 ≤ n) (k : Fin n) :
    rankOne (plusRootGroup n K hn) k = (rankOneD K hn k).range := by
  rw [rankOne, plusRootGroup_single, plusRootGroup_neg_single]
  refine le_antisymm (sup_le ?_ ?_) ?_
  · rintro _ ⟨c, rfl⟩
    exact ⟨upperSL2 (Multiplicative.toAdd c), rankOneD_upperSL2 K hn k _⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨lowerSL2 (Multiplicative.toAdd c), rankOneD_lowerSL2 K hn k _⟩
  · rintro _ ⟨M, rfl⟩
    refine (Subgroup.closure_le _).mpr ?_ (rankOneD_mem_closure K hn k M)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact Subgroup.mem_sup_left ⟨c, rfl⟩
    · exact Subgroup.mem_sup_right ⟨c, rfl⟩

theorem rankOneD_mem_rankOne (hn : 3 ≤ n) (k : Fin n) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    rankOneD K hn k M ∈ rankOne (plusRootGroup n K hn) k := by
  rw [rankOne_plusRootGroup]
  exact ⟨M, rfl⟩

private theorem two_le_of_ne {i j : Fin n} (hij : i ≠ j) : 2 ≤ n := by
  have h : i.val ≠ j.val := fun e => hij (Fin.ext e)
  have := i.isLt
  have := j.isLt
  omega

theorem mem_rootsD_of_toStdD_eq {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (h : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    γ ∈ roots (isFiniteType_cartanD n) ∅ := by
  have := two_le_of_ne hij
  rw [rootsD_eq n (by omega)]
  exact ⟨i, j, boolSign s, boolSign t, hij, boolSign_eq_one_or_eq_neg_one s,
    boolSign_eq_one_or_eq_neg_one t, h⟩

theorem exists_toStdD_eq_of_mem_rootsD (hn : n ≠ 1) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) :
    ∃ (i j : Fin n) (_ : i ≠ j) (s t : Bool),
      toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
  rw [rootsD_eq n hn] at hγ
  obtain ⟨i, j, s, t, hij, hs, ht, h⟩ := hγ
  obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
  obtain ⟨t', rfl⟩ := exists_boolSign_eq ht
  exact ⟨i, j, hij, s', t', h⟩

theorem single_add_single_apply_mem {i j : Fin n} (hij : i ≠ j) (s t : Bool) (x : Fin n) :
    (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) x = 0 ∨
      (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) x = 1 ∨
      (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) x = -1 := by
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs with h1 h2 h2
  · exact absurd (h1.symm.trans h2) hij
  · cases s <;> simp
  · cases t <;> simp
  · simp

theorem single_add_single_apply_left {i j : Fin n} (hij : i ≠ j) (a b : ℤ) :
    (Pi.single i a + Pi.single j b : Fin n → ℤ) i = a := by
  rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]

theorem stdReflD_add (k : Fin n) (e e' : Fin n → ℤ) :
    stdReflD n k (e + e') = stdReflD n k e + stdReflD n k e' := by
  by_cases h : k.val + 1 < n
  · rw [stdReflD_of_lt n h, stdReflD_of_lt n h, stdReflD_of_lt n h]
    rfl
  · rw [stdReflD_of_not_lt n h, stdReflD_of_not_lt n h, stdReflD_of_not_lt n h]
    funext a
    simp only [Pi.add_apply]
    ring

theorem stdReflD_single (hn : 2 ≤ n) (k i : Fin n) (s : Bool) :
    stdReflD n k (Pi.single i (boolSign s)) =
      Pi.single (Equiv.swap (rootIdxD n k) (rootIdxD' n k) i)
        (boolSign (longWeylBool (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) i s)) := by
  by_cases h : k.val + 1 < n
  · rw [stdReflD_of_lt n h, rootIdxD_of_lt n h, rootIdxD'_of_lt n h, rootSignD_of_lt n h,
      Pi.single_comp_equiv, Equiv.symm_swap]
    simp [longWeylBool]
  · have ha : (⟨k.val - 1, by omega⟩ : Fin n) = rootIdxD n k :=
      Fin.ext (by rw [val_rootIdxD_of_not_lt n h]; simp only; omega)
    have hb : rootIdxD' n k = k := Fin.ext (by rw [val_rootIdxD'_of_not_lt n h]; omega)
    rw [stdReflD_of_not_lt n h, ha, hb, rootSignD_of_not_lt n h]
    have hav : (rootIdxD n k).val + 2 = n := by rw [val_rootIdxD_of_not_lt n h]; omega
    have hkv : k.val + 1 = n := by omega
    funext x
    by_cases hx : x = Equiv.swap (rootIdxD n k) k i
    · rw [hx, Equiv.swap_apply_self, Pi.single_eq_same, Pi.single_eq_same]
      by_cases hia : i = rootIdxD n k
      · rw [hia, Equiv.swap_apply_left, ite_eq_left (Or.inr hkv)]
        simp [longWeylBool]
      · by_cases hik : i = k
        · rw [hik, Equiv.swap_apply_right, ite_eq_left (Or.inl hav)]
          simp [longWeylBool]
        · have hne : ¬(i.val + 2 = n ∨ i.val + 1 = n) := by
            rintro (h1 | h1)
            · exact hia (Fin.ext (by omega))
            · exact hik (Fin.ext (by omega))
          rw [Equiv.swap_apply_of_ne_of_ne hia hik, ite_eq_right hne]
          simp [longWeylBool, hia, hik]
    · have hx' : Equiv.swap (rootIdxD n k) k x ≠ i := fun e =>
        hx (by rw [← e, Equiv.swap_apply_self])
      rw [Pi.single_eq_of_ne hx', Pi.single_eq_of_ne hx, mul_zero]

theorem toStdD_reflection_eq (hn : 2 ≤ n) (k : Fin n) {γ : Fin n → ℤ} {i j : Fin n} {s t : Bool}
    (h : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    toStdD n (reflection (cartanD n) k γ) =
      Pi.single (Equiv.swap (rootIdxD n k) (rootIdxD' n k) i)
          (boolSign (longWeylBool (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) i s)) +
        Pi.single (Equiv.swap (rootIdxD n k) (rootIdxD' n k) j)
          (boolSign (longWeylBool (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) j t)) := by
  rw [toStdD_reflection, h, stdReflD_add, stdReflD_single hn, stdReflD_single hn]

end CFSG.LieType.Universal.Spin.PlusCT
