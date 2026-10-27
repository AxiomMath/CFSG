module

public import CFSG.LieType.Steinberg.Classical.SpinPlus.Basic
public import CFSG.LieType.Steinberg.Classical.OrthogonalRoots
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Commutator

public noncomputable section

namespace CFSG.LieType.Steinberg.SpinPlus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem
open scoped commutatorElement

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

@[expose] def commC (α β : Fin n → ℤ) (_ : ℕ × ℕ) : ℤ := chainSign (toStdD n α) (toStdD n β)

theorem commC_natAbs (α β : Fin n → ℤ) (p : ℕ × ℕ) : (commC α β p).natAbs = 1 := by
  rcases chainSign_eq_one_or_eq_neg_one (toStdD n α) (toStdD n β) with h | h <;>
    simp [commC, h]

theorem commC_natAbs_mem (α : Fin n → ℤ) (_ : α ∈ (Φ n K hn).roots) (β : Fin n → ℤ)
    (_ : β ∈ (Φ n K hn).roots) (p : ℕ × ℕ) (_ : p ∈ expPairs (Φ n K hn) α β) :
    (commC α β p).natAbs ∈ ({1, 2, 3} : Set ℕ) := by
  rw [commC_natAbs]
  exact Or.inl rfl

private theorem list_eq_singleton {l : List (ℕ × ℕ)} (hl : l.Nodup)
    (h : ∀ p, p ∈ l ↔ p = (1, 1)) : l = [(1, 1)] :=
  List.perm_singleton.1 ((List.perm_ext_iff_of_nodup hl (List.nodup_singleton _)).2
    fun p => by rw [h, List.mem_singleton])

theorem commOrder_list_eq (O : CommOrder (Φ n K hn)) {α β : Fin n → ℤ}
    (hα : α ∈ (Φ n K hn).roots) (hβ : β ∈ (Φ n K hn).roots) (hαβ : α + β ≠ 0) :
    (α + β ∈ (Φ n K hn).roots → O.list α β = [(1, 1)]) ∧
      (α + β ∉ (Φ n K hn).roots → O.list α β = []) := by
  have hmem := fun p => (O.mem_iff α hα β hβ hαβ p).trans
    (Orthogonal.mem_expPairs_D (by omega) (Φ_roots hn) hα hβ hαβ p)
  refine ⟨fun hr => list_eq_singleton (O.nodup α β) fun p => (hmem p).trans (and_iff_left hr),
    fun hr => List.eq_nil_iff_forall_not_mem.2 fun p hp => hr ((hmem p).1 hp).2⟩

theorem commutatorFormula (O : CommOrder (Φ n K hn)) : CommutatorFormula (x n K hn) O commC := by
  intro α hα β hβ hαβ c d
  have ha := (isLong_toStdD_iff (by omega)).mpr hα
  have hb := (isLong_toStdD_iff (by omega)).mpr hβ
  have hab := toStdD_add_ne_zero hαβ
  by_cases hr : α + β ∈ (Φ n K hn).roots
  · rw [(commOrder_list_eq hn O hα hβ hαβ).1 hr, List.map_singleton, List.prod_singleton,
      one_smul, one_smul, pow_one, pow_one]
    have hl : IsLong (toStdD n α + toStdD n β) := by
      rw [← toStdD_add]
      exact (isLong_toStdD_iff (by omega)).mpr hr
    unfold x
    rw [toStdD_add]
    exact commutator_rootElt _ ha hb hab hl c d
  · rw [(commOrder_list_eq hn O hα hβ hαβ).2 hr, List.map_nil, List.prod_nil,
      commutatorElement_eq_one_iff_commute]
    have hl : ¬IsLong (toStdD n α + toStdD n β) := by
      rw [← toStdD_add]
      exact fun h => hr ((isLong_toStdD_iff (by omega)).mp h)
    exact commute_rootElt _ ha hb hab hl c d

theorem cast_eq_commC {O : CommOrder (Φ n K hn)} {C : (Fin n → ℤ) → (Fin n → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (x n K hn) O C) {α β : Fin n → ℤ} (hα : α ∈ (Φ n K hn).roots)
    (hβ : β ∈ (Φ n K hn).roots) (hαβ : α + β ≠ 0) {p : ℕ × ℕ}
    (hp : p ∈ expPairs (Φ n K hn) α β) : (C α β p : K) = (commC α β p : K) := by
  obtain ⟨rfl, hr⟩ := (Orthogonal.mem_expPairs_D (by omega) (Φ_roots hn) hα hβ hαβ p).mp hp
  have h1 := hC α hα β hβ hαβ 1 1
  have h2 := commutatorFormula hn O α hα β hβ hαβ 1 1
  rw [(commOrder_list_eq hn O hα hβ hαβ).1 hr, List.map_singleton, List.prod_singleton] at h1 h2
  simp only [one_smul, one_pow, mul_one] at h1 h2
  exact ((isParametrization hn) _ hr).2.2 (h1.symm.trans h2)

end CFSG.LieType.Steinberg.SpinPlus
