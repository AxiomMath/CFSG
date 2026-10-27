module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassCConj
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14ClassCBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module

section

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

theorem tvC_top {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} (hA : IsElemAbelian p A)
    {t : LinearMap.GeneralLinearGroup (ZMod 2) U} (ht : IsF2Transvection t) :
    HasCentralizedConj p ⊤ A t := by
  classical
  by_cases hc : IsCyclic A
  · exact i28_14_C_of_cyclic hp hA hc t
  obtain ⟨E, hEA, hcard, c, hcE, d, hdE, hc0, hd0, hcd⟩ := i28_14_C_exists_hyperplane hp hp2 hA hc
  have hodd := i28_14_C_odd_card hp hp2 hA hEA
  have : Fintype E := Fintype.ofFinite E
  have hoddF : Odd (Fintype.card E) := by rwa [← Nat.card_eq_fintype_card]
  have hdspan : d ∉ Submodule.span (ZMod 2) {c} := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    rcases zmod2_eq_zero_or_one a with rfl | rfl
    · exact hd0 (by rw [← ha, zero_smul])
    · exact hcd (by rw [← ha, one_smul])
  obtain ⟨φ₀, hφ₀d, hφ₀c⟩ : ∃ φ₀ : Dual (ZMod 2) U, φ₀ d = 1 ∧ φ₀ c = 0 := by
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hdspan inferInstance
    refine ⟨f, ?_, ?_⟩
    · rcases zmod2_eq_zero_or_one (f d) with h | h
      · exact absurd h hf
      · exact h
    · have : f c ∈ Submodule.map f (Submodule.span (ZMod 2) {c}) :=
        Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self c)
      rw [hmap] at this
      exact (Submodule.mem_bot (ZMod 2)).mp this
  let φ : Dual (ZMod 2) U := φ₀ ∘ₗ avgOp E
  have hφc : φ c = 0 := by
    change φ₀ (avgOp E c) = 0
    rw [avgOp_of_mem_fixSub E hoddF hcE, hφ₀c]
  have hφd : φ d = 1 := by
    change φ₀ (avgOp E d) = 1
    rw [avgOp_of_mem_fixSub E hoddF hdE, hφ₀d]
  have hφ0 : φ ≠ 0 := fun h => by
    have := hφd
    rw [h] at this
    exact zero_ne_one this
  have hφE : ∀ e ∈ E, ∀ x, φ ((e : U →ₗ[ZMod 2] U) x) = φ x := fun e he x => by
    change φ₀ (avgOp E ((e : U →ₗ[ZMod 2] U) x)) = φ₀ (avgOp E x)
    rw [avgOp_comp E he]
  obtain ⟨φt, a, h, hφt, ha, rfl⟩ := (isF2Transvection_iff t).mp ht
  obtain ⟨g, hg⟩ := i28_14_C_exists_conj_tv h hφc hφt ha hφ0 hc0
  refine i28_14_C_close (y := g⁻¹) (Subgroup.mem_top _) hEA hcard.le fun e he => ?_
  rw [inv_inv, hg]
  exact i28_14_C_comm_tv hφc (hcE e he) (hφE e he)

end

end CFSG.HardMathSupport.Solomon.Coordinator
