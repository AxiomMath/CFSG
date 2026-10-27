module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivationTests
public import CFSG.Timmesfeld.Orders.ExceptionalWeyl

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.GF2Type.SmithTypeE.E8.Lead

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction CFSG.Timmesfeld.ExceptionalOrders

abbrev Vec7 : Type := Fin (Tag.rank .E7) → ℤ

@[expose] def Phip : Set Vec7 := {β | IsRoot .E7 β ∧ 0 < height β}

@[expose] def lwW (i : Fin (Tag.rank .E7)) : ℤ := [3125, 625, 125, 25, 5, 1, 15625].getD i 0

@[expose] def lw (v : Vec7) : ℤ := ∑ i, lwW i * v i

theorem lw_add (v w : Vec7) : lw (v + w) = lw v + lw w := by
  simp [lw, mul_add, Finset.sum_add_distrib]

theorem lw_nsmul (n : ℕ) (v : Vec7) : lw (n • v) = n * lw v := by
  simp [lw, Finset.mul_sum, mul_left_comm]

theorem lw_nsmul_add_nsmul (a b : ℕ) (α β : Vec7) : lw (a • α + b • β) = a * lw α + b * lw β := by
  rw [lw_add, lw_nsmul, lw_nsmul]

section Checks


theorem lw_pos {β : Vec7} (hβ : IsRoot .E7 β) (hp : 0 < height β) : 0 < lw β := by
  have h : ∀ v ∈ rootList .E7, 0 < height v → 0 < lw v := by decide +kernel
  exact h β (mem_rootList.2 hβ) hp

theorem lw_injOn {β γ : Vec7} (hβ : IsRoot .E7 β) (hβp : 0 < height β) (hγ : IsRoot .E7 γ)
    (hγp : 0 < height γ) (h : lw β = lw γ) : β = γ := by
  have h' : ∀ v ∈ rootList .E7, ∀ w ∈ rootList .E7, 0 < height v → 0 < height w →
      lw v = lw w → v = w := by decide +kernel
  exact h' β (mem_rootList.2 hβ) γ (mem_rootList.2 hγ) hβp hγp h

theorem lw_le {β : Vec7} (hβ : IsRoot .E7 β) (hp : 0 < height β) : lw β ≤ 30000 := by
  have h : ∀ v ∈ rootList .E7, 0 < height v → lw v ≤ 30000 := by decide +kernel
  exact h β (mem_rootList.2 hβ) hp

abbrev n7 : Fin (Tag.rank .E7) := ⟨6, by decide⟩

theorem c7_cases {β : Vec7} (hβ : IsRoot .E7 β) (hp : 0 < height β) :
    β n7 = 0 ∨ β n7 = 1 := by
  have h : ∀ v ∈ rootList .E7, 0 < height v → (v n7 = 0 ∨ v n7 = 1) := by decide +kernel
  exact h β (mem_rootList.2 hβ) hp

theorem c7_eq_one_iff {β : Vec7} (hβ : IsRoot .E7 β) (hp : 0 < height β) :
    β n7 = 1 ↔ 15625 ≤ lw β := by
  have h : ∀ v ∈ rootList .E7, 0 < height v → (v n7 = 1 ↔ 15625 ≤ lw v) := by decide +kernel
  exact h β (mem_rootList.2 hβ) hp

theorem ncard_c7 : {β : Vec7 | IsRoot .E7 β ∧ 0 < height β ∧ 15625 ≤ lw β}.ncard = 27 :=
  (ncard_setOf_isRoot_and (τ := .E7) fun β => 0 < height β ∧ 15625 ≤ lw β).trans
    (by decide +kernel)

end Checks

end CFSG.GF2Type.SmithTypeE.E8.Lead
