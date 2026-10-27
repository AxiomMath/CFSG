module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.MElementAux2

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open MElt

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem exists_M_element {X₁ X₂ H : Subgroup (ModGL τ K)} (hb : TwBasic X₁ X₂)
    (hc : TwCentral X₁ X₂) (hco : TwCoords X₁ X₂) (hp : TwPure X₁ X₂) (h3 : 3 ≤ Nat.card K)
    (hHG : H ≤ adjointGroup τ K) (hXH : X₁ ⊔ X₂ ≤ H) {g : ModGL τ K} (hgH : g ∈ H)
    (hgX : ¬ conjSub g (Uθ τ K) ≤ X₁ ⊔ X₂) :
    ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂) := by
  classical
  by_contra! hno
  have hX₁X : X₁ ≤ X₁ ⊔ X₂ := le_sup_left
  refine hgX fun b hb₀ => ?_
  have hbc : ∀ x ∈ X₁, b * x = x * b := by
    have hle : (⨆ x ∈ X₁, conjSub x (Uθ τ K)) ≤ Subgroup.centralizer ({b} : Set (ModGL τ K)) := by
      refine iSup₂_le fun x hx y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxH : x⁻¹ ∈ H := inv_mem (hXH (hX₁X hx))
      have hg'H : x⁻¹ * g ∈ H := mul_mem hxH hgH
      have hg'X : ¬ conjSub (x⁻¹ * g) (Uθ τ K) ≤ X₁ ⊔ X₂ := by
        intro hle
        apply hgX
        have e : conjSub g (Uθ τ K) = conjSub x (conjSub (x⁻¹ * g) (Uθ τ K)) := by
          rw [← conjSub_mul, mul_inv_cancel_left]
        rw [e]
        exact conjSub_le_of_mem_of_le (hX₁X hx) hle
      have ha : x⁻¹ * y * x ∈ Uθ τ K := mem_conjSub_iff.1 hy
      have hb' : x⁻¹ * b * x ∈ conjSub (x⁻¹ * g) (Uθ τ K) := by
        rw [mem_conjSub_iff]
        have e : (x⁻¹ * g)⁻¹ * (x⁻¹ * b * x) * (x⁻¹ * g) = g⁻¹ * b * g := by group
        rw [e]
        exact mem_conjSub_iff.1 hb₀
      have h := core_commute hb hco hp h3 hHG hXH hno hg'H hg'X _ ha _ hb'
      calc y * b = x * ((x⁻¹ * y * x) * (x⁻¹ * b * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * b * x) * (x⁻¹ * y * x)) * x⁻¹ := by rw [h]
        _ = b * y := by group
    rw [hb.gen] at hle
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hbG : b ∈ adjointGroup τ K := by
    have hu := mem_conjSub_iff.1 hb₀
    have e : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hHG hgH)
      (rootSubgroup_le_adjointGroup (τ := τ) (K := K) (highRoot τ) hu)) (inv_mem (hHG hgH))
  have hbp : b ^ ringChar K = 1 := by
    obtain ⟨c, hc'⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hb₀)
    have e : b = g * pinnedX τ K (highRoot τ) c * g⁻¹ := by rw [hc']; group
    rw [e, conj_pow, pinnedX_pow, ringChar.Nat.cast_ringChar, zero_mul, pinnedX_zero]
    group
  exact hc.unipotent_le b hbG hbc hbp

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
