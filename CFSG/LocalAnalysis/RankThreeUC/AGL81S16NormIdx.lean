module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.RankThreeUC

theorem card_fix_mul_le {F : Type} [Field F] [Finite F] {θ : F →+* F}
    (α : (Fin 4 → F) ≃+ (Fin 4 → F))
    (hα : ∀ (c : F) (x : Fin 4 → F), α (c • x) = θ c • α x) (hne : ∃ x, α x ≠ x) :
    Nat.card {x : Fin 4 → F // α x = x} * Nat.card F ≤ Nat.card (Fin 4 → F) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Fin 4 → F) →+ (Fin 4 → F), ∀ x, ψ x = α x - x :=
    ⟨α.toAddMonoidHom - AddMonoidHom.id _, fun x => rfl⟩
  have hker : Nat.card {x : Fin 4 → F // α x = x} = Nat.card ψ.ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [AddMonoidHom.mem_ker, hψ, sub_eq_zero]
  have hmul : Nat.card ψ.ker * Nat.card ψ.range = Nat.card (Fin 4 → F) :=
    AddSubgroup.card_ker_mul_card_range ψ
  suffices hF : Nat.card F ≤ Nat.card ψ.range by
    rw [hker, ← hmul]
    exact Nat.mul_le_mul le_rfl hF
  by_cases hA : ∃ x : Fin 4 → F, ¬ ∃ c : F, α x = c • x
  ·
    obtain ⟨x0, hx0⟩ := hA
    refine Nat.card_le_card_of_injective
      (fun c : F => (⟨ψ (c • x0), AddMonoidHom.mem_range.mpr ⟨c • x0, rfl⟩⟩ : ψ.range)) ?_
    intro c c' h
    have hc : ψ (c • x0) = ψ (c' • x0) := congrArg Subtype.val h
    have e1 : ψ (c • x0) = θ c • α x0 - c • x0 := by rw [hψ, hα]
    have e2 : ψ (c' • x0) = θ c' • α x0 - c' • x0 := by rw [hψ, hα]
    have h0 : (θ c • α x0 - c • x0) - (θ c' • α x0 - c' • x0) = 0 := by
      rw [← e1, ← e2, hc, sub_self]
    have key : (θ c - θ c') • α x0 - (c - c') • x0 = 0 := by
      have e3 : (θ c - θ c') • α x0 - (c - c') • x0
          = (θ c • α x0 - c • x0) - (θ c' • α x0 - c' • x0) := by
        simp only [sub_smul]
        abel
      exact e3.trans h0
    by_contra hcc
    have hd : c - c' ≠ 0 := sub_ne_zero.mpr hcc
    have hθd : θ (c - c') ≠ 0 := by
      intro h0'
      exact hd (θ.injective (by rw [h0', map_zero]))
    have key3 : θ (c - c') • α x0 = (c - c') • x0 := by
      rw [map_sub]
      exact sub_eq_zero.mp key
    apply hx0
    refine ⟨(θ (c - c'))⁻¹ * (c - c'), ?_⟩
    calc α x0 = (θ (c - c'))⁻¹ • (θ (c - c') • α x0) := (inv_smul_smul₀ hθd _).symm
      _ = (θ (c - c'))⁻¹ • ((c - c') • x0) := by rw [key3]
      _ = ((θ (c - c'))⁻¹ * (c - c')) • x0 := smul_smul _ _ _
  ·
    have hA' : ∀ x : Fin 4 → F, ∃ c : F, α x = c • x := fun x => by
      by_contra hx
      exact hA ⟨x, hx⟩
    choose g hg using hA'
    have key : ∀ i j : Fin 4, i ≠ j → g (Pi.single i 1) = g (Pi.single j 1) := by
      intro i j hij
      have h1 : α (Pi.single i 1 + Pi.single j 1)
          = g (Pi.single i 1 + Pi.single j 1) • (Pi.single i 1 + Pi.single j 1) := hg _
      have h2 : α (Pi.single i 1 + Pi.single j 1)
          = g (Pi.single i 1) • Pi.single i 1 + g (Pi.single j 1) • Pi.single j 1 := by
        rw [map_add, hg, hg]
      have h3 : g (Pi.single i 1 + Pi.single j 1) = g (Pi.single i 1) := by
        have := congrFun (h1.symm.trans h2) i
        simpa [Pi.single_apply, hij] using this
      have h4 : g (Pi.single i 1 + Pi.single j 1) = g (Pi.single j 1) := by
        have := congrFun (h1.symm.trans h2) j
        simpa [Pi.single_apply, hij.symm] using this
      exact h3.symm.trans h4
    obtain ⟨μ, hμ⟩ : ∃ μ : F, ∀ i : Fin 4, α (Pi.single i 1) = μ • Pi.single i 1 := by
      refine ⟨g (Pi.single (0 : Fin 4) (1 : F)), fun i => ?_⟩
      by_cases hi : i = 0
      · subst hi
        exact hg _
      · rw [hg, key i 0 hi]
    have hμ0 : μ ≠ 0 := by
      intro h0
      have h1 : α (Pi.single (0 : Fin 4) (1 : F)) = α 0 := by
        rw [hμ 0, h0, zero_smul, map_zero]
      have h2 : (Pi.single (0 : Fin 4) (1 : F) : Fin 4 → F) = 0 := α.injective h1
      have h3 := congrFun h2 0
      simp at h3
    have hθ : ∀ c : F, θ c = c := by
      intro c
      have h1 := hg (c • Pi.single (0 : Fin 4) (1 : F) + Pi.single (1 : Fin 4) (1 : F))
      have h2 : α (c • Pi.single (0 : Fin 4) (1 : F) + Pi.single (1 : Fin 4) (1 : F))
          = (θ c * μ) • Pi.single (0 : Fin 4) (1 : F) + μ • Pi.single (1 : Fin 4) (1 : F) := by
        rw [map_add, hα, hμ 0, hμ 1, smul_smul]
      have h3 := h1.symm.trans h2
      have h4 : g (c • Pi.single (0 : Fin 4) (1 : F) + Pi.single (1 : Fin 4) (1 : F)) = μ := by
        have := congrFun h3 1
        simpa [Pi.single_apply] using this
      have h5 : g (c • Pi.single (0 : Fin 4) (1 : F) + Pi.single (1 : Fin 4) (1 : F)) * c
          = θ c * μ := by
        have := congrFun h3 0
        simpa [Pi.single_apply] using this
      have h7 : (θ c - c) * μ = 0 := by linear_combination -h5 + c * h4
      exact sub_eq_zero.mp ((mul_eq_zero.mp h7).resolve_right hμ0)
    have hlin : ∀ x : Fin 4 → F, α x = μ • x := by
      intro x
      have hi : ∀ (i : Fin 4) (c : F), α (Pi.single i c) = μ • Pi.single i c := by
        intro i c
        have hc : (Pi.single i c : Fin 4 → F) = c • Pi.single i (1 : F) := by
          ext j
          by_cases h : j = i
          · subst h
            simp
          · simp [Pi.single_apply, h]
        rw [hc, hα, hμ i, hθ c, smul_comm]
      calc α x = α (∑ i, Pi.single i (x i)) := by rw [Finset.univ_sum_single]
        _ = ∑ i, α (Pi.single i (x i)) := map_sum α _ _
        _ = ∑ i, μ • Pi.single i (x i) := Finset.sum_congr rfl fun i _ => hi i (x i)
        _ = μ • ∑ i, Pi.single i (x i) := by rw [Finset.smul_sum]
        _ = μ • x := by rw [Finset.univ_sum_single]
    obtain ⟨x1, hx1⟩ := hne
    have hμ1 : μ - 1 ≠ 0 := by
      intro h
      apply hx1
      rw [hlin x1, sub_eq_zero.mp h, one_smul]
    have hψx : ∀ x, ψ x = (μ - 1) • x := by
      intro x
      rw [hψ, hlin x, sub_smul, one_smul]
    have hinj : Function.Injective ψ := by
      intro x y hxy
      rw [hψx, hψx] at hxy
      have := congrArg (fun z => (μ - 1)⁻¹ • z) hxy
      simpa only [inv_smul_smul₀ hμ1] using this
    refine Nat.card_le_card_of_injective
      (fun c : F => (⟨ψ (Pi.single (0 : Fin 4) c),
        AddMonoidHom.mem_range.mpr ⟨Pi.single (0 : Fin 4) c, rfl⟩⟩ : ψ.range)) ?_
    intro c c' h
    have h1 : ψ (Pi.single (0 : Fin 4) c) = ψ (Pi.single (0 : Fin 4) c') :=
      congrArg Subtype.val h
    have h2 : (Pi.single (0 : Fin 4) c : Fin 4 → F) = Pi.single (0 : Fin 4) c' := hinj h1
    simpa using congrFun h2 0

end CFSG.LocalAnalysis.RankThreeUC
