module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Perm
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Check

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem card_orthGroup_le (ε : Eps) : Nat.card (orthGroup ε) ≤ oBound ε := by
  classical
  have hinj : Function.Injective fun σ : orthGroup ε =>
      (⟨colsOf σ, List.mem_toFinset.2 (colsOf_mem_oCols σ.2)⟩ : (oCols ε).toFinset) := by
    intro σ τ h
    exact Subtype.ext (eq_of_colsOf_eq σ.2.1 τ.2.1 (congrArg Subtype.val h))
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard] at h1
  have h2 := (checks ε).2.2.1
  rw [oCheck, beq_iff_eq] at h2
  exact h1.trans (h2 ▸ List.toFinset_card_le _)

theorem card_affGroup_le (ε : Eps) :
    Nat.card (affGroup ε) ≤ (zeroSet ε).card * oBound ε := by
  classical
  have e := MulAction.orbitProdStabilizerEquivGroup (affGroup ε) (0 : V6)
  rw [← Nat.card_congr e, Nat.card_prod]
  refine Nat.mul_le_mul ?_ ?_
  · have hsub : ∀ x ∈ MulAction.orbit (affGroup ε) (0 : V6), x ∈ zeroSet ε := by
      rintro x ⟨σ, rfl⟩
      simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
      change qfV ε ((σ : Equiv.Perm V6) 0) = 0
      rw [σ.2.1, qfV_zero]
    have hinj : Function.Injective fun x : MulAction.orbit (affGroup ε) (0 : V6) =>
        (⟨x.1, hsub x.1 x.2⟩ : zeroSet ε) := by
      intro x y h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext h
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_finsetCard] at this
  · have hmem : ∀ σ : MulAction.stabilizer (affGroup ε) (0 : V6),
        ((σ : affGroup ε) : Equiv.Perm V6) ∈ orthGroup ε := fun σ =>
      mem_orthGroup_of_mem_affGroup (σ : affGroup ε).2 σ.2
    have hinj : Function.Injective fun σ : MulAction.stabilizer (affGroup ε) (0 : V6) =>
        (⟨((σ : affGroup ε) : Equiv.Perm V6), hmem σ⟩ : orthGroup ε) := by
      intro σ τ h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    exact (Nat.card_le_card_of_injective _ hinj).trans (card_orthGroup_le ε)

end CFSG.EvenSmallLie.OmegaEight.Stage1
