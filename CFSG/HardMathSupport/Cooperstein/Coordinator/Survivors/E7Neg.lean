module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.Open.LocalVocabulary

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem

@[expose] def e7W0Word : List (Fin Tag.E7.rank) :=
  (List.replicate 9 ([0, 1, 2, 3, 4, 5, 6] : List (Fin 7))).flatten

theorem e7W0_single : ∀ i : Fin Tag.E7.rank,
    e7W0Word.foldr (reflect .E7) (Pi.single i 1) = -Pi.single i 1 := by
  decide +kernel

theorem wordProd_smul_foldr {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem wordProd_smul_neg_of_single'
    {τ : Tag} {l : List (Fin τ.rank)}
    (h : ∀ i : Fin τ.rank, l.foldr (reflect τ) (Pi.single i 1) = -Pi.single i 1)
    (α : Fin τ.rank → ℤ) : (coxeterSystem τ).wordProd l • α = -α := by
  have hf : ∀ i : Fin τ.rank, ∀ c : ℤ,
      (coxeterSystem τ).wordProd l • (Pi.single i c : Fin τ.rank → ℤ) =
        -(Pi.single i c : Fin τ.rank → ℤ) := by
    intro i c
    have e : (Pi.single i c : Fin τ.rank → ℤ) = c • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [e, smul_comm, wordProd_smul_foldr, h, smul_neg]
  conv_lhs => rw [← Finset.univ_sum_single α]
  rw [Finset.smul_sum]
  simp only [hf, Finset.sum_neg_distrib, Finset.univ_sum_single]

theorem exists_weyl_neg_E7 :
    ∃ w₁ : WeylGroup .E7, ∀ α : Fin Tag.E7.rank → ℤ, w₁ • α = -α :=
  ⟨_, wordProd_smul_neg_of_single' e7W0_single⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
