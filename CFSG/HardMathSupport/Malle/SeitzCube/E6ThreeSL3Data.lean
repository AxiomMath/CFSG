module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.E6 (chain13 chain56 e6Index chainRoot e6RootVec)

@[expose] def e6HighestRoot : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def e6A2Word : List (Fin Tag.E6.rank) :=
  ([3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2] : List (Fin 6))

theorem wordProd_smul_E6 (l : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    (coxeterSystem .E6).wordProd l • v = l.foldr (reflect .E6) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

@[expose] def e6A2Simple₀ (i : Fin 3) : Fin Tag.E6.rank → ℤ :=
  match i with
  | 0 => Pi.single (e6Index 0) 1
  | 1 => Pi.single (e6Index 4) 1
  | 2 => Pi.single (e6Index 1) 1

@[expose] def e6A2Simple₁ (i : Fin 3) : Fin Tag.E6.rank → ℤ :=
  match i with
  | 0 => Pi.single (e6Index 2) 1
  | 1 => Pi.single (e6Index 5) 1
  | 2 => -e6HighestRoot

@[expose] def e6A2Weight (i : Fin 3) (a : Fin 3) : Fin Tag.E6.rank → ℤ :=
  match a with
  | 0 => 0
  | 1 => -e6A2Simple₀ i
  | 2 => -e6A2Simple₀ i - e6A2Simple₁ i

@[expose] def e6A2Root (i a b : Fin 3) : Fin Tag.E6.rank → ℤ := e6A2Weight i a - e6A2Weight i b

@[expose] def e6A2Frame (i : Fin 3) (γ : Fin 2 → ℤ) : Fin Tag.E6.rank → ℤ :=
  γ 0 • e6A2Simple₀ i + γ 1 • e6A2Simple₁ i

theorem chainRoot13_eq : ∀ a b : Fin 3, chainRoot chain13 a b = e6A2Root 0 a b := by
  decide +kernel

theorem chainRoot56_eq : ∀ a b : Fin 3, chainRoot chain56 a b = e6A2Root 1 a b := by
  decide +kernel

theorem wordProd_chainRoot13_eq : ∀ a b : Fin 3,
    (coxeterSystem Tag.E6).wordProd e6A2Word • chainRoot chain13 a b = e6A2Root 2 a b := by
  intro a b
  rw [wordProd_smul_E6]
  revert a b
  decide +kernel

theorem e6A2_root_check : (∀ i a b : Fin 3, a ≠ b → ∃ m : Fin 72, e6RootVec m = e6A2Root i a b) ∧
    ∀ i j : Fin 3, i ≠ j → ∀ a b a' b' : Fin 3, a ≠ b → a' ≠ b' →
      e6A2Root i a b ≠ e6A2Root j a' b' ∧ e6A2Root i a b + e6A2Root j a' b' ≠ 0 ∧
        ¬ ∃ m : Fin 72, e6RootVec m = e6A2Root i a b + e6A2Root j a' b' := by
  decide +kernel

end CFSG.HardMathSupport.Malle.SeitzCube
