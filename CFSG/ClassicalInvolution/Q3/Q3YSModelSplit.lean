module

public import CFSG.ClassicalInvolution.Q3.Q3YSTorus
public import CFSG.ClassicalInvolution.Q3.Q3YSInputs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Steinberg

section Cartan

theorem odd_cartanA (m : ℕ) (hm : 2 ≤ m) :
    Odd (CartanMatrix.A m ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
      Odd (CartanMatrix.A m ⟨1, by omega⟩ ⟨0, by omega⟩) := by
  constructor <;> simp [CartanMatrix.A, Fin.ext_iff]

theorem odd_cartanC (n : ℕ) (hn : 3 ≤ n) :
    Odd (Symplectic.cartanC n ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
      Odd (Symplectic.cartanC n ⟨1, by omega⟩ ⟨0, by omega⟩) := by
  constructor <;> simp [Symplectic.cartanC, Fin.ext_iff] <;>
    split_ifs <;> first | (exfalso; omega) | decide

theorem odd_cartanB (n : ℕ) (hn : 3 ≤ n) :
    Odd (Spin.cartanB n ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
      Odd (Spin.cartanB n ⟨1, by omega⟩ ⟨0, by omega⟩) := by
  constructor <;> simp [Spin.cartanB, Fin.ext_iff] <;>
    split_ifs <;> first | (exfalso; omega) | decide

theorem odd_cartanD (n : ℕ) (hn : 4 ≤ n) :
    Odd (Spin.cartanD n ⟨0, by omega⟩ ⟨1, by omega⟩) ∧
      Odd (Spin.cartanD n ⟨1, by omega⟩ ⟨0, by omega⟩) := by
  constructor <;> simp [Spin.cartanD, Fin.ext_iff] <;>
    split_ifs <;> first | (exfalso; omega) | decide

theorem odd_cartanE (r : ℕ) (hr : 3 ≤ r) :
    Odd (CFSG.Blueprint.Chevalley.Tag.cartanE r ⟨0, by omega⟩ ⟨2, by omega⟩) ∧
      Odd (CFSG.Blueprint.Chevalley.Tag.cartanE r ⟨2, by omega⟩ ⟨0, by omega⟩) := by
  constructor <;> simp [CFSG.Blueprint.Chevalley.Tag.cartanE, Fin.ext_iff]

end Cartan

section Model

theorem fourGroup_of_nodes {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K}
    (hext : ∃ x C O, ChevalleyExtras D (GaloisField 3 1) x C O) {a b : Fin D.rank}
    (hab : Odd (D.cartan a b)) (hba : Odd (D.cartan b a)) :
    ∃ F : Subgroup K, IsElemAbelian 2 F ∧ Nat.card F = 4 ∧ F ⊓ Subgroup.center K = ⊥ := by
  obtain ⟨x, C, O, hX⟩ := hext
  exact exists_fourGroup_torus hX neg_one_ne_one_gf3 hab hba


theorem fourGroup_psl (n : ℕ) (hadm : StatedLieAdmissible .PSL n 3 1) :
    ∃ F : Subgroup (modelUniv .PSL n 3 1 Nat.prime_three).K, IsElemAbelian 2 F ∧
      Nat.card F = 4 ∧ F ⊓ Subgroup.center (modelUniv .PSL n 3 1 Nat.prime_three).K = ⊥ := by
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hn3 : n ≠ 2 := fun h => hadm.2.2.2.2 (by simp [h])
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have hfin : Finite (modelUniv .PSL (m + 1) 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  exact fourGroup_of_nodes (Balance.exists_chevalleyExtras_model (p := 3) .PSL (m + 1) 1 hadm
    (Or.inl ⟨rfl, by omega⟩)) (a := ⟨0, by show 0 < m; omega⟩) (b := ⟨1, by show 1 < m; omega⟩)
    (odd_cartanA m hm).1 (odd_cartanA m hm).2

theorem fourGroup_psp (n : ℕ) (hadm : StatedLieAdmissible .PSp n 3 1) (hne : n ≠ 2) :
    ∃ F : Subgroup (modelUniv .PSp n 3 1 Nat.prime_three).K, IsElemAbelian 2 F ∧
      Nat.card F = 4 ∧ F ⊓ Subgroup.center (modelUniv .PSp n 3 1 Nat.prime_three).K = ⊥ := by
  have hn : 3 ≤ n := by have := hadm.2.2.1; omega
  have hfin : Finite (modelUniv .PSp n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  exact fourGroup_of_nodes (Balance.exists_chevalleyExtras_model_nonSimplyLaced (p := 3) .PSp n 1
    (Or.inl ⟨rfl, by omega⟩)) (a := ⟨0, by show 0 < n; omega⟩) (b := ⟨1, by show 1 < n; omega⟩)
    (odd_cartanC n hn).1 (odd_cartanC n hn).2

theorem fourGroup_pOmegaOdd (n : ℕ) (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    ∃ F : Subgroup (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K, IsElemAbelian 2 F ∧
      Nat.card F = 4 ∧ F ⊓ Subgroup.center (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K = ⊥ := by
  have hn : 3 ≤ n := hadm.2.2.1
  have hfin : Finite (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  exact fourGroup_of_nodes
    (Balance.exists_chevalleyExtras_model_nonSimplyLaced (p := 3) .POmegaOdd n 1
      (Or.inr (Or.inl ⟨rfl, by omega⟩))) (a := ⟨0, by show 0 < n; omega⟩)
    (b := ⟨1, by show 1 < n; omega⟩) (odd_cartanB n hn).1 (odd_cartanB n hn).2

theorem fourGroup_pOmegaPlus (n : ℕ) (hadm : StatedLieAdmissible .POmegaPlus n 3 1) :
    ∃ F : Subgroup (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K, IsElemAbelian 2 F ∧
      Nat.card F = 4 ∧ F ⊓ Subgroup.center (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K = ⊥ := by
  have hn : 4 ≤ n := hadm.2.2
  have hfin : Finite (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  have hext := Balance.exists_chevalleyExtras_model (p := 3) .POmegaPlus n 1 hadm
    (Or.inr (Or.inl rfl))
  change ∃ F : Subgroup (ModelFacts.modelUniv .POmegaPlus n 3 1 Nat.prime_three).K,
    IsElemAbelian 2 F ∧ Nat.card F = 4 ∧
      F ⊓ Subgroup.center (ModelFacts.modelUniv .POmegaPlus n 3 1 Nat.prime_three).K = ⊥
  change (∃ x C O, ChevalleyExtras
    (ModelFacts.modelUniv .POmegaPlus n 3 1 Nat.prime_three).D (GaloisField 3 1) x C O) at hext
  change Finite (ModelFacts.modelUniv .POmegaPlus n 3 1 Nat.prime_three).K at hfin
  rw [ModelFacts.modelUniv_POmegaPlus (by omega)] at hext hfin ⊢
  exact fourGroup_of_nodes hext (a := ⟨0, by show 0 < n; omega⟩) (b := ⟨1, by show 1 < n; omega⟩)
    (odd_cartanD n hn).1 (odd_cartanD n hn).2

theorem fourGroup_e6 (n : ℕ) (hadm : StatedLieAdmissible .E6 n 3 1) :
    ∃ F : Subgroup (modelUniv .E6 n 3 1 Nat.prime_three).K, IsElemAbelian 2 F ∧
      Nat.card F = 4 ∧ F ⊓ Subgroup.center (modelUniv .E6 n 3 1 Nat.prime_three).K = ⊥ := by
  have hfin : Finite (modelUniv .E6 n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  exact fourGroup_of_nodes (Balance.exists_chevalleyExtras_model (p := 3) .E6 n 1 hadm
    (Or.inr (Or.inr (Or.inl rfl)))) (a := ⟨0, by show 0 < 6; omega⟩)
    (b := ⟨2, by show 2 < 6; omega⟩) (odd_cartanE 6 (by norm_num)).1
    (odd_cartanE 6 (by norm_num)).2

theorem fourGroup_e7 (n : ℕ) (hadm : StatedLieAdmissible .E7 n 3 1) :
    ∃ F : Subgroup (modelUniv .E7 n 3 1 Nat.prime_three).K, IsElemAbelian 2 F ∧
      Nat.card F = 4 ∧ F ⊓ Subgroup.center (modelUniv .E7 n 3 1 Nat.prime_three).K = ⊥ := by
  have hfin : Finite (modelUniv .E7 n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  exact fourGroup_of_nodes (Balance.exists_chevalleyExtras_model (p := 3) .E7 n 1 hadm
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (a := ⟨0, by show 0 < 7; omega⟩)
    (b := ⟨2, by show 2 < 7; omega⟩) (odd_cartanE 7 (by norm_num)).1
    (odd_cartanE 7 (by norm_num)).2

theorem modelFourGroup3On_split : ModelFourGroup3On fun t => t = .PSL ∨ t = .PSp ∨
    t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 := by
  intro t n ht _ hadm hne _
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fourGroup_psl n hadm
  · exact fourGroup_psp n hadm fun h => hne ⟨rfl, h⟩
  · exact fourGroup_pOmegaOdd n hadm
  · exact fourGroup_pOmegaPlus n hadm
  · exact fourGroup_e6 n hadm
  · exact fourGroup_e7 n hadm

end Model

end CFSG.ClassicalInvolution.Q3.Q3YS
