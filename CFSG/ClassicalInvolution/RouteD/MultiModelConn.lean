module

public import CFSG.ClassicalInvolution.RouteD.MultiModelRoot

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Symplectic

section Nodes

theorem nodes_A {m : ℕ} (hm : 4 ≤ m) :
    ∃ ν : Fin m, ∀ i : Fin m, i = ν ∨ CartanMatrix.A m ν i = 0 ∨
      ∃ k : Fin m, CartanMatrix.A m ν k = 0 ∧ CartanMatrix.A m k i = 0 := by
  refine ⟨⟨0, by omega⟩, fun i => ?_⟩
  by_cases h0 : i.val = 0
  · exact Or.inl (Fin.ext h0)
  by_cases h1 : i.val = 1
  · refine Or.inr (Or.inr ⟨⟨3, by omega⟩, ?_, ?_⟩)
    · simp [CartanMatrix.A, Fin.ext_iff]
    · simp [CartanMatrix.A, Fin.ext_iff, h1]
  · refine Or.inr (Or.inl ?_)
    simp [CartanMatrix.A, Fin.ext_iff]
    omega

theorem nodes_D {n : ℕ} (hn : 5 ≤ n) :
    ∃ ν : Fin n, ∀ i : Fin n, i = ν ∨ cartanD n ν i = 0 ∨
      ∃ k : Fin n, cartanD n ν k = 0 ∧ cartanD n k i = 0 := by
  refine ⟨⟨0, by omega⟩, fun i => ?_⟩
  by_cases h0 : i.val = 0
  · exact Or.inl (Fin.ext h0)
  by_cases h1 : i.val = 1
  · refine Or.inr (Or.inr ⟨⟨3, by omega⟩, ?_, ?_⟩)
    · simp [cartanD, Fin.ext_iff]
      omega
    · simp [cartanD, Fin.ext_iff, h1]
      omega
  · refine Or.inr (Or.inl ?_)
    simp [cartanD, Fin.ext_iff]
    omega

theorem nodes_B {n : ℕ} (hn : 5 ≤ n) :
    ∃ ν : Fin n, ν.val + 1 < n ∧ ∀ i : Fin n, i = ν ∨ cartanB n ν i = 0 ∨
      ∃ k : Fin n, k.val + 1 < n ∧ cartanB n ν k = 0 ∧ cartanB n k i = 0 := by
  refine ⟨⟨0, by omega⟩, by simp; omega, fun i => ?_⟩
  by_cases h0 : i.val = 0
  · exact Or.inl (Fin.ext h0)
  by_cases h1 : i.val = 1
  · refine Or.inr (Or.inr ⟨⟨3, by omega⟩, by simp; omega, ?_, ?_⟩)
    · simp [cartanB, Fin.ext_iff]
    · simp [cartanB, Fin.ext_iff, h1]
  · refine Or.inr (Or.inl ?_)
    simp [cartanB, Fin.ext_iff]
    omega

theorem nodes_E6 : ∃ ν : Fin 6, ∀ i : Fin 6, i = ν ∨ CFSG.Blueprint.Chevalley.Tag.cartan .E6 ν i = 0 ∨
    ∃ k : Fin 6, CFSG.Blueprint.Chevalley.Tag.cartan .E6 ν k = 0 ∧
      CFSG.Blueprint.Chevalley.Tag.cartan .E6 k i = 0 := by
  refine ⟨0, fun i => ?_⟩
  fin_cases i
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl (by decide))
    | exact Or.inr (Or.inr ⟨1, by decide, by decide⟩)

theorem nodes_E7 : ∃ ν : Fin 7, ∀ i : Fin 7, i = ν ∨ CFSG.Blueprint.Chevalley.Tag.cartan .E7 ν i = 0 ∨
    ∃ k : Fin 7, CFSG.Blueprint.Chevalley.Tag.cartan .E7 ν k = 0 ∧
      CFSG.Blueprint.Chevalley.Tag.cartan .E7 k i = 0 := by
  refine ⟨0, fun i => ?_⟩
  fin_cases i
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl (by decide))
    | exact Or.inr (Or.inr ⟨1, by decide, by decide⟩)

theorem nodes_E8 : ∃ ν : Fin 8, ∀ i : Fin 8, i = ν ∨ CFSG.Blueprint.Chevalley.Tag.cartan .E8 ν i = 0 ∨
    ∃ k : Fin 8, CFSG.Blueprint.Chevalley.Tag.cartan .E8 ν k = 0 ∧
      CFSG.Blueprint.Chevalley.Tag.cartan .E8 k i = 0 := by
  refine ⟨0, fun i => ?_⟩
  fin_cases i
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl (by decide))
    | exact Or.inr (Or.inr ⟨1, by decide, by decide⟩)

end Nodes

section Models

variable {p : ℕ} [Fact p.Prime]

theorem commFamilyConnected_psl {n e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSL n p e)
    (hn : 5 ≤ n) : CommFamilyConnected (ModelFund p .PSL n e) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine commFamilyConnected_modelFund_of_nodes hp2 trivial hadm (by decide) (by decide) ?_
  obtain ⟨ν, hν⟩ := nodes_A (m := m) (by omega)
  exact ⟨ν, trivial, fun i => (hν i).imp_right fun h =>
    h.imp_right fun ⟨k, h1, h2⟩ => ⟨k, trivial, h1, h2⟩⟩

theorem commFamilyConnected_pOmegaPlus {n e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaPlus n p e) (hn : 5 ≤ n) :
    CommFamilyConnected (ModelFund p .POmegaPlus n e) := by
  refine commFamilyConnected_modelFund_of_nodes hp2 trivial hadm (by decide) (by decide) ?_
  have h3 : 3 ≤ n := by omega
  have h : modelUniv .POmegaPlus n p e Fact.out =
      ⟨spinGroup (quadPlus n (GaloisField p e)), plusDatum n (GaloisField p e) h3⟩ :=
    ModelFacts.modelUniv_POmegaPlus h3
  generalize modelUniv .POmegaPlus n p e Fact.out = L at h ⊢
  subst h
  obtain ⟨ν, hν⟩ := nodes_D hn
  exact ⟨ν, trivial, fun i => (hν i).imp_right fun h =>
    h.imp_right fun ⟨k, h1, h2⟩ => ⟨k, trivial, h1, h2⟩⟩

theorem commFamilyConnected_pOmegaOdd {n e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaOdd n p e) (hn : 5 ≤ n) :
    CommFamilyConnected (ModelFund p .POmegaOdd n e) := by
  refine commFamilyConnected_modelFund_of_nodes hp2 trivial hadm (by decide) (by decide) ?_
  obtain ⟨ν, hν, hcrit⟩ := nodes_B hn
  exact ⟨ν, hν, hcrit⟩

theorem commFamilyConnected_pOmegaMinus {n e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaMinus n p e) (hn : 6 ≤ n) :
    CommFamilyConnected (ModelFund p .POmegaMinus n e) := by
  refine commFamilyConnected_modelFund_of_nodes hp2 trivial hadm (by decide) (by decide) ?_
  obtain ⟨ν, hν, hcrit⟩ := nodes_B (n := n - 1) (by omega)
  refine ⟨ν, by have : ν.val + 1 < n - 1 := hν; show ν.val + 2 < n; omega, fun i => ?_⟩
  rcases hcrit i with h | h | ⟨k, hk, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨k, by have : k.val + 1 < n - 1 := hk; show k.val + 2 < n; omega, h1, h2⟩)

theorem commFamilyConnected_E6 {e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E6 0 p e) :
    CommFamilyConnected (ModelFund p .E6 0 e) := by
  refine commFamilyConnected_modelFund_of_nodes hp2 trivial hadm (by decide) (by decide) ?_
  obtain ⟨ν, hν⟩ := nodes_E6
  exact ⟨ν, trivial, fun i => (hν i).imp_right fun h =>
    h.imp_right fun ⟨k, h1, h2⟩ => ⟨k, trivial, h1, h2⟩⟩

theorem commFamilyConnected_E7 {e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E7 0 p e) :
    CommFamilyConnected (ModelFund p .E7 0 e) := by
  refine commFamilyConnected_modelFund_of_nodes hp2 trivial hadm (by decide) (by decide) ?_
  obtain ⟨ν, hν⟩ := nodes_E7
  exact ⟨ν, trivial, fun i => (hν i).imp_right fun h =>
    h.imp_right fun ⟨k, h1, h2⟩ => ⟨k, trivial, h1, h2⟩⟩

theorem commFamilyConnected_E8 {e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E8 0 p e) :
    CommFamilyConnected (ModelFund p .E8 0 e) := by
  refine commFamilyConnected_modelFund_of_nodes hp2 trivial hadm (by decide) (by decide) ?_
  obtain ⟨ν, hν⟩ := nodes_E8
  exact ⟨ν, trivial, fun i => (hν i).imp_right fun h =>
    h.imp_right fun ⟨k, h1, h2⟩ => ⟨k, trivial, h1, h2⟩⟩

end Models

end CFSG.ClassicalInvolution.RouteD
