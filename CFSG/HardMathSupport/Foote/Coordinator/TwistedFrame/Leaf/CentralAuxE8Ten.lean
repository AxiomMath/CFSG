module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.LieType.Steinberg.Adjoint

namespace DataE8Ten

@[expose] def words : Fin 3 → List (Fin Tag.E8.rank) := ![[6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7], [5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7], [4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7]]

theorem hmin : ∀ i, ∀ β ∈ rootFinset Tag.E8, β (iθ Tag.E8) = 0 → 0 < height β →
    0 < height ((words i).foldr (reflect Tag.E8) β) := by decide +kernel

theorem hperp : ∀ β ∈ rootFinset Tag.E8, β (iθ Tag.E8) = 0 → 0 < height β →
    (∀ i, ((words i).reverse.foldr (reflect Tag.E8) β) (iθ Tag.E8) = 0 ∧
      0 < height ((words i).reverse.foldr (reflect Tag.E8) β)) →
    ∀ j : Fin Tag.E8.rank, j.val ∉ ({0, 1, 2, 3} : Finset ℕ) → β j = 0 := by decide +kernel

theorem hS₁ : ∀ i, (words i).foldr (reflect Tag.E8) (highRoot Tag.E8) ∈ rootFinset Tag.E8 ∧
    ∀ j : Fin Tag.E8.rank, j.val ∈ ({0, 1, 2, 3} : Finset ℕ) →
      iform ((words i).foldr (reflect Tag.E8) (highRoot Tag.E8)) (Pi.single j 1) = 0 := by decide +kernel

theorem hdeg : ∀ i, ((words i).foldr (reflect Tag.E8) (highRoot Tag.E8)) (iθ Tag.E8) = 1 := by decide +kernel

theorem hwθ : TwClass.wordE8Ten.foldr (reflect Tag.E8) (highRoot Tag.E8) = highRoot Tag.E8 := by decide +kernel

theorem hwS₂ : ∀ α ∈ rootFinset Tag.E8, (∀ i : Fin Tag.E8.rank, i.val ∉ ({0, 1, 2, 3} : Finset ℕ) → α i = 0) →
    ∀ i : Fin Tag.E8.rank, i.val ∉ ({0, 1, 2, 3} : Finset ℕ) →
      ((TwClass.wordE8Ten).reverse.foldr (reflect Tag.E8) α) i = 0 := by decide +kernel

@[expose] def μ₀ : Fin Tag.E8.rank → ℤ := ![0, 0, 0, 0, 4, 3, 2, 1]
@[expose] def μ : Fin Tag.E8.rank → Fin 3 → ℤ := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, -1], ![-1, -1, 0], ![-1, 0, 0], ![0, 0, 0]]
@[expose] def Nf : Fin Tag.E8.rank → ℤ := ![1, 1, 1, 1, 1, 1, 1, 1]

theorem hNf : ∀ j : Fin Tag.E8.rank, j.val ∉ ({0, 1, 2, 3} : Finset ℕ) → Nf j ≠ 0 := by decide +kernel

theorem hμ : ∀ j : Fin Tag.E8.rank, j.val ∉ ({0, 1, 2, 3} : Finset ℕ) → ∀ l : Fin Tag.E8.rank,
    μ₀ j * iform (highRoot Tag.E8) (Pi.single l 1) +
      ∑ m, μ j m * iform ((words m).foldr (reflect Tag.E8) (highRoot Tag.E8)) (Pi.single l 1) =
        Nf j * (if l = j then 1 else 0) := by decide +kernel

@[expose] def U₀ : Fin Tag.E8.rank → ℤ := ![-1, 1, 0, 0, 0, 0, 0, 0]
@[expose] def U : Fin Tag.E8.rank → Fin 3 → ℤ := ![![-1, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 0, 0]]
@[expose] def N : ℤ := 1
@[expose] def W : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ := ![![2, -1, 1, 0, 0, 0, 0, 0], ![2, -1, 1, 0, 0, 0, 0, 0], ![3, -2, 2, 0, 0, 0, 0, 0], ![4, -3, 2, 0, 0, 0, 0, 0], ![3, -3, 1, -1, 0, 0, 0, 0], ![4, -2, 2, 0, 0, 0, 0, 0], ![2, -1, 1, 0, 0, 0, 0, 0], ![2, -1, 1, 0, 0, 0, 0, 0]]

theorem hN : N ≠ 0 := by decide +kernel

theorem hU : ∀ j l : Fin Tag.E8.rank, N * ((if j = l then 1 else 0) -
    (highRoot Tag.E8 j * U₀ l + ∑ m, ((words m).foldr (reflect Tag.E8) (highRoot Tag.E8)) j * U l m)) =
      ∑ i : Fin Tag.E8.rank, if i.val ∈ ({0, 1, 2, 3} : Finset ℕ) then W j i * Tag.E8.cartan i l else 0 := by
  decide +kernel

end DataE8Ten


theorem wS₂_e8Ten (α : Fin Tag.E8.rank → ℤ) (hα : IsRoot Tag.E8 α)
    (hs : ∀ i : Fin Tag.E8.rank, i.val ∉ ({0, 1, 2, 3} : Finset ℕ) → α i = 0) :
    IsRoot Tag.E8 (((coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten)⁻¹ • α) ∧
      ∀ i : Fin Tag.E8.rank, i.val ∉ ({0, 1, 2, 3} : Finset ℕ) →
        (((coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten)⁻¹ • α) i = 0 := by
  refine ⟨IsRoot.smul hα _, fun i hi => ?_⟩
  rw [wordProd_inv_smul_foldr]
  exact DataE8Ten.hwS₂ α (mem_rootFinset.2 hα) hs i hi

theorem twClassData_e8Ten : TwClassData TwClass.e8Ten := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • highRoot Tag.E8 = highRoot Tag.E8 := by
      rw [wordProd_smul_foldr]
      exact DataE8Ten.hwθ
    exact h
  · intro α hα
    exact wS₂_e8Ten α hα.1 hα.2
  · refine ⟨3, fun i => (coxeterSystem Tag.E8).wordProd (DataE8Ten.words i), ?_⟩
    exact leviDataFor_of_cert ({0, 1, 2, 3} : Finset ℕ) _ DataE8Ten.words DataE8Ten.hmin DataE8Ten.hperp
      (fun i => mem_S₁_of_orth TwClass.e8Ten (DataE8Ten.hS₁ i).1 (DataE8Ten.hS₁ i).2)
      DataE8Ten.hdeg DataE8Ten.μ₀ DataE8Ten.μ DataE8Ten.Nf DataE8Ten.hNf DataE8Ten.hμ
      DataE8Ten.U₀ DataE8Ten.U DataE8Ten.N DataE8Ten.hN DataE8Ten.W DataE8Ten.hU

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
