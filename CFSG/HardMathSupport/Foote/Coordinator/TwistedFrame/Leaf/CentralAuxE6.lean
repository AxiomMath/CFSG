module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.LieType.Steinberg.Adjoint

namespace DataE6Six

@[expose] def words : Fin 1 → List (Fin Tag.E6.rank) := ![[3, 2, 0, 4, 3, 2, 5, 4, 3, 1]]

theorem hmin : ∀ i, ∀ β ∈ rootFinset Tag.E6, β (iθ Tag.E6) = 0 → 0 < height β →
    0 < height ((words i).foldr (reflect Tag.E6) β) := by decide +kernel

theorem hperp : ∀ β ∈ rootFinset Tag.E6, β (iθ Tag.E6) = 0 → 0 < height β →
    (∀ i, ((words i).reverse.foldr (reflect Tag.E6) β) (iθ Tag.E6) = 0 ∧
      0 < height ((words i).reverse.foldr (reflect Tag.E6) β)) →
    ∀ j : Fin Tag.E6.rank, j.val ∉ ({0, 2, 4, 5} : Finset ℕ) → β j = 0 := by decide +kernel

theorem hS₁ : ∀ i, (words i).foldr (reflect Tag.E6) (highRoot Tag.E6) ∈ rootFinset Tag.E6 ∧
    ∀ j : Fin Tag.E6.rank, j.val ∈ ({0, 2, 4, 5} : Finset ℕ) →
      iform ((words i).foldr (reflect Tag.E6) (highRoot Tag.E6)) (Pi.single j 1) = 0 := by decide +kernel

theorem hdeg : ∀ i, ((words i).foldr (reflect Tag.E6) (highRoot Tag.E6)) (iθ Tag.E6) = 1 := by decide +kernel

theorem hwθ : TwClass.wordE6.foldr (reflect Tag.E6) (highRoot Tag.E6) = highRoot Tag.E6 := by decide +kernel

theorem hwS₂ : ∀ α ∈ rootFinset Tag.E6, (∀ i : Fin Tag.E6.rank, i.val ∉ ({0, 2, 4, 5} : Finset ℕ) → α i = 0) →
    ∀ i : Fin Tag.E6.rank, i.val ∉ ({0, 2, 4, 5} : Finset ℕ) →
      ((TwClass.wordE6).reverse.foldr (reflect Tag.E6) α) i = 0 := by decide +kernel

@[expose] def μ₀ : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 2, 0, 0]
@[expose] def μ : Fin Tag.E6.rank → Fin 1 → ℤ := ![![0], ![0], ![0], ![-1], ![0], ![0]]
@[expose] def Nf : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 1, 1, 1]

theorem hNf : ∀ j : Fin Tag.E6.rank, j.val ∉ ({0, 2, 4, 5} : Finset ℕ) → Nf j ≠ 0 := by decide +kernel

theorem hμ : ∀ j : Fin Tag.E6.rank, j.val ∉ ({0, 2, 4, 5} : Finset ℕ) → ∀ l : Fin Tag.E6.rank,
    μ₀ j * iform (highRoot Tag.E6) (Pi.single l 1) +
      ∑ m, μ j m * iform ((words m).foldr (reflect Tag.E6) (highRoot Tag.E6)) (Pi.single l 1) =
        Nf j * (if l = j then 1 else 0) := by decide +kernel

@[expose] def U₀ : Fin Tag.E6.rank → ℤ := ![1, 0, 0, 0, 0, 0]
@[expose] def U : Fin Tag.E6.rank → Fin 1 → ℤ := ![![-2], ![1], ![0], ![0], ![0], ![0]]
@[expose] def N : ℤ := 3
@[expose] def W : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ := ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![-3, 0, 0, 0, 0, 0], ![-6, 0, -3, 0, 0, 0], ![-4, 0, -2, 0, 2, 1], ![-2, 0, -1, 0, 1, 2]]

theorem hN : N ≠ 0 := by decide +kernel

theorem hU : ∀ j l : Fin Tag.E6.rank, N * ((if j = l then 1 else 0) -
    (highRoot Tag.E6 j * U₀ l + ∑ m, ((words m).foldr (reflect Tag.E6) (highRoot Tag.E6)) j * U l m)) =
      ∑ i : Fin Tag.E6.rank, if i.val ∈ ({0, 2, 4, 5} : Finset ℕ) then W j i * Tag.E6.cartan i l else 0 := by
  decide +kernel

end DataE6Six


theorem wS₂_e6Six (α : Fin Tag.E6.rank → ℤ) (hα : IsRoot Tag.E6 α)
    (hs : ∀ i : Fin Tag.E6.rank, i.val ∉ ({0, 2, 4, 5} : Finset ℕ) → α i = 0) :
    IsRoot Tag.E6 (((coxeterSystem Tag.E6).wordProd TwClass.wordE6)⁻¹ • α) ∧
      ∀ i : Fin Tag.E6.rank, i.val ∉ ({0, 2, 4, 5} : Finset ℕ) →
        (((coxeterSystem Tag.E6).wordProd TwClass.wordE6)⁻¹ • α) i = 0 := by
  refine ⟨IsRoot.smul hα _, fun i hi => ?_⟩
  rw [wordProd_inv_smul_foldr]
  exact DataE6Six.hwS₂ α (mem_rootFinset.2 hα) hs i hi

theorem twClassData_e6Six : TwClassData TwClass.e6Six := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • highRoot Tag.E6 = highRoot Tag.E6 := by
      rw [wordProd_smul_foldr]
      exact DataE6Six.hwθ
    exact h
  · intro α hα
    exact wS₂_e6Six α hα.1 hα.2
  · refine ⟨1, fun i => (coxeterSystem Tag.E6).wordProd (DataE6Six.words i), ?_⟩
    exact leviDataFor_of_cert ({0, 2, 4, 5} : Finset ℕ) _ DataE6Six.words DataE6Six.hmin DataE6Six.hperp
      (fun i => mem_S₁_of_orth TwClass.e6Six (DataE6Six.hS₁ i).1 (DataE6Six.hS₁ i).2)
      DataE6Six.hdeg DataE6Six.μ₀ DataE6Six.μ DataE6Six.Nf DataE6Six.hNf DataE6Six.hμ
      DataE6Six.U₀ DataE6Six.U DataE6Six.N DataE6Six.hN DataE6Six.W DataE6Six.hU

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
