module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CentralAuxData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.LieType.Steinberg.Adjoint

namespace DataF4Six

@[expose] def words : Fin 1 → List (Fin Tag.F4.rank) := ![[1, 2, 1, 3, 2, 1, 0]]

theorem hmin : ∀ i, ∀ β ∈ rootFinset Tag.F4, β (iθ Tag.F4) = 0 → 0 < height β →
    0 < height ((words i).foldr (reflect Tag.F4) β) := by decide +kernel

theorem hperp : ∀ β ∈ rootFinset Tag.F4, β (iθ Tag.F4) = 0 → 0 < height β →
    (∀ i, ((words i).reverse.foldr (reflect Tag.F4) β) (iθ Tag.F4) = 0 ∧
      0 < height ((words i).reverse.foldr (reflect Tag.F4) β)) →
    ∀ j : Fin Tag.F4.rank, j.val ∉ ({2, 3} : Finset ℕ) → β j = 0 := by decide +kernel

theorem hS₁ : ∀ i, (words i).foldr (reflect Tag.F4) (highRoot Tag.F4) ∈ rootFinset Tag.F4 ∧
    ∀ j : Fin Tag.F4.rank, j.val ∈ ({2, 3} : Finset ℕ) →
      iform ((words i).foldr (reflect Tag.F4) (highRoot Tag.F4)) (Pi.single j 1) = 0 := by decide +kernel

theorem hdeg : ∀ i, ((words i).foldr (reflect Tag.F4) (highRoot Tag.F4)) (iθ Tag.F4) = 1 := by decide +kernel

theorem hwθ : TwClass.wordF4.foldr (reflect Tag.F4) (highRoot Tag.F4) = highRoot Tag.F4 := by decide +kernel

theorem hwS₂ : ∀ α ∈ rootFinset Tag.F4, (∀ i : Fin Tag.F4.rank, i.val ∉ ({2, 3} : Finset ℕ) → α i = 0) →
    ∀ i : Fin Tag.F4.rank, i.val ∉ ({2, 3} : Finset ℕ) →
      ((TwClass.wordF4).reverse.foldr (reflect Tag.F4) α) i = 0 := by decide +kernel

@[expose] def μ₀ : Fin Tag.F4.rank → ℤ := ![1, 2, 0, 0]
@[expose] def μ : Fin Tag.F4.rank → Fin 1 → ℤ := ![![0], ![-1], ![0], ![0]]
@[expose] def Nf : Fin Tag.F4.rank → ℤ := ![2, 2, 1, 1]

theorem hNf : ∀ j : Fin Tag.F4.rank, j.val ∉ ({2, 3} : Finset ℕ) → Nf j ≠ 0 := by decide +kernel

theorem hμ : ∀ j : Fin Tag.F4.rank, j.val ∉ ({2, 3} : Finset ℕ) → ∀ l : Fin Tag.F4.rank,
    μ₀ j * iform (highRoot Tag.F4) (Pi.single l 1) +
      ∑ m, μ j m * iform ((words m).foldr (reflect Tag.F4) (highRoot Tag.F4)) (Pi.single l 1) =
        Nf j * (if l = j then 1 else 0) := by decide +kernel

@[expose] def U₀ : Fin Tag.F4.rank → ℤ := ![0, 1, 0, -1]
@[expose] def U : Fin Tag.F4.rank → Fin 1 → ℤ := ![![1], ![0], ![0], ![-1]]
@[expose] def N : ℤ := 1
@[expose] def W : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ := ![![0, 0, 1, 2], ![0, 0, 1, 2], ![0, 0, 2, 3], ![0, 0, 1, 2]]

theorem hN : N ≠ 0 := by decide +kernel

theorem hU : ∀ j l : Fin Tag.F4.rank, N * ((if j = l then 1 else 0) -
    (highRoot Tag.F4 j * U₀ l + ∑ m, ((words m).foldr (reflect Tag.F4) (highRoot Tag.F4)) j * U l m)) =
      ∑ i : Fin Tag.F4.rank, if i.val ∈ ({2, 3} : Finset ℕ) then W j i * Tag.F4.cartan i l else 0 := by
  decide +kernel

end DataF4Six


theorem wS₂_f4Six (α : Fin Tag.F4.rank → ℤ) (hα : IsRoot Tag.F4 α)
    (hs : ∀ i : Fin Tag.F4.rank, i.val ∉ ({2, 3} : Finset ℕ) → α i = 0) :
    IsRoot Tag.F4 (((coxeterSystem Tag.F4).wordProd TwClass.wordF4)⁻¹ • α) ∧
      ∀ i : Fin Tag.F4.rank, i.val ∉ ({2, 3} : Finset ℕ) →
        (((coxeterSystem Tag.F4).wordProd TwClass.wordF4)⁻¹ • α) i = 0 := by
  refine ⟨IsRoot.smul hα _, fun i hi => ?_⟩
  rw [wordProd_inv_smul_foldr]
  exact DataF4Six.hwS₂ α (mem_rootFinset.2 hα) hs i hi

theorem twClassData_f4Six : TwClassData TwClass.f4Six := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (coxeterSystem Tag.F4).wordProd TwClass.wordF4 • highRoot Tag.F4 = highRoot Tag.F4 := by
      rw [wordProd_smul_foldr]
      exact DataF4Six.hwθ
    exact h
  · intro α hα
    exact wS₂_f4Six α hα.1 hα.2
  · refine ⟨1, fun i => (coxeterSystem Tag.F4).wordProd (DataF4Six.words i), ?_⟩
    exact leviDataFor_of_cert ({2, 3} : Finset ℕ) _ DataF4Six.words DataF4Six.hmin DataF4Six.hperp
      (fun i => mem_S₁_of_orth TwClass.f4Six (DataF4Six.hS₁ i).1 (DataF4Six.hS₁ i).2)
      DataF4Six.hdeg DataF4Six.μ₀ DataF4Six.μ DataF4Six.Nf DataF4Six.hNf DataF4Six.hμ
      DataF4Six.U₀ DataF4Six.U DataF4Six.N DataF4Six.hN DataF4Six.W DataF4Six.hU

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
