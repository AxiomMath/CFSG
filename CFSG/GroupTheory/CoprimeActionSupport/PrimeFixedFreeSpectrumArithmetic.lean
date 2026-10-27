module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension
public import CFSG.LinearAlgebra.CoprimeActions.FiniteOrderSplitEigenspaceDecomposition
public import CFSG.GroupTheory.CoprimeActionSupport.ShultMultiplicityArithmetic

public section


namespace CFSG.GroupTheory.CoprimeActionSupport.PrimeFixedFreeSpectrumArithmetic


open Module Polynomial

open CFSG.LinearAlgebra.CoprimeActions


universe u


theorem dimension_eq {F : Type u} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (r : ℕ) (hr : r.Prime) (hrF : (r : F) ≠ 0) (T : V ≃ₗ[F] V) (hT : T ^ r = 1)
    (hker : LinearMap.ker (T.toLinearMap - LinearMap.id) = ⊥)
    (hN : 2 ≤ finrank F V)
    (hdim : r * finrank F (DistinctEigenspaceCommutantDimension.commutant T.toLinearMap) =
      finrank F V ^ 2 + r - 1) :
    finrank F V = r - 1 := by
  classical
  have hTr : T.toLinearMap ^ r = 1 := by
    have h2 : ∀ n : ℕ, T.toLinearMap ^ n = (T ^ n).toLinearMap := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, pow_succ, ih]; rfl
    rw [h2, hT]; rfl
  obtain ⟨I, _, _, lam, U, hinj, hint, hlam, hTU⟩ :=
    FiniteOrderSplitEigenspaceDecomposition.exists_decomposition r hr.pos hrF T.toLinearMap hTr
  haveI : NeZero (r : F) := ⟨hrF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F r
  have hcard : (nthRootsFinset r (1 : F)).card = r := hζ.card_nthRootsFinset
  set R : Finset F := nthRootsFinset r (1 : F) with hR
  have hmem : ∀ i, lam i ∈ R := fun i => by
    rw [hR, mem_nthRootsFinset hr.pos]; exact hlam i
  have h1R : (1 : F) ∈ R := by rw [hR, mem_nthRootsFinset hr.pos]; exact one_pow _
  let f : I → R := fun i => ⟨lam i, hmem i⟩
  have hf : Function.Injective f := fun i j h => hinj (congrArg Subtype.val h)
  let a' : R → ℕ := Function.extend f (fun i => finrank F (U i)) 0
  have ha'f : ∀ i, a' (f i) = finrank F (U i) := fun i => hf.extend_apply _ _ i
  have ha'0 : ∀ x, x ∉ Set.range f → a' x = 0 := fun x hx => by
    simp only [a']
    rw [Function.extend_apply' _ _ _ (by simpa using hx)]; rfl
  have hUi : ∀ i, lam i = 1 → finrank F (U i) = 0 := by
    intro i hi
    have : U i = ⊥ := by
      rw [eq_bot_iff, ← hker]
      intro u hu
      have := hTU i u hu
      simp [LinearMap.mem_ker, hi, this]
    rw [this]; simp
  have ha1 : a' ⟨1, h1R⟩ = 0 := by
    by_cases h : ⟨1, h1R⟩ ∈ Set.range f
    · obtain ⟨i, hi⟩ := h
      rw [← hi, ha'f]
      exact hUi i (congrArg Subtype.val hi)
    · exact ha'0 _ h
  have hcardR : Fintype.card R = r := by simpa using hcard
  let ψ0 : R ≃ Fin r := Fintype.equivFinOfCardEq hcardR
  let ψ : R ≃ Fin r := ψ0.trans (Equiv.swap (ψ0 ⟨1, h1R⟩) ⟨0, hr.pos⟩)
  have hψ : ψ ⟨1, h1R⟩ = ⟨0, hr.pos⟩ := by simp [ψ]
  let a : Fin r → ℕ := fun j => a' (ψ.symm j)
  have ha0 : a ⟨0, hr.pos⟩ = 0 := by
    simp only [a]; rw [← hψ]; simpa using ha1
  have hsum : ∑ j, a j = finrank F V := by
    have : ∑ j, a j = ∑ x : R, a' x := Equiv.sum_comp ψ.symm a'
    rw [this, ← DistinctEigenspaceCommutantDimension.sum_finrank_eq hint]
    exact (Fintype.sum_of_injective f hf (fun i => finrank F (U i)) a'
      (fun x hx => ha'0 x hx) (fun i => (ha'f i).symm)).symm
  have hsq : ∑ j, a j ^ 2 = finrank F (DistinctEigenspaceCommutantDimension.commutant T.toLinearMap) := by
    rw [DistinctEigenspaceCommutantDimension.finrank_eq hinj hint hTU]
    have : ∑ j, a j ^ 2 = ∑ x : R, a' x ^ 2 := Equiv.sum_comp ψ.symm (fun x => a' x ^ 2)
    rw [this]
    exact (Fintype.sum_of_injective f hf (fun i => finrank F (U i) ^ 2) (fun x => a' x ^ 2)
      (fun x hx => by rw [ha'0 x hx]; simp) (fun i => by rw [ha'f])).symm
  have hdim' : r * ∑ j, a j ^ 2 = (∑ j, a j) ^ 2 + r - 1 := by rw [hsq, hsum]; exact hdim
  rw [← hsum] at hN ⊢
  by_cases h2 : r = 2
  · subst h2
    exfalso
    simp only [Fin.sum_univ_two] at hdim' hN
    have h0 : a 0 = 0 := ha0
    rw [h0] at hdim' hN
    have hc : ∀ c : ℕ, c + 2 - 1 = c + 1 := by intro c; omega
    rw [hc] at hdim'
    nlinarith
  · exact ShultMultiplicityArithmetic.sum_eq_prime_sub_one hr h2 hN a ha0 rfl hdim'


end CFSG.GroupTheory.CoprimeActionSupport.PrimeFixedFreeSpectrumArithmetic
