module

public import CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialIrreducibleMatrixBasis
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness
public import CFSG.GroupTheory.CoprimeActionSupport.PrimeOrbitEquivariantSection
public import CFSG.LinearAlgebra.CoprimeActions.BasisPermutationCommutantDimension
public import CFSG.GroupTheory.CoprimeActionSupport.PrimeFixedFreeSpectrumArithmetic
public import CFSG.GroupTheory.CoprimeActionSupport.PrimePowerSuccessorFermat

public section


namespace CFSG

namespace LargeExtraspecial.RepresentationSupport

namespace ShultPrimeExtraspecialFixedFree


open ExtraspecialOddQuotientAutFaithfulness

open CFSG.LinearAlgebra.CoprimeActions CFSG.GroupTheory.CoprimeActionSupport


theorem conclusion {F : Type*} [Field F] [IsAlgClosed F]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] [Nontrivial W]
    {q : ℕ} (hq : q.Prime) (hqF : (q : F) ≠ 0)
    {E : Type*} [Group E] [Finite E] (hE : CFSG.IsExtraspecialPGroup q E)
    {d : ℕ} (hd : 0 < d) (hcard : Nat.card E = q ^ (1 + 2 * d))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ≠ q) (hrF : (r : F) ≠ 0)
    (σ : Representation F E W) (hfaith : Function.Injective σ) (hirr : σ.IsIrreducible)
    (α : MulAut E) (hαr : α ^ r = 1)
    (hαZ : ∀ z : Subgroup.center E, α (z : E) = z)
    (hfix : ∀ x : E ⧸ Subgroup.center E, quotientHom E α x = x ↔ x = 1)
    (T : W ≃ₗ[F] W) (hTr : T ^ r = 1)
    (hker : LinearMap.ker (T.toLinearMap - LinearMap.id) = ⊥)
    (hcov : ∀ e : E, T.toLinearMap ∘ₗ σ e = σ (α e) ∘ₗ T.toLinearMap) :
    q = 2 ∧ ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k := by
  classical
  obtain ⟨χ, hχ, hscalar⟩ :=
    IrreducibleCentralCharacter.exists_character σ hfaith hirr
  have hσ1 : (MulAut.toPerm _ (quotientHom E α)) ^ r = 1 := by
    rw [← map_pow, ← map_pow, hαr, map_one, map_one]
  have hτ1 : (MulAut.toPerm E α) ^ r = 1 := by
    rw [← map_pow, hαr, map_one]
  have hπ : ∀ y : E, (QuotientGroup.mk (MulAut.toPerm E α y) : E ⧸ Subgroup.center E) =
      (MulAut.toPerm _ (quotientHom E α)) (QuotientGroup.mk y) := by
    intro y
    exact (quotientHom_mk α y).symm
  obtain ⟨s, hs1, hs2, hs3⟩ := PrimeOrbitEquivariantSection.exists_section
    (QuotientGroup.mk : E → E ⧸ Subgroup.center E) QuotientGroup.mk_surjective
    (MulAut.toPerm _ (quotientHom E α)) (MulAut.toPerm E α) r hr hσ1 hτ1 hπ 1
    (fun x => hfix x) 1 rfl (map_one α)
  obtain ⟨b, hb⟩ := ExtraspecialIrreducibleMatrixBasis.exists_basis hq hE σ hirr χ hχ hscalar s hs1
  have hdim := ExtraspecialIrreducibleMatrixBasis.dimension_eq hq hE σ hirr χ hχ hscalar s hs1 hcard
  have hbT : ∀ i, T.toLinearMap ∘ₗ b i ∘ₗ T.symm.toLinearMap =
      b ((MulAut.toPerm _ (quotientHom E α)) i) := by
    intro i
    rw [hb, hb]
    have h := hcov (s i)
    have h2 := hs2 i
    show _ = σ (s ((MulAut.toPerm _ (quotientHom E α)) i))
    rw [hs2 i]
    show _ = σ (α (s i))
    rw [← LinearMap.comp_assoc, h, LinearMap.comp_assoc]
    ext v; simp
  have hform := BasisPermutationCommutantDimension.prime_formula b T
    (MulAut.toPerm _ (quotientHom E α)) hbT r hr hσ1 1 (fun x => hfix x)
  have hq2 : 2 ≤ q := hq.two_le
  have hW : 2 ≤ Module.finrank F W := by
    rw [hdim]
    calc 2 ≤ q := hq2
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ d := Nat.pow_le_pow_right hq.pos hd
  have hfin := PrimeFixedFreeSpectrumArithmetic.dimension_eq r hr hrF T hTr hker hW hform
  have hrd : r = q ^ d + 1 := by
    have := hr.two_le
    omega
  obtain ⟨h1, -, h3⟩ := PrimePowerSuccessorFermat.conclusion hq hr hr2 hd hrd
  exact ⟨h1, h3⟩


end ShultPrimeExtraspecialFixedFree

end LargeExtraspecial.RepresentationSupport

end CFSG
