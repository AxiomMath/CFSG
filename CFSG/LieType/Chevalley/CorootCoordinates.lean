module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.LieType.Chevalley.SimplyLacedCommutation

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem corootPair_eq_sum
    {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (δ : Fin τ.rank → ℤ) :
    corootPair β δ = ∑ i, δ i * corootPair β (Pi.single i 1) := by
  have hN := iform_self_pos_of_isRoot hβ
  have hδ : δ = ∑ i, δ i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : corootPair β δ * iform β β =
      (∑ i, δ i * corootPair β (Pi.single i 1)) * iform β β := by
    rw [corootPair_mul hβ, Finset.sum_mul]
    conv_lhs => rw [hδ, iform_finset_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iform_smul_right, mul_assoc, corootPair_mul hβ]
    ring
  exact mul_right_cancel₀ hN.ne' h1

end CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace CFSG.StandardType.LangRat

theorem j4e_rootChar_corootTuple
    {τ : Tag} {L : Type} [Field L] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (t : Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (fun j => t ^ corootPair γ (Pi.single j 1)) v = t ^ corootPair γ v := by
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.corootPair_eq_sum hγ v]
  simp only [rootChar, ← _root_.zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end CFSG.StandardType.LangRat

namespace CFSG.LieType.Chevalley

theorem corootPair_eq_iform_of_simplyLaced
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) :
    corootPair β v = iform β v := by
  have h2 : iform β β = 2 := by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ hβ
  rw [corootPair, h2]
  omega

end CFSG.LieType.Chevalley
