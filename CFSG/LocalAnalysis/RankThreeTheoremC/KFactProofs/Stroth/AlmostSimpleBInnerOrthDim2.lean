module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerOrthAbs
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

theorem oddPCoreInClosure_orthogonalGroup_of_finrank_le_two {K : Type} [Field K] [Finite K]
    [CharP K 2] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hd : Module.finrank K W ≤ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OddPCoreInClosure p ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  refine oddPCoreInClosure_of_hom hp hp2
    (CFSG.RankThree.OrthogonalInvolutions.dicksonHom R hR) fun g hg hg2 => ?_
  by_contra hne
  have hne' : (g : W ≃ₗ[K] W) ≠ 1 := fun h => hne (Subtype.ext h)
  have htt : (g : W ≃ₗ[K] W) * (g : W ≃ₗ[K] W) = 1 := by
    have h := congrArg Subtype.val hg2
    simpa [pow_two] using h
  have h1 := CFSG.RankThree.OrthogonalInvolutions.two_mul_finrank_commSpace_le htt
  have h2 := CFSG.RankThree.OrthogonalInvolutions.one_le_finrank_commSpace hne'
  have h3 : Module.finrank K
      (CFSG.RankThree.OrthogonalInvolutions.commSpace (g : W ≃ₗ[K] W)) = 1 := by omega
  rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_apply, h3] at hg
  have h4 := congrArg Multiplicative.toAdd hg
  simp only [toAdd_ofAdd, toAdd_one, Nat.cast_one] at h4
  exact absurd h4 (by decide)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
