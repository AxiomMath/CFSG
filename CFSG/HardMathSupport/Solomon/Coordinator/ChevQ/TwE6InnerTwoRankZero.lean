module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont
public import CFSG.LieType.SeitzGeneration.ExcHigh.NativeCond
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoToral
public import CFSG.LieType.SeitzGeneration.HyperLeaf

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree


theorem twE6_hyperGen_of_rankZero (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hq : q % 3 = 2) (hq2 : q ≠ 2)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 3) (hNR : ¬ NormalizesRGroup (ringChar K) E₀)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hdiag : ∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) :
    HyperGen 3 ⊤ E₀ := by
  have hT : ∀ x ∈ E₀,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom := by
    intro x hx
    have hfix := twBase_twistHom_fix K σ q Fr hσ hFr (x : ModGL TwistTag.E6.tag K) x.2
    refine ⟨g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0, mem_twistedTorusOf.2 ⟨hdiag x hx, ?_⟩, ?_⟩
    · rw [map_mul, map_mul, map_inv, hfix, hg0]
      group
    · show g0 * _ * g0⁻¹ = _
      group
  exact twE6NegDatum_hyperGen q K σ hK hσ hq hq2 E₀ hE₀ hcard hNR Fr hFr v g0 hg0C hg0 hT hv

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
