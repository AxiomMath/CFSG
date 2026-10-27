module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MinusStmt

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD

@[expose] def D4PlaneInTorusMinus (p f : ℕ) (hp : p.Prime) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : Prop :=
  haveI : Fact p.Prime := ⟨hp⟩
  ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : IsAlgClosure K L) (_ : CharP L p)
    (g₀ : ModGL TwistTag.D4.tag L), D4MinusFrame p f L g₀ ∧
      ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ∀ e ∈ E,
        g₀⁻¹ * triEmb K σ L (β⁻¹ e) * g₀ ∈
          twistedTorusOf (trialityOpposition L)
            (twistHom TwistTag.D4 L (iterateFrobenius L p f))

end CFSG.GH74.GLS.Stage2.Bender.Thm1
