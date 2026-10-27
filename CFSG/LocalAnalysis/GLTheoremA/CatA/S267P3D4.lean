module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ExcLift
import CFSG.RankThree.PartTwo.Census.Exceptional.Geck
import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeIso
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

theorem p3At_D4
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.D 4 Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  have hfin : ∀ d : TauCeti.ValidLieTypeIndex, Finite d.fixedField := fun _ => inferInstance
  haveI := hfin ⟨.D 4 Q, hv⟩
  obtain ⟨ι, hι, hcomm⟩ := CFSG.RankThree.PartTwo.Census.Exceptional.exists_commuting_rootSL2
    (K := TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 Q, hv⟩) .D4
    ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1], ![1, 1, 2, 1]] (by decide +kernel)
  let θ := (CFSG.HardMathSupport.Dickson.Bal207.D4Graph.isoAdj
      (TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 Q, hv⟩)).symm.trans
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 Q hv).symm
  exact H.false_of_commuting_SL2_fixedField e hchar (fun i => θ.toMonoidHom.comp (ι i))
    (fun i => θ.injective.comp (hι i)) (fun i j hij A B => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul, hcomm i j hij A B])

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
