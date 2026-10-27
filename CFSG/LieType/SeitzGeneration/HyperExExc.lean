module

public import CFSG.LieType.SeitzGeneration.HyperExParabolicUntw
public import CFSG.LieType.SeitzGeneration.HyperExParabolicTw
public import CFSG.LieType.SeitzGeneration.HyperExReeType

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbedding

theorem ExcCubeFor.union {P Q : TauCeti.LieTypeIndex → Prop} (hP : ExcCubeFor P)
    (hQ : ExcCubeFor Q) : ExcCubeFor fun d => P d ∨ Q d := by
  intro d p hp hp2 hpd hl hd hE
  rcases hd with h | h
  · exact hP d p hp hp2 hpd hl h hE
  · exact hQ d p hp hp2 hpd hl h hE

structure ExcCubeResiduals : Prop where
  g2 : ExcCubeFor IsG2Index
  f4 : ExcCubeFor IsF4Index
  e6 : ExcCubeFor IsE6Index
  e7 : ExcCubeFor IsE7Index
  e8 : ExcCubeFor IsE8Index
  triality : ExcCubeFor IsTrialityIndex
  twistedE6 : ExcCubeFor IsTwistedE6Index
  reeTypeThree : HyperExReeTypeThree

theorem hyperExFor_exc_of_residuals (h : ExcCubeResiduals) :
    HyperExFor fun d => ¬ IsClassicalIndex d.1 := by
  have hU : ExcCubeFor IsUntwistedExcIndex :=
    h.g2.union (h.f4.union (h.e6.union (h.e7.union h.e8)))
  have hT : ExcCubeFor IsTwistedExcIndex := h.triality.union h.twistedE6
  have hC := hyperExFor_or (hyperExFor_of_cube seitzExcParabolicHyperUntw hU)
    (hyperExFor_of_cube seitzExcParabolicHyperTw hT)
  exact HyperExFor.mono (fun d hd => ((not_isClassicalIndex_iff d.1).1 hd).imp id id)
    (hyperExFor_or hC (hyperExFor_reeType h.reeTypeThree))

end CFSG.LieType.SeitzGeneration
