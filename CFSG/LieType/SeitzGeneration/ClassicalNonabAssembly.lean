module

public import CFSG.LieType.SeitzGeneration.UnitaryNonabMain
public import CFSG.LieType.SeitzGeneration.HeisTorusGen

public section

namespace CFSG.LieType.SeitzGeneration

theorem seitzInnerUnitaryNonab_p5 :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ 5 ≤ p ∧ IsUnitaryIndex' d.1 ∧ ¬ CentralPrimeFree p d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp5, ⟨m, q, hd⟩, hlift⟩
  subst hd
  exact planeGen_inner_unitary_nonab_p hv hp hp5 (by simpa [CentralPrimeFree] using hlift) hE hc
    hinner

theorem seitzInnerClassicalNonab_of_halves
    (hL : SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ 5 ≤ p ∧ IsLinearIndex d.1 ∧ ¬ CentralPrimeFree p d.1)
    (hU : SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ 5 ≤ p ∧ IsUnitaryIndex' d.1 ∧ ¬ CentralPrimeFree p d.1) :
    SeitzInnerClassicalNonab :=
  SeitzPlanes.of_cover (fun d p _ _ E ⟨hE, h5, _, hf⟩ => by
    obtain ⟨d, hv⟩ := d
    cases d with
    | A m q => exact Or.inl ⟨hE, h5, ⟨m, q, rfl⟩, hf⟩
    | twistedA m q => exact Or.inr ⟨hE, h5, ⟨m, q, rfl⟩, hf⟩
    | _ => exact absurd trivial hf) hL hU

theorem seitzInnerClassicalNonab_holds : SeitzInnerClassicalNonab :=
  seitzInnerClassicalNonab_of_halves seitzInnerLinearNonab_holds seitzInnerUnitaryNonab_p5

end CFSG.LieType.SeitzGeneration
