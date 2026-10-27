module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreDatum
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddBender

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

section Certified


theorem qFixedRootSelector_oddLieType : QFixedRootSelector fun D _ => OddLieType D := by
  intro D _ _ _ hD n α J d
  obtain ⟨t, m, p, f, hp, hp2, hadm, hDm⟩ := hD
  set F := α.toMonoidHom.eqLocus (MonoidHom.id D) with hF
  let e : J.subgroupOf F ≃* J := Subgroup.subgroupOfEquivOfLe d.le_fixed
  exfalso
  rcases CFSG.ComponentClassification.CatLeafProof.gls3OddLieAutComponentsInput_holds D t m p f
      hp hp2 hadm hDm α d.orderOf_eq (J.subgroupOf F) d.isComponent with
    ⟨τ', n', f', hadm', hm'⟩ | ⟨-, -, -, hL⟩
  · exact u3NotOddLie d.model
      ⟨τ', n', p, f', hp, hp2, hadm', lieModel_quotient_center_of_mulEquiv e hm'⟩
  · refine OddBender.not_two_pow_six_dvd_card_of_lieModel_PSL_two_two_three
      (StdType.lieModel_of_mulEquiv e hL) ?_
    exact (pow_dvd_pow 2 (by have := d.two_le; omega : 6 ≤ 3 * n)).trans d.two_pow_dvd_card

end Certified

end CFSG.LocalAnalysis.EvenBN.GMSK
