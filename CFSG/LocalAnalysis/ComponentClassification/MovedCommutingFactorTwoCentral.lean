module

public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction

public section

open scoped commutatorElement

namespace CFSG.ComponentClassification.MovedCommutingFactorTwoCentral

theorem central {G : Type*} [Group G] [Finite G]
    (ambient factor acting : Subgroup G) (htwo : IsPGroup 2 acting) (hacting : acting ≤ factor)
    (hnormalizes : acting ≤ Subgroup.normalizer (ambient : Set G))
    (actor : G) (hactor : actor ∈ ambient)
    (hcommutes : ⁅factor, factor.map (MulAut.conj actor).toMonoidHom⁆ = ⊥)
    (hodd : Odd (Nat.card ↥(ambient ⊓ (factor ⊔ factor.map (MulAut.conj actor).toMonoidHom)))) :
    acting ≤ (Subgroup.center factor).map factor.subtype := by
  let image := acting.map (MulAut.conj actor).toMonoidHom
  let product := acting ⊔ image
  have himage : image ≤ factor.map (MulAut.conj actor).toMonoidHom := Subgroup.map_mono hacting
  have hproductTwo : IsPGroup 2 product := BlockTwoProductAction.two_join acting image htwo
    (htwo.map (MulAut.conj actor).toMonoidHom) (by
      apply le_antisymm _ bot_le
      rw [← hcommutes]
      exact Subgroup.commutator_mono hacting himage)
  have hproductBound : product ≤ factor ⊔ factor.map (MulAut.conj actor).toMonoidHom :=
    sup_le (hacting.trans le_sup_left) (himage.trans le_sup_right)
  have hbot := TwoActionOddIntersection.two_in_odd_eq_bot (ambient ⊓ product)
    (ambient ⊓ (factor ⊔ factor.map (MulAut.conj actor).toMonoidHom))
      (hproductTwo.to_le inf_le_right) hodd (inf_le_inf_left _ hproductBound)
  intro member hmember
  have hdisplacementAmbient : actor * member * actor⁻¹ * member⁻¹ ∈ ambient := by
    have hconjugate := (Subgroup.mem_normalizer_iff.mp (hnormalizes hmember) actor⁻¹).mp (ambient.inv_mem hactor)
    simpa only [mul_assoc] using ambient.mul_mem hactor hconjugate
  have hdisplacementProduct : actor * member * actor⁻¹ * member⁻¹ ∈ product :=
    product.mul_mem ((le_sup_right : image ≤ product) (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩))
      ((le_sup_left : acting ≤ product) (acting.inv_mem hmember))
  have hdisplacementOne := Subgroup.mem_bot.mp (hbot ▸
    (show actor * member * actor⁻¹ * member⁻¹ ∈ ambient ⊓ product from
      ⟨hdisplacementAmbient, hdisplacementProduct⟩))
  have heq : actor * member * actor⁻¹ = member := mul_inv_eq_one.mp hdisplacementOne
  have hmemberImage : member ∈ factor.map (MulAut.conj actor).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨member, hacting hmember, heq⟩
  have hcentral := Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes)
  apply Subgroup.mem_map.mpr
  refine ⟨⟨member, hacting hmember⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentral hmemberImage) other.val other.property)

end CFSG.ComponentClassification.MovedCommutingFactorTwoCentral
