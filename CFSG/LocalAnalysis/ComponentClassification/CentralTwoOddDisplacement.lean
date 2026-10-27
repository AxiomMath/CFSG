module

public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.MappedCenter

public section

namespace CFSG.ComponentClassification.CentralTwoOddDisplacement

theorem centralizes {G : Type*} [Group G] [Finite G]
    (ambient first second acting : Subgroup G) (htwo : IsPGroup 2 acting)
    (hcontained : acting ≤ first) (hcentral : acting ≤ (Subgroup.center ambient).map ambient.subtype)
    (hnormalizes : acting ≤ Subgroup.normalizer (second : Set G))
    (actor : G) (hactor : actor ∈ second) (hactorAmbient : actor ∈ Subgroup.normalizer (ambient : Set G))
    (hodd : Odd (Nat.card ↥(second ⊓ (first ⊔ first.map (MulAut.conj actor).toMonoidHom)))) :
    actor ∈ Subgroup.centralizer (acting : Set G) := by
  let image := acting.map (MulAut.conj actor).toMonoidHom
  let product := acting ⊔ image
  have hcommutes : ⁅acting, image⁆ = ⊥ := MappedCenter.commute ambient acting image hcentral
    (MappedCenter.conjugate_le ambient acting hcentral actor hactorAmbient)
  have htwoProduct : IsPGroup 2 product := BlockTwoProductAction.two_join acting image htwo
    (htwo.map (MulAut.conj actor).toMonoidHom) hcommutes
  have hproductBound : product ≤ first ⊔ first.map (MulAut.conj actor).toMonoidHom :=
    sup_le (hcontained.trans le_sup_left) ((Subgroup.map_mono hcontained).trans le_sup_right)
  have hbot := TwoActionOddIntersection.two_in_odd_eq_bot (second ⊓ product)
    (second ⊓ (first ⊔ first.map (MulAut.conj actor).toMonoidHom)) (htwoProduct.to_le inf_le_right)
      hodd (inf_le_inf_left _ hproductBound)
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hdisplacementSecond : actor * member * actor⁻¹ * member⁻¹ ∈ second := by
    have hconjugate := (Subgroup.mem_normalizer_iff.mp (hnormalizes hmember) actor⁻¹).mp (second.inv_mem hactor)
    simpa only [mul_assoc] using second.mul_mem hactor hconjugate
  have hdisplacementProduct : actor * member * actor⁻¹ * member⁻¹ ∈ product :=
    product.mul_mem ((le_sup_right : image ≤ product) (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩))
      ((le_sup_left : acting ≤ product) (acting.inv_mem hmember))
  have hone := Subgroup.mem_bot.mp (hbot ▸
    (show actor * member * actor⁻¹ * member⁻¹ ∈ second ⊓ product from ⟨hdisplacementSecond, hdisplacementProduct⟩))
  have heq := mul_inv_eq_one.mp hone
  have hmul := congrArg (fun element : G => element * actor) heq
  simpa only [inv_mul_cancel_right] using hmul.symm

end CFSG.ComponentClassification.CentralTwoOddDisplacement
