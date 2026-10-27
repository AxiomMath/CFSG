module

public import CFSG.LocalAnalysis.ComponentClassification.ComponentFamilyPumpUpFusion
public import CFSG.LocalAnalysis.ComponentClassification.BlockFusion

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockProductFusion

theorem product_involution_mem {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (member : G) (hmember : member ∈ first ⊔ second) (horder : orderOf member = 2) :
    member ∈ BlockFusion.involutions component := by
  classical
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨other, hotherFirst, hotherSecond⟩ := ComponentFamilyPumpUpFusion.exists_outside_two
    hfamilyCard (⟨first, hfirst⟩ : Index) (⟨second, hsecond⟩ : Index)
  have hcentralizes : first ⊔ second ≤ Subgroup.centralizer (other.val : Set G) := by
    apply sup_le
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (UniversalOrbitBlock.block_commutes component heven huniversal first hfirst other.val other.property
          (fun heq => hotherFirst (Subtype.ext heq.symm)))
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (UniversalOrbitBlock.block_commutes component heven huniversal second hsecond other.val other.property
          (fun heq => hotherSecond (Subtype.ext heq.symm)))
  exact ⟨horder, other.val, other.property, hcentralizes hmember⟩

theorem intersection_odd {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second third fourth : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component)
    (hfourth : fourth ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component) :
    Odd (Nat.card ↥((first ⊔ second) ⊓
      (UniversalOrbitBlock.conjugate third actor ⊔ UniversalOrbitBlock.conjugate fourth actor))) := by
  apply Nat.not_even_iff_odd.mp
  intro hintersectionEven
  let intersection := (first ⊔ second) ⊓
    (UniversalOrbitBlock.conjugate third actor ⊔ UniversalOrbitBlock.conjugate fourth actor)
  obtain ⟨member, horder⟩ := exists_prime_orderOf_dvd_card' (G := intersection) 2
    (even_iff_two_dvd.mp hintersectionEven)
  have hambientOrder : orderOf member.val = 2 :=
    (orderOf_injective intersection.subtype intersection.subtype_injective member).trans horder
  have hbase := product_involution_mem component heven huniversal hcard first second hfirst hsecond
    member.val member.property.1 hambientOrder
  have himage : member.val ∈ (third ⊔ fourth).map (MulAut.conj actor).toMonoidHom := by
    rw [Subgroup.map_sup]
    exact member.property.2
  obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp himage
  have horiginalOrder : orderOf original = 2 :=
    (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective original).symm.trans
      ((congrArg orderOf heq).trans hambientOrder)
  have hconjugate := product_involution_mem component heven huniversal hcard third fourth hthird hfourth
    original horiginal horiginalOrder
  have hnormalizes := (BlockFusion.transporter_iff component heven huniversal hquasisimple original hconjugate actor).mp
    (by
      have heq' : (MulAut.conj actor) original = member.val := heq
      rwa [heq'])
  exact hactor hnormalizes

end CFSG.ComponentClassification.BlockProductFusion
