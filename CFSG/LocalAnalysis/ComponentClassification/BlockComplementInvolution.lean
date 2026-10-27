module

public import CFSG.LocalAnalysis.ComponentClassification.CommutingOrbitFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.ComponentFamilyPumpUpFusion
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockComplementInvolution

theorem exists_fixed {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (element : G) (horder : orderOf element = 2)
    (helement : element ∈ UniversalOrbitBlock.normalizer component)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component) :
    ∃ member : G, orderOf member = 2 ∧
      member ∈ UniversalOrbitBlock.generated component ∧
      member ∈ Subgroup.centralizer {element} ∧
      member ∈ Subgroup.centralizer
        ((factor ⊔ UniversalOrbitBlock.conjugate factor element : Subgroup G) : Set G) ∧
      Subgroup.centralizer {member} ≤ UniversalOrbitBlock.normalizer component := by
  classical
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  let factors : Index → Subgroup G := Subtype.val
  let permutation : Index → Index := fun index =>
    ⟨UniversalOrbitBlock.conjugate index.val element,
      (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple element).mp
        helement index.val index.property⟩
  have hsquare : element * element = 1 := by
    rw [← pow_two, ← horder]
    exact pow_orderOf_eq_one element
  have hpermutation : Function.Involutive permutation := by
    intro index
    apply Subtype.ext
    change UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate index.val element) element = index.val
    rw [UniversalOrbitBlock.conjugate_conjugate, hsquare, UniversalOrbitBlock.conjugate_one]
  have hautomorphism : Function.Involutive (MulAut.conj element) := by
    intro member
    have hconjSquare : MulAut.conj element * MulAut.conj element = 1 := by rw [← map_mul, hsquare, map_one]
    exact congrArg (fun automorphism : MulAut G => automorphism member) hconjSquare
  have hfamilyEven : ∀ index : Index, Even (Nat.card (factors index)) :=
    fun index => UniversalOrbitBlock.orbit_even component heven index.val index.property.1
  have hfamilyCommutes : Pairwise (fun first second : Index => ⁅factors first, factors second⁆ = ⊥) := by
    intro first second hne
    exact UniversalOrbitBlock.block_commutes component heven huniversal first.val first.property
      second.val second.property (fun heq => hne (Subtype.ext heq))
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
  let first : Index := ⟨factor, hfactor⟩
  obtain ⟨other, hotherFirst, hotherSecond⟩ := ComponentFamilyPumpUpFusion.exists_outside_two
    hfamilyCard first (permutation first)
  obtain ⟨member, hmemberOrder, hmemberFixed, hmemberProduct, hmemberCentral⟩ :=
    CommutingOrbitFixedInvolution.outside_pair factors hfamilyEven hfamilyCommutes permutation
      hpermutation (MulAut.conj element) hautomorphism (fun _ => rfl)
      first other hotherFirst hotherSecond
  have hmemberM : member ∈ UniversalOrbitBlock.generated component :=
    (sup_le (CommutingComponentFamily.factor_le _ other.val other.property)
      (CommutingComponentFamily.factor_le _ (permutation other).val (permutation other).property)) hmemberProduct
  have hmemberCentralizer : member ∈ Subgroup.centralizer {element} := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change element * member * element⁻¹ = member at hmemberFixed
    calc
      member * element = (element * member * element⁻¹) * element := by rw [hmemberFixed]
      _ = element * member := by group
  have hmemberFactor : member ∈ Subgroup.centralizer (factor : Set G) :=
    Subgroup.centralizer_le (show (factor : Set G) ⊆
      ((factor ⊔ UniversalOrbitBlock.conjugate factor element : Subgroup G) : Set G) from
        (le_sup_left : factor ≤ factor ⊔ UniversalOrbitBlock.conjugate factor element)) hmemberCentral
  exact ⟨member, hmemberOrder, hmemberM, hmemberCentralizer, hmemberCentral,
    UniversalOrbitBlock.involution_centralizer_le component heven huniversal hquasisimple factor hfactor
      member hmemberOrder hmemberFactor⟩

end CFSG.ComponentClassification.BlockComplementInvolution
