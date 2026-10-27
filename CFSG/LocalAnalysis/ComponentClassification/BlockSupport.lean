module

public import CFSG.LocalAnalysis.ComponentClassification.CommutingFamilySupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockProperSupportOdd
public import CFSG.LocalAnalysis.ComponentClassification.OddOrderCoordinates

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockSupport

@[expose] def family {G : Type*} [Group G] (component : Subgroup G) :
    ↥(UniversalOrbitBlock.block component) → Subgroup G := Subtype.val

theorem generated_eq {G : Type*} [Group G] (component : Subgroup G) :
    (⨆ index, family component index) = UniversalOrbitBlock.generated component :=
  (sSup_eq_iSup' (UniversalOrbitBlock.block component)).symm

theorem commutes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) :
    Pairwise (fun first second => ∀ left right : G,
      left ∈ family component first → right ∈ family component second → Commute left right) := by
  intro first second hdistinct left right hleft hright
  have hcommutator := UniversalOrbitBlock.block_commutes component heven huniversal
    first.val first.property second.val second.property (fun heq => hdistinct (Subtype.ext heq))
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutator hleft) right hright).symm

theorem subproduct_eq {G : Type*} [Group G] (component : Subgroup G)
    (subset : Set (Subgroup G)) (hsubset : subset ⊆ UniversalOrbitBlock.block component) :
    CommutingFamilySupport.subproduct (family component) {index | index.val ∈ subset} = sSup subset := by
  apply le_antisymm
  · exact iSup_le (fun index => iSup_le (fun hindex => le_sSup hindex))
  · exact sSup_le (fun factor hfactor =>
      le_iSup_of_le (⟨factor, hsubset hfactor⟩ : ↥(UniversalOrbitBlock.block component))
        (le_iSup_of_le hfactor le_rfl))

theorem subgroup_le {G : Type*} [Group G] (component : Subgroup G)
    (subset : Set (Subgroup G)) (hsubset : subset ⊆ UniversalOrbitBlock.block component) :
    BlockProperSupportOdd.subgroup component subset ≤ UniversalOrbitBlock.generated component :=
  sup_le (sSup_le_sSup hsubset) (MappedCenter.contained _)

@[expose] def support {G : Type*} [Group G] (component : Subgroup G) (member : G) : Set (Subgroup G) :=
  {factor | factor ∈ UniversalOrbitBlock.block component ∧ member ∉ Subgroup.centralizer (factor : Set G)}

theorem support_le {G : Type*} [Group G] (component : Subgroup G) (member : G) :
    support component member ⊆ UniversalOrbitBlock.block component := fun _ hfactor => hfactor.1

theorem support_inv {G : Type*} [Group G] (component : Subgroup G) (member : G) :
    support component member⁻¹ = support component member := by
  ext factor
  exact and_congr_right (fun _ => not_congr (Subgroup.inv_mem_iff _))

theorem support_mul {G : Type*} [Group G] (component : Subgroup G) (first second : G) :
    support component (first * second) ⊆ support component first ∪ support component second := by
  intro factor hfactor
  by_contra hnot
  have hfirst : first ∈ Subgroup.centralizer (factor : Set G) := by
    by_contra hfirstNot
    exact hnot (Or.inl ⟨hfactor.1, hfirstNot⟩)
  have hsecond : second ∈ Subgroup.centralizer (factor : Set G) := by
    by_contra hsecondNot
    exact hnot (Or.inr ⟨hfactor.1, hsecondNot⟩)
  exact hfactor.2 ((Subgroup.centralizer (factor : Set G)).mul_mem hfirst hsecond)

theorem support_conjugate {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (actor : G) (hactor : actor ∈ UniversalOrbitBlock.normalizer component) (member : G) :
    support component ((MulAut.conj actor) member) =
      (fun factor => UniversalOrbitBlock.conjugate factor actor) '' support component member := by
  ext factor
  constructor
  · intro hfactor
    let original := UniversalOrbitBlock.conjugate factor actor⁻¹
    have horiginal : original ∈ UniversalOrbitBlock.block component :=
      (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple actor⁻¹).mp
        ((UniversalOrbitBlock.normalizer component).inv_mem hactor) factor hfactor.1
    have hback : UniversalOrbitBlock.conjugate original actor = factor := by
      dsimp only [original]
      rw [UniversalOrbitBlock.conjugate_conjugate, mul_inv_cancel, UniversalOrbitBlock.conjugate_one]
    refine ⟨original, ⟨horiginal, ?_⟩, hback⟩
    have htransport := CommutingFamilySupport.centralizer_transport (MulAut.conj actor) original member
    change (MulAut.conj actor) member ∈ Subgroup.centralizer (UniversalOrbitBlock.conjugate original actor : Set G) ↔ _ at htransport
    rw [hback] at htransport
    exact hfactor.2 ∘ htransport.mpr
  · rintro ⟨original, horiginal, rfl⟩
    refine ⟨(UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple actor).mp
      hactor original horiginal.1, ?_⟩
    exact horiginal.2 ∘ (CommutingFamilySupport.centralizer_transport (MulAut.conj actor) original member).mp

theorem support_subproduct {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (subset : Set (Subgroup G)) (hsubset : subset ⊆ UniversalOrbitBlock.block component)
    (member : UniversalOrbitBlock.generated component) :
    support component member.val ⊆ subset ↔ member.val ∈ BlockProperSupportOdd.subgroup component subset := by
  classical
  let : Fintype ↥(UniversalOrbitBlock.block component) := Fintype.ofFinite _
  let lift : ↥(⨆ index, family component index) :=
    ⟨member.val, (generated_eq component).symm ▸ member.property⟩
  have hsupport := CommutingFamilySupport.support_subproduct (family component)
    (commutes component heven huniversal) {index | index.val ∈ subset} lift
  change (∀ index : ↥(UniversalOrbitBlock.block component),
      member.val ∉ Subgroup.centralizer (index.val : Set G) → index.val ∈ subset) ↔
    member.val ∈ CommutingFamilySupport.subproduct (family component) {index | index.val ∈ subset} ⊔
      (Subgroup.center ↥(⨆ index, family component index)).map (⨆ index, family component index).subtype at hsupport
  rw [subproduct_eq component subset hsubset, generated_eq component] at hsupport
  constructor
  · intro hcontained
    exact hsupport.mp (fun index hindex => hcontained ⟨index.property, hindex⟩)
  · intro hmember factor hfactor
    exact hsupport.mpr hmember ⟨factor, hfactor.1⟩ hfactor.2

theorem support_pair {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (first second : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (member : UniversalOrbitBlock.generated component) (hmember : member.val ∈ first ⊔ second) :
    support component member.val ⊆ {first, second} := by
  have hsubset : ({first, second} : Set (Subgroup G)) ⊆ UniversalOrbitBlock.block component := by
    intro factor hfactor
    rcases hfactor with rfl | hfactor
    · exact hfirst
    · exact (Set.mem_singleton_iff.mp hfactor) ▸ hsecond
  apply (support_subproduct component heven huniversal {first, second} hsubset member).mpr
  apply Subgroup.mem_sup_left
  simpa only [sSup_pair] using hmember

theorem invariant_normalizes {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (subset : Set (Subgroup G)) (hsubset : subset ⊆ UniversalOrbitBlock.block component)
    (acting : Subgroup G) (hnormalizes : acting ≤ UniversalOrbitBlock.normalizer component)
    (hinvariant : ∀ actor ∈ acting,
      (fun factor => UniversalOrbitBlock.conjugate factor actor) '' subset = subset) :
    acting ≤ Subgroup.normalizer (BlockProperSupportOdd.subgroup component subset : Set G) := by
  apply Subgroup.le_set_normalizer_iff.mpr
  intro actor hactor member hmember
  let original : UniversalOrbitBlock.generated component := ⟨member, subgroup_le component subset hsubset hmember⟩
  let moved : UniversalOrbitBlock.generated component := ⟨(MulAut.conj actor) member,
    (Subgroup.mem_normalizer_iff.mp (hnormalizes hactor) member).mp original.property⟩
  apply (support_subproduct component heven huniversal subset hsubset moved).mp
  have horiginalSupport := (support_subproduct component heven huniversal subset hsubset original).mpr hmember
  change support component ((MulAut.conj actor) member) ⊆ subset
  rw [support_conjugate component heven huniversal hquasisimple actor (hnormalizes hactor) member,
    ← hinvariant actor hactor]
  exact Set.image_mono horiginalSupport

@[expose] noncomputable def coordinates {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) :
    UniversalOrbitBlock.generated component →*
      ((index : ↥(UniversalOrbitBlock.block component)) → index.val ⧸ Subgroup.center index.val) :=
  letI : Fintype ↥(UniversalOrbitBlock.block component) := Fintype.ofFinite _
  (CommutingFamilyCentralQuotient.coordinates (family component) (commutes component heven huniversal)).comp
    (MulEquiv.subgroupCongr (generated_eq component).symm).toMonoidHom

theorem coordinates_eq_one_iff {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (member : UniversalOrbitBlock.generated component) (index : ↥(UniversalOrbitBlock.block component)) :
    coordinates component heven huniversal member index = 1 ↔
      member.val ∈ Subgroup.centralizer (index.val : Set G) := by
  classical
  let : Fintype ↥(UniversalOrbitBlock.block component) := Fintype.ofFinite _
  exact CommutingFamilyCentralQuotient.coordinates_eq_one_iff (family component)
    (commutes component heven huniversal) ((MulEquiv.subgroupCongr (generated_eq component).symm) member) index

theorem support_coordinates {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (member : UniversalOrbitBlock.generated component) (index : ↥(UniversalOrbitBlock.block component)) :
    index.val ∈ support component member.val ↔ coordinates component heven huniversal member index ≠ 1 := by
  exact (and_iff_right index.property).trans (not_congr (coordinates_eq_one_iff component heven huniversal member index).symm)

theorem support_eq_of_odd_displacement {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (first second : UniversalOrbitBlock.generated component)
    (hfirst : first.val ^ 2 = 1) (hsecond : second.val ^ 2 = 1)
    (hodd : Odd (orderOf (first.val⁻¹ * second.val))) :
    support component first.val = support component second.val := by
  have hfirstSquare : first ^ 2 = 1 := Subtype.ext hfirst
  have hsecondSquare : second ^ 2 = 1 := Subtype.ext hsecond
  have hoddLocal : Odd (orderOf (first⁻¹ * second)) := by
    have heq := orderOf_injective (UniversalOrbitBlock.generated component).subtype
      (UniversalOrbitBlock.generated component).subtype_injective (first⁻¹ * second)
    exact heq ▸ hodd
  ext factor
  by_cases hfactor : factor ∈ UniversalOrbitBlock.block component
  · let index : ↥(UniversalOrbitBlock.block component) := ⟨factor, hfactor⟩
    let homomorphism := (Pi.evalMonoidHom
      (fun index : ↥(UniversalOrbitBlock.block component) => index.val ⧸ Subgroup.center index.val) index).comp
        (coordinates component heven huniversal)
    rw [support_coordinates component heven huniversal first index,
      support_coordinates component heven huniversal second index]
    exact not_congr (OddOrderCoordinates.equal homomorphism first second hfirstSquare hsecondSquare hoddLocal)
  · change (factor ∈ UniversalOrbitBlock.block component ∧ _) ↔ (factor ∈ UniversalOrbitBlock.block component ∧ _)
    simp only [hfactor, false_and]

theorem support_eq_of_odd_two_displacement {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (first second : UniversalOrbitBlock.generated component) (firstExponent secondExponent : ℕ)
    (hfirst : first.val ^ (2 ^ firstExponent) = 1) (hsecond : second.val ^ (2 ^ secondExponent) = 1)
    (hodd : Odd (orderOf (first.val⁻¹ * second.val))) :
    support component first.val = support component second.val := by
  have hfirstPower : first ^ (2 ^ firstExponent) = 1 := Subtype.ext hfirst
  have hsecondPower : second ^ (2 ^ secondExponent) = 1 := Subtype.ext hsecond
  have hoddLocal : Odd (orderOf (first⁻¹ * second)) :=
    (orderOf_injective (UniversalOrbitBlock.generated component).subtype
      (UniversalOrbitBlock.generated component).subtype_injective (first⁻¹ * second)) ▸ hodd
  ext factor
  by_cases hfactor : factor ∈ UniversalOrbitBlock.block component
  · let index : ↥(UniversalOrbitBlock.block component) := ⟨factor, hfactor⟩
    let homomorphism := (Pi.evalMonoidHom
      (fun index : ↥(UniversalOrbitBlock.block component) => index.val ⧸ Subgroup.center index.val) index).comp
        (coordinates component heven huniversal)
    rw [support_coordinates component heven huniversal first index,
      support_coordinates component heven huniversal second index]
    exact not_congr (OddOrderCoordinates.equal_two_power homomorphism first second firstExponent secondExponent
      hfirstPower hsecondPower hoddLocal)
  · change (factor ∈ UniversalOrbitBlock.block component ∧ _) ↔ (factor ∈ UniversalOrbitBlock.block component ∧ _)
    simp only [hfactor, false_and]

end CFSG.ComponentClassification.BlockSupport
