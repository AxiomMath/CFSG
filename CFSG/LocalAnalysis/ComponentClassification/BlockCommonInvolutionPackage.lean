module

public import CFSG.LocalAnalysis.ComponentClassification.BlockCommonInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockCommonInvolutionPair

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockCommonInvolutionPackage

structure Common {G : Type*} [Group G] (component opposite : Subgroup G)
    (rank : ℕ) (elementary : Subgroup G) : Prop where
  isElementary : IsElemAbelian 2 elementary
  card : Nat.card elementary = 2 ^ rank
  contained : ∀ factor ∈ UniversalOrbitBlock.block component, elementary ≤ factor ⊓ opposite
  involutions : ∀ factor ∈ UniversalOrbitBlock.block component, ∀ member : G,
    member ∈ factor ⊓ opposite ∧ orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1
  central : elementary ≤ (Subgroup.center (UniversalOrbitBlock.generated component)).map
    (UniversalOrbitBlock.generated component).subtype
  normalizes : UniversalOrbitBlock.normalizer component ⊓ opposite ≤ Subgroup.normalizer (elementary : Set G)
  omega : ∀ factor ∈ UniversalOrbitBlock.block component, ∀ sylow : Sylow 2 ↥(factor ⊓ opposite),
    InvolutionGeneratedSubgroup.omega ((sylow : Subgroup ↥(factor ⊓ opposite)).map (factor ⊓ opposite).subtype) = elementary

theorem common {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (opposite : Subgroup G) (rank : ℕ) (elementary : Subgroup G)
    (helementary : IsElemAbelian 2 elementary) (hsize : Nat.card elementary = 2 ^ rank)
    (hcontained : ∀ factor ∈ UniversalOrbitBlock.block component, elementary ≤ factor ⊓ opposite)
    (hcharacterization : ∀ factor ∈ UniversalOrbitBlock.block component, ∀ member : G,
      member ∈ factor ⊓ opposite ∧ orderOf member = 2 ↔ member ∈ elementary ∧ member ≠ 1)
    (hnormal : UniversalOrbitBlock.normalizer component ⊓ opposite ≤ Subgroup.normalizer (elementary : Set G)) :
    Common component opposite rank elementary := by
  have hfactorContained : ∀ factor ∈ UniversalOrbitBlock.block component, elementary ≤ factor :=
    fun factor hfactor => (hcontained factor hfactor).trans inf_le_left
  refine ⟨helementary, hsize, hcontained, hcharacterization,
    BlockCommonInvolutionStructure.central_generated component heven huniversal hcard elementary hfactorContained,
    hnormal, ?_⟩
  intro factor hfactor sylow
  exact BlockCommonInvolutionStructure.omega_sylow (factor ⊓ opposite) elementary helementary
    (hcontained factor hfactor)
    ((BlockCommonInvolutionStructure.centralizes_factors component heven huniversal hcard elementary hfactorContained
      factor hfactor).trans (Subgroup.centralizer_le (show (factor ⊓ opposite : Subgroup G) ≤ factor from inf_le_left)))
    (fun member hmember horder => ((hcharacterization factor hfactor member).mp ⟨hmember, horder⟩).1) sylow

theorem Common.nontrivial {G : Type*} [Group G] [Finite G]
    {component opposite elementary : Subgroup G} {rank : ℕ}
    (properties : Common component opposite rank elementary) (hpositive : 1 ≤ rank) : Nontrivial elementary := by
  apply elementary.nontrivial_iff_ne_bot.mpr
  intro hbot
  have hcardOne := (Subgroup.card_eq_one).mpr hbot
  rw [properties.card] at hcardOne
  exact (ne_of_gt (Nat.one_lt_pow (by omega : rank ≠ 0) (by omega : 1 < 2))) hcardOne

theorem Common.factor_center {G : Type*} [Group G] [Finite G]
    {component opposite elementary : Subgroup G} {rank : ℕ}
    (properties : Common component opposite rank elementary)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component) :
    elementary ≤ (Subgroup.center factor).map factor.subtype := by
  have hcontained : ∀ factor ∈ UniversalOrbitBlock.block component, elementary ≤ factor :=
    fun factor hfactor => (properties.contained factor hfactor).trans inf_le_left
  have hcentralizes := BlockCommonInvolutionStructure.centralizes_factors component heven huniversal hcard
    elementary hcontained factor hfactor
  intro member hmember
  apply Subgroup.mem_map.mpr
  refine ⟨⟨member, hcontained factor hfactor hmember⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentralizes hmember) other.val other.property)

theorem Common.normal {G : Type*} [Group G]
    {component opposite elementary : Subgroup G} {rank : ℕ}
    (properties : Common component opposite rank elementary) :
    (elementary.subgroupOf (UniversalOrbitBlock.normalizer component ⊓ opposite)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer properties.normalizes

theorem Common.rank {G : Type*} [Group G] [Finite G]
    {component opposite elementary : Subgroup G} {rank : ℕ}
    (properties : Common component opposite rank elementary)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component) :
    pRank 2 (factor ⊓ opposite) = rank := by
  apply le_antisymm
  · obtain ⟨witness, hcontained, helementary, hsize⟩ := TwoRankTransport.witness (factor ⊓ opposite)
    have hle : witness ≤ elementary := by
      intro member hmember
      by_cases hone : member = 1
      · rw [hone]
        exact elementary.one_mem
      · exact ((properties.involutions factor hfactor member).mp
          ⟨hcontained hmember, orderOf_eq_prime (helementary.2 member hmember) hone⟩).1
    have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [hsize, properties.card] at hcard
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard
  · exact TwoRankTransport.rank_le (factor ⊓ opposite) elementary (properties.contained factor hfactor)
      properties.isElementary rank properties.card

theorem Common.omega_subgroup {G : Type*} [Group G] [Finite G]
    {component opposite elementary : Subgroup G} {rank : ℕ}
    (properties : Common component opposite rank elementary)
    (heven : Even (Nat.card component)) (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component)
    (subgroup : Subgroup G) (hcontained : elementary ≤ subgroup) (hsubgroup : subgroup ≤ factor ⊓ opposite)
    (sylow : Sylow 2 subgroup) :
    InvolutionGeneratedSubgroup.omega ((sylow : Subgroup subgroup).map subgroup.subtype) = elementary := by
  have hfactorContained : ∀ factor ∈ UniversalOrbitBlock.block component, elementary ≤ factor :=
    fun factor hfactor => (properties.contained factor hfactor).trans inf_le_left
  have hcentralizes := BlockCommonInvolutionStructure.centralizes_factors component heven huniversal hcard
    elementary hfactorContained factor hfactor
  exact BlockCommonInvolutionStructure.omega_sylow subgroup elementary properties.isElementary hcontained
    (hcentralizes.trans (Subgroup.centralizer_le (hsubgroup.trans inf_le_left)))
      (fun member hmember horder => ((properties.involutions factor hfactor member).mp
        ⟨hsubgroup hmember, horder⟩).1) sylow

theorem exists_pair {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (element : G) (helement : element ∈ BlockFusion.involutions component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (himage : (MulAut.conj actor) element ∈ UniversalOrbitBlock.normalizer component) :
    ∃ rank : ℕ, 1 ≤ rank ∧ ∃ firstCommon secondCommon : Subgroup G,
      Common component ((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) rank firstCommon ∧
      Common (UniversalOrbitBlock.conjugate component actor) (UniversalOrbitBlock.normalizer component) rank secondCommon ∧
      Disjoint firstCommon secondCommon ∧ ⁅firstCommon, secondCommon⁆ = ⊥ ∧
      (∀ factor ∈ UniversalOrbitBlock.block component,
        factor ⊓ Subgroup.centralizer (secondCommon : Set G) =
          factor ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ∧
        ∀ member ∈ secondCommon, member ≠ 1 → factor ⊓ Subgroup.centralizer {member} =
          factor ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) := by
  have hself := UniversalOrbitBlock.mem_block_self component
  let rank := pRank 2 (component ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)
  have hpositive : 1 ≤ rank := BlockCommonRank.positive component heven huniversal hquasisimple hcard hcontrol
    element helement actor hactor himage component component hself hself
  have hmutualEven := fun first hfirst second hsecond =>
    BlockMutualNormalizers.even component heven huniversal hquasisimple hcard hcontrol
      element helement actor hactor himage first second hfirst hsecond
  obtain ⟨firstCommon, hfirstElementary, hfirstSize, hfirstContained, hfirstInvolutions⟩ :=
    BlockCommonInvolutions.left component heven huniversal hquasisimple hcard hcontrol actor hactor hmutualEven
      component hself
  obtain ⟨secondCommon, hsecondElementary, hsecondSize, hsecondContained, hsecondInvolutions⟩ :=
    BlockCommonInvolutions.right component heven huniversal hquasisimple hcard hcontrol actor hactor hmutualEven
      component hself
  have hfirstNormal := BlockCommonInvolutionStructure.normalizes_common component heven huniversal hquasisimple actor
    firstCommon hfirstElementary hfirstContained hfirstInvolutions
  have hsecondNormal := BlockCommonInvolutionPair.image_normalizes component heven huniversal hquasisimple actor
    secondCommon hsecondElementary hsecondContained hsecondInvolutions
  have hfirstProperties := common component heven huniversal hcard _ rank firstCommon hfirstElementary hfirstSize
    hfirstContained hfirstInvolutions hfirstNormal
  have horbit := UniversalOrbitBlock.orbit_conjugate component component
    (UniversalOrbitBlock.mem_orbit_self component) actor
  have hconjugateEven := UniversalOrbitBlock.orbit_even component heven _ horbit
  have hconjugateUniversal := UniversalOrbitBlock.orbit_universal component huniversal _ horbit
  have hconjugateCard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor)) := by
    rw [← Nat.card_congr (OrbitBlockConjugation.equivalence component actor)]
    exact hcard
  have hconjugateContained : ∀ factor ∈ UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor),
      secondCommon ≤ factor ⊓ UniversalOrbitBlock.normalizer component := by
    intro factor hfactor
    have hback := (OrbitBlockConjugation.block (UniversalOrbitBlock.conjugate component actor) factor actor⁻¹).mpr hfactor
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hback
    have hle := hsecondContained (UniversalOrbitBlock.conjugate factor actor⁻¹) hback
    rwa [UniversalOrbitBlock.conjugate_conjugate, mul_inv_cancel, UniversalOrbitBlock.conjugate_one] at hle
  have hconjugateInvolutions : ∀ factor ∈ UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor),
      ∀ member : G, member ∈ factor ⊓ UniversalOrbitBlock.normalizer component ∧ orderOf member = 2 ↔
        member ∈ secondCommon ∧ member ≠ 1 := by
    intro factor hfactor member
    have hback := (OrbitBlockConjugation.block (UniversalOrbitBlock.conjugate component actor) factor actor⁻¹).mpr hfactor
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hback
    have hiff := hsecondInvolutions (UniversalOrbitBlock.conjugate factor actor⁻¹) hback member
    rwa [UniversalOrbitBlock.conjugate_conjugate, mul_inv_cancel, UniversalOrbitBlock.conjugate_one] at hiff
  have hsecondProperties := common _ hconjugateEven hconjugateUniversal hconjugateCard _ rank secondCommon hsecondElementary
    hsecondSize hconjugateContained hconjugateInvolutions (by
      rw [← OrbitBlockConjugation.normalizer component actor, inf_comm]
      exact hsecondNormal)
  have hsecondTwo := InvolutionGeneratedSubgroup.two_of_elementary secondCommon hsecondElementary
  have hdisjointFactor := BlockTwoActionFaithful.disjoint_factor component heven huniversal hquasisimple hcard
    component component component hself hself hself actor hactor secondCommon hsecondTwo
      ((hsecondContained component hself).trans (inf_le_left.trans le_sup_left))
  have hdisjoint : Disjoint firstCommon secondCommon := hdisjointFactor.mono
    ((hfirstContained component hself).trans inf_le_left) le_rfl
  have hfirstOvergroup : firstCommon ≤ UniversalOrbitBlock.normalizer component ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom :=
    le_inf (((hfirstContained component hself).trans inf_le_left).trans
      ((CommutingComponentFamily.factor_le _ component hself).trans Subgroup.le_normalizer))
      ((hfirstContained component hself).trans inf_le_right)
  have hsecondOvergroup : secondCommon ≤ UniversalOrbitBlock.normalizer component ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom := by
    apply le_inf ((hsecondContained component hself).trans inf_le_right)
    rw [OrbitBlockConjugation.normalizer]
    exact ((hconjugateContained _ (UniversalOrbitBlock.mem_block_self _)).trans inf_le_left).trans
      ((CommutingComponentFamily.factor_le _ _ (UniversalOrbitBlock.mem_block_self _)).trans Subgroup.le_normalizer)
  refine ⟨rank, hpositive, firstCommon, secondCommon, hfirstProperties, hsecondProperties, hdisjoint,
    BlockCommonInvolutionPair.normalized_disjoint_commute _ firstCommon secondCommon hfirstOvergroup hsecondOvergroup
      hfirstNormal hsecondNormal hdisjoint, ?_⟩
  intro factor hfactor
  have hcentralizes := BlockCommonCentralizers.intersection_centralizes component heven huniversal hquasisimple hcard hcontrol
    actor hactor secondCommon hsecondElementary hsecondContained hsecondNormal factor hfactor
  have himageContained : ∀ factor ∈ UniversalOrbitBlock.block component,
      secondCommon ≤ UniversalOrbitBlock.conjugate factor actor :=
    fun factor hfactor => (hsecondContained factor hfactor).trans inf_le_left
  refine ⟨BlockCommonInvolutionPair.centralizer_eq component heven huniversal hquasisimple hcard actor secondCommon
    hsecondElementary (hsecondProperties.nontrivial hpositive) himageContained factor hcentralizes, ?_⟩
  intro member hmember hne
  exact BlockCommonCentralizers.singleton_eq component heven huniversal hquasisimple hcard secondCommon hsecondElementary
    actor himageContained factor hcentralizes member hmember hne

end CFSG.ComponentClassification.BlockCommonInvolutionPackage
