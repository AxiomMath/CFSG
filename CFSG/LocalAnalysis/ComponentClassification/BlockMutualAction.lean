module

public import CFSG.LocalAnalysis.ComponentClassification.BlockFactorContainment
public import CFSG.LocalAnalysis.ComponentClassification.BlockProductFusion
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionOddIntersection

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockMutualAction

theorem commutator_le_core {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (twoSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup)
    (hcontained : twoSubgroup ≤ UniversalOrbitBlock.conjugate second actor)
    (hnormalizes : twoSubgroup ≤ Subgroup.normalizer (first : Set G)) :
    ⁅twoSubgroup, first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom⁆ ≤
      (componentClassificationOddCore
        ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
          (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype := by
  let image := UniversalOrbitBlock.conjugate second actor
  let imageNormalizer := (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  have hsecondNormalizer : image ≤ imageNormalizer := Subgroup.map_mono
    ((CommutingComponentFamily.factor_le _ second hsecond).trans Subgroup.le_normalizer)
  apply TwoActionOddIntersection.commutator_le_core first image imageNormalizer twoSubgroup
    hsecondNormalizer htwo hcontained hnormalizes
  · simpa only [sup_idem] using BlockProductFusion.intersection_odd component heven huniversal hquasisimple hcard
      first first second second hfirst hfirst hsecond hsecond actor hactor
  · intro member hmember
    obtain ⟨preimage, hpreimage, heq⟩ := Subgroup.mem_map.mp hmember.2
    have hpreserved := (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple
      preimage).mp hpreimage second hsecond
    have hconjugateEq : image.map (MulAut.conj member).toMonoidHom =
        UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate second preimage) actor := by
      change UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate second actor) member = _
      rw [UniversalOrbitBlock.conjugate_conjugate, UniversalOrbitBlock.conjugate_conjugate]
      have hmultiply : member * actor = actor * preimage := by
        change actor * preimage * actor⁻¹ = member at heq
        rw [← heq]
        group
      rw [hmultiply]
    rw [hconjugateEq]
    simpa only [sup_idem] using BlockProductFusion.intersection_odd component heven huniversal hquasisimple hcard
      first first second (UniversalOrbitBlock.conjugate second preimage) hfirst hfirst hsecond hpreserved actor hactor
  · intro member hmember hnotNormalizes
    obtain ⟨preimage, hpreimage, heq⟩ := Subgroup.mem_map.mp hmember.2
    have hpreserved := (UniversalOrbitBlock.normalizer_iff_preserves_block component heven huniversal hquasisimple
      preimage).mp hpreimage second hsecond
    have hconjugateEq : image.map (MulAut.conj member).toMonoidHom =
        UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate second preimage) actor := by
      change UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate second actor) member = _
      rw [UniversalOrbitBlock.conjugate_conjugate, UniversalOrbitBlock.conjugate_conjugate]
      have hmultiply : member * actor = actor * preimage := by
        change actor * preimage * actor⁻¹ = member at heq
        rw [← heq]
        group
      rw [hmultiply]
    have hne : second ≠ UniversalOrbitBlock.conjugate second preimage := by
      intro hequal
      apply hnotNormalizes
      apply (CommutingComponentFamily.normalizer_iff_conjugate_eq image member).mpr
      exact hconjugateEq.trans (congrArg (fun candidate : Subgroup G => UniversalOrbitBlock.conjugate candidate actor)
        hequal.symm)
    have hcommutes := UniversalOrbitBlock.block_commutes component heven huniversal second hsecond
      (UniversalOrbitBlock.conjugate second preimage) hpreserved hne
    rw [hconjugateEq]
    have hmap := congrArg (Subgroup.map (MulAut.conj actor).toMonoidHom) hcommutes
    change ⁅second.map (MulAut.conj actor).toMonoidHom,
      (UniversalOrbitBlock.conjugate second preimage).map (MulAut.conj actor).toMonoidHom⁆ = ⊥
    simpa only [Subgroup.map_commutator, Subgroup.map_bot] using hmap

theorem intersection_center_join_ne_top {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component) :
    (((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subgroupOf first) ⊔
      Subgroup.center first ≠ ⊤ := by
  let intersection := ((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subgroupOf first
  let : Group.IsPerfect first := ⟨(UniversalOrbitBlock.orbit_quasisimple component hquasisimple first hfirst.1).1⟩
  intro hcover
  have hderived : commutator first = ⁅intersection, intersection⁆ := by
    change ⁅(⊤ : Subgroup first), ⊤⁆ = ⁅intersection, intersection⁆
    rw [← hcover]
    exact CentralExtensions.commutator_sup_central intersection (Subgroup.center first) le_rfl
  have hintersectionTop : intersection = ⊤ := by
    apply top_unique
    rw [← Group.IsPerfect.commutator_eq_top, hderived]
    exact Subgroup.commutator_le_self _
  have hfirstLe : first ≤ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom := by
    intro member hmember
    have hmem : (⟨member, hmember⟩ : first) ∈ intersection := by rw [hintersectionTop]; exact Subgroup.mem_top _
    exact hmem
  have hpreimageLe : UniversalOrbitBlock.conjugate first actor⁻¹ ≤ UniversalOrbitBlock.normalizer component := by
    intro member hmember
    obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp hmember
    obtain ⟨lift, hlift, hliftEq⟩ := Subgroup.mem_map.mp (hfirstLe horiginal)
    have hidentity : (MulAut.conj actor⁻¹) ((MulAut.conj actor) lift) = lift := by
      simp only [MulAut.conj_apply, inv_inv]
      group
    have hmemberEq : member = lift := by
      have heq' : (MulAut.conj actor⁻¹) original = member := heq
      have hliftEq' : (MulAut.conj actor) lift = original := hliftEq
      rw [← hliftEq', hidentity] at heq'
      exact heq'.symm
    rwa [hmemberEq]
  have hinverse := BlockFactorContainment.transporter component heven huniversal hquasisimple hcard hcontrol
    first hfirst actor⁻¹ hpreimageLe
  exact hactor ((UniversalOrbitBlock.normalizer component).inv_mem_iff.mp hinverse)

end CFSG.ComponentClassification.BlockMutualAction
