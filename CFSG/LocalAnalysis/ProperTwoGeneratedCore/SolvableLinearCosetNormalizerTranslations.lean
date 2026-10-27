module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerSolvableOrSeven
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExactTwoPowerPointIndex

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.CosetNormalizer CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

local instance factPrimeSevenTranslations : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

theorem not_isSolvable_coordinateG_zmod_seven : ¬ Group.IsSolvable (coordinateG (ZMod 7)) := by
  intro hsolv
  have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 (ZMod 7)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  have : IsSimpleGroup (coordinateG (ZMod 7)) := (pslEquivCoordinateG (ZMod 7)).symm.isSimpleGroup
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
  let _ : CommGroup (coordinateG (ZMod 7)) :=
    { (inferInstance : Group (coordinateG (ZMod 7))) with mul_comm := hcomm }
  have hp := IsSimpleGroup.prime_card (α := coordinateG (ZMod 7))
  rw [card_coordinateG_zmod_seven] at hp
  norm_num at hp

theorem not_projective_seven_of_isSolvable {Δ : Set G}
    (hsolv : Group.IsSolvable (cosetNormalizerPerm Δ).range) (b : Δ ≃ Omega (ZMod 7))
    (hb : (fun σ : Equiv.Perm Δ => b.permCongr σ) '' ((cosetNormalizerPerm Δ).range :
      Set (Equiv.Perm Δ)) = (coordinateG (ZMod 7) : Set (Equiv.Perm (Omega (ZMod 7))))) :
    False := by
  have hmap : (cosetNormalizerPerm Δ).range.map b.permCongrHom.toMonoidHom =
      coordinateG (ZMod 7) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map]
    exact hb
  let e : (cosetNormalizerPerm Δ).range ≃* coordinateG (ZMod 7) :=
    ((cosetNormalizerPerm Δ).range.equivMapOfInjective _ b.permCongrHom.injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact not_isSolvable_coordinateG_zmod_seven
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

variable [Finite G]

theorem coset_normalizer_translation_data
    {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (hrank : twoRank (pairPointStabilizer H beta) = 1) {u : G}
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) (huz : Commute u z)
    (hesc : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) (U : Subgroup G)
    [IsElementaryAbelian 2 U] (hUset : (U : Set G) = {1} ∪ distinguishedRoots H z u)
    (hsolv : Group.IsSolvable (cosetNormalizerPerm ((fun v : G => u * v) '' (U : Set G))).range) :
    let Δ := (fun v : G => u * v) '' (U : Set G)
    let L := localInvolutionPointHull z u
    Subgroup.normalizer Δ ≤ H ∧
      L ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer Δ ∧
      (∀ b ∈ U, b ≠ 1 → ∀ b' ∈ U, b' ≠ 1 →
        ∃ m ∈ L ⊓ Subgroup.normalizer (U : Set G), m * b * m⁻¹ = b') ∧
      ∃ j : Additive U ≃ Δ, (∀ v : U, (j (Additive.ofMul v) : G) = u * v) ∧
        ∀ g ∈ translationGroup (Additive U),
          j.permCongr g.toEquiv ∈ (cosetNormalizerPerm Δ).range := by
  intro Δ L
  classical
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(L ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({u} : Set G))) := inferInstance
  obtain ⟨U', hU'el, hU'set, -, hΔ', -, -, hNH, -, hJ⟩ :=
    RankOnePair.involution_coset_normalizer_solvable_or_projective_seven h
      (properStrongEmbeddingCommutingImages_holds G) (smallerR1Full G) beta hbeta hrank huD hu
      huz hesc R T₁
  have hUU : U' = U :=
    SetLike.coe_injective (hU'set.trans (by rw [hUset, one_union_distinguishedRoots_eq]))
  subst hUU
  rw [hΔ'] at hNH hJ
  obtain ⟨j, hj, -, -, hLN, hC, hbranch⟩ := hJ
  obtain ⟨-, -, -, -, hreg⟩ := hC
  have htrans : ∀ b ∈ U', b ≠ 1 → ∀ b' ∈ U', b' ≠ 1 →
      ∃ m ∈ L ⊓ Subgroup.normalizer (U' : Set G), m * b * m⁻¹ = b' := by
    intro b hb hb1 b' hb' hb'1
    have hx : u * b ∈ Δ := ⟨b, hb, rfl⟩
    have hy : u * b' ∈ Δ := ⟨b', hb', rfl⟩
    have hxu : u * b ≠ u := fun h' => hb1 (by simpa using h')
    have hyu : u * b' ≠ u := fun h' => hb'1 (by simpa using h')
    obtain ⟨⟨σ, hσ⟩, hσxy, -⟩ := hreg ⟨u * b, hx⟩ ⟨u * b', hy⟩ hxu hyu
    obtain ⟨m, hm, rfl⟩ := hσ
    obtain ⟨hmL, hmU⟩ := Subgroup.mem_subgroupOf.mp hm
    refine ⟨m, ⟨hmL, hmU⟩, ?_⟩
    have h1 : (m : G) * (u * b) * (m : G)⁻¹ = u * b' := congrArg Subtype.val hσxy
    have hmu : (m : G) * u = u * m :=
      Subgroup.mem_centralizer_singleton_iff.mp (localInvolutionPointHull_le_centralizer z u hmL)
    have h2 : (m : G) * (u * b) * (m : G)⁻¹ = u * ((m : G) * b * (m : G)⁻¹) := by
      rw [← mul_assoc (m : G) u, hmu]; group
    rw [h2] at h1
    exact mul_left_cancel h1
  rcases hbranch with ⟨-, htr⟩ | ⟨-, ⟨b, hb⟩, -⟩
  · exact ⟨hNH, hLN, htrans, j, hj, htr⟩
  · exact (not_projective_seven_of_isSolvable hsolv b hb).elim

theorem exact_two_power_point_index_root_coset
    (hgen : PairGenerationTheorem G)
    {H : Subgroup G} {z u : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : pointRightCosetSpace H} (hb : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H) :
    let N := Subgroup.normalizer (rootCoset H z u)
    let D := pairPointStabilizer H beta
    let q := Nat.card ({1} ∪ distinguishedRoots H z u : Set G)
    let k := Nat.card (elementFixedSet H u)
    (∃ Q : Sylow 2 D, (Q : Subgroup D).map D.subtype ≤ N ⊓ D) ∧ D.relIndex N = q * (k - 1) ∧
      (Nat.card (pointRightCosetSpace H) - 1 = q * (k - 1) →
        ∀ S : Sylow 2 N, ∃ Q : Sylow 2 G, (Q : Subgroup G) = (S : Subgroup N).map N.subtype) := by
  intro N D q k
  obtain ⟨T1⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({u} : Set G) ⊓ H)) := inferInstance
  obtain ⟨-, -, -, hDelta, -, -, hQ, hindex, -, -, hglobal⟩ :=
    involution_coset_normalizer_exact_two_power_point_index hgen h beta hb huD hu huz hescape T1
  have hU : cosetUnitSet H z u = {1} ∪ distinguishedRoots H z u := by
    rw [cosetUnitSet, one_union_distinguishedRoots_eq]
  have hroot : (fun w : G => u * w) '' cosetUnitSet H z u = rootCoset H z u := by
    rw [hU]; rfl
  have hk : cosetFixedSet H u = elementFixedSet H u := rfl
  rw [hDelta, hroot] at hQ hindex hglobal
  rw [hU, hk] at hindex hglobal
  exact ⟨hQ, hindex, hglobal⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair
