module

public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelFixedSpace
public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelSections
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock

public noncomputable section

namespace CFSG.Wreathed.SameFieldOddKernel

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.SquareRootSmallCharacterRigidity
open scoped BigOperators Classical

variable {G : Type} [Group G]

theorem original_irreducible_affording_exists (β : CFSG.BlocksIrr G) :
    ∃ ρ : FiniteComplexRepresentation.{0, 0} G,
      ρ.IsIrreducible ∧ ρ.character = (β : G → ℂ) := by
  simpa only [CFSG.blocksIrr_eq_irreducible_characters, Set.mem_ofPred_eq] using β.property

@[expose] def affordingComplexRepresentation (β : CFSG.BlocksIrr G) :
    FiniteComplexRepresentation.{0, 0} G :=
  Classical.choose (original_irreducible_affording_exists β)

theorem affordingComplexRepresentation_spec (β : CFSG.BlocksIrr G) :
    (affordingComplexRepresentation β).IsIrreducible ∧
      (affordingComplexRepresentation β).character = (β : G → ℂ) :=
  Classical.choose_spec (original_irreducible_affording_exists β)

theorem original_irreducible_basis_label_unique [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (β : CFSG.BlocksIrr G) :
    ∃! label : basis.index, (basis.representation label).character = (β : G → ℂ) := by
  obtain ⟨label, hlabel⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    basis (affordingComplexRepresentation β) (affordingComplexRepresentation_spec β).1
  have hβ := hlabel.trans (affordingComplexRepresentation_spec β).2
  exact ⟨label, hβ, fun other hother => basis.distinct (hother.trans hβ.symm)⟩

@[expose] def oddKernelQuotientCharacterRepresentation (β : CFSG.BlocksIrr G)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] :
    FiniteComplexRepresentation.{0, 0} (K ⧸ O) where
  vector := Representation.invariants
    (((affordingComplexRepresentation β).representation.comp K.subtype).comp O.subtype)
  representation := fixedSpaceQuotientRepresentation
    (affordingComplexRepresentation β).representation K O

theorem oddKernelQuotientCharacterRepresentation_apply (β : CFSG.BlocksIrr G)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (g : K)
    (w : Representation.invariants
      (((affordingComplexRepresentation β).representation.comp K.subtype).comp O.subtype)) :
    (Representation.invariants
      (((affordingComplexRepresentation β).representation.comp K.subtype).comp O.subtype)).subtype
      ((oddKernelQuotientCharacterRepresentation β K O).representation (QuotientGroup.mk' O g) w) =
      (affordingComplexRepresentation β).representation (g : G) w.val := rfl

theorem oddKernelQuotientCharacterRepresentation_average [Fintype G]
    (β : CFSG.BlocksIrr G) (K : Subgroup G) (O : Subgroup K) [O.Normal] (g : K) :
    (oddKernelQuotientCharacterRepresentation β K O).character (QuotientGroup.mk' O g) =
      (Nat.card O : ℂ)⁻¹ * ∑ o : O, (β : G → ℂ) ((g : G) * ((o : K) : G)) := by
  change (fixedSpaceQuotientRepresentation
    (affordingComplexRepresentation β).representation K O).character (g : K ⧸ O) = _
  rw [fixedSpaceQuotientRepresentation_character_mk]
  change (Nat.card O : ℂ)⁻¹ * ∑ o : O,
    (affordingComplexRepresentation β).character ((g : G) * ((o : K) : G)) = _
  rw [(affordingComplexRepresentation_spec β).2]

theorem oddKernelQuotientCharacterRepresentation_degree_le
    (β : CFSG.BlocksIrr G) (K : Subgroup G) (O : Subgroup K) [O.Normal]
    (Q : ℕ) (hβdegree : (β : G → ℂ) 1 = (Q : ℂ)) :
    Module.finrank ℂ (oddKernelQuotientCharacterRepresentation β K O).vector ≤ Q := by
  have hfinrank : Module.finrank ℂ (affordingComplexRepresentation β).vector = Q := by
    have hdegree := congrFun (affordingComplexRepresentation_spec β).2 1
    rw [hβdegree] at hdegree
    change (affordingComplexRepresentation β).representation.character 1 = (Q : ℂ) at hdegree
    rw [Representation.char_one] at hdegree
    exact_mod_cast hdegree
  exact hfinrank ▸ Submodule.finrank_le _

theorem oddKernelQuotientCharacterRepresentation_degree_eq_iff
    {β : CFSG.BlocksIrr G} {K : Subgroup G} {O : Subgroup K} [O.Normal]
    (Q : ℕ) (hβdegree : (β : G → ℂ) 1 = (Q : ℂ)) :
    Module.finrank ℂ (oddKernelQuotientCharacterRepresentation β K O).vector = Q ↔
      O.map K.subtype ≤ MonoidHom.ker (affordingComplexRepresentation β).representation := by
  have hfinrank : Module.finrank ℂ (affordingComplexRepresentation β).vector = Q := by
    have hdegree := congrFun (affordingComplexRepresentation_spec β).2 1
    rw [hβdegree] at hdegree
    change (affordingComplexRepresentation β).representation.character 1 = (Q : ℂ) at hdegree
    rw [Representation.char_one] at hdegree
    exact_mod_cast hdegree
  rw [← hfinrank]
  change Module.finrank ℂ (Representation.invariants
    (((affordingComplexRepresentation β).representation.comp K.subtype).comp O.subtype)) =
      Module.finrank ℂ (affordingComplexRepresentation β).vector ↔ _
  rw [finrank_invariants_eq_finrank_iff, Subgroup.map_le_iff_le_comap, MonoidHom.comap_ker]

theorem oddKernelQuotientCharacterRepresentation_layer
    (β : CFSG.BlocksIrr G) (K : Subgroup G) (O : Subgroup K) [O.Normal]
    (L : Subgroup (K ⧸ O)) (g : L) :
    (fixedSpaceLayerComplexRepresentation (affordingComplexRepresentation β).representation
      K O L).character g =
      (oddKernelQuotientCharacterRepresentation β K O).character (g : K ⧸ O) := rfl

theorem oddKernelQuotientCharacterRepresentation_section_union [Fintype G]
    (β : CFSG.BlocksIrr G) (K : Subgroup G) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (y : K) (a : ℕ) (ha : 1 ≤ a)
    (hy : orderOf y = 2 ^ a) (c : ℂ)
    (hβsection : ∀ h : ℤ, Odd h → ∀ v : G, Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({(y : G)} : Set G) →
      (β : G → ℂ) ((y : G) ^ h * v) = c) :
    ∀ g ∈ squareRootSection (QuotientGroup.mk' O y),
      (oddKernelQuotientCharacterRepresentation β K O).character g = c := by
  have hsectionρ : ∀ h : ℤ, Odd h → ∀ v : G, Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({(y : G)} : Set G) →
      (affordingComplexRepresentation β).character ((y : G) ^ h * v) = c := by
    simpa only [(affordingComplexRepresentation_spec β).2] using hβsection
  have hsections := (odd_kernel_fixed_space_character_preserves_cyclic_two_sections
    K O hO y a ha hy (affordingComplexRepresentation β).representation c hsectionρ).2.2.1
  have hclass : CFSG.BlocksIsClassFunction
      (oddKernelQuotientCharacterRepresentation β K O).character :=
    fun g x => Representation.char_conj _ g x
  exact (classFunction_section_value_iff hclass).mp (fun h v hh hv hvy =>
    (hsections h hh v hv hvy).1)

theorem original_root_quotient_and_layer_character_data [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (β : CFSG.BlocksIrr G) (Q : ℕ) (hβdegree : (β : G → ℂ) 1 = (Q : ℂ))
    (hβsection : ∀ h : ℤ, Odd h → ∀ v : G, Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({WreathCentralSquare.actualRoot S e} : Set G) →
      (β : G → ℂ) (WreathCentralSquare.actualRoot S e ^ h * v) = -1) :
    let ρ := affordingComplexRepresentation β
    let θ := oddKernelQuotientCharacterRepresentation β K O
    let θL := fixedSpaceLayerComplexRepresentation ρ.representation K O L
    let y := WreathCentralSquare.actualRoot (FullSylowCoveringObstruction.subgroupSylow S K hSK)
      (FullSylowCoveringObstruction.subgroupCoordinates S e K hSK)
    let yL := WreathCentralSquare.actualRoot (layerSylow S K hSK O L hindex)
      (layerCoordinates S e K hSK O hO L hindex)
    ρ.IsIrreducible ∧ ρ.character = (β : G → ℂ) ∧
    Module.finrank ℂ θ.vector ≤ Q ∧
    Module.finrank ℂ θL.vector = Module.finrank ℂ θ.vector ∧
    (∀ g : L, θL.character g = θ.character (g : K ⧸ O)) ∧
    (∀ g : K, θ.character (QuotientGroup.mk' O g) =
      (Nat.card O : ℂ)⁻¹ * ∑ o : O, (β : G → ℂ) ((g : G) * ((o : K) : G))) ∧
    (∀ g ∈ squareRootSection (QuotientGroup.mk' O y), θ.character g = -1) ∧
    (∀ g ∈ squareRootSection yL, θL.character g = -1) ∧
    (Module.finrank ℂ θL.vector = Q ↔
      O.map K.subtype ≤ MonoidHom.ker ρ.representation) := by
  let ρ := affordingComplexRepresentation β
  let θ := oddKernelQuotientCharacterRepresentation β K O
  let θL := fixedSpaceLayerComplexRepresentation ρ.representation K O L
  let y := WreathCentralSquare.actualRoot (FullSylowCoveringObstruction.subgroupSylow S K hSK)
    (FullSylowCoveringObstruction.subgroupCoordinates S e K hSK)
  let yL := WreathCentralSquare.actualRoot (layerSylow S K hSK O L hindex)
    (layerCoordinates S e K hSK O hO L hindex)
  have hβsectionK : ∀ h : ℤ, Odd h → ∀ v : G, Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({(y : G)} : Set G) →
      (β : G → ℂ) ((y : G) ^ h * v) = -1 := by
    simpa only [y, coveringRoot_coe] using hβsection
  have hsectionX := oddKernelQuotientCharacterRepresentation_section_union β K O hO
    y (n + 1) (by omega) (coveringRoot_order n hn S e K hSK) (-1) hβsectionK
  have hsectionL : ∀ g ∈ squareRootSection yL, θL.character g = -1 := by
    intro g hg
    have himage := map_mem_squareRootSection L.subtype hg
    change (g : K ⧸ O) ∈ squareRootSection (yL : K ⧸ O) at himage
    have hyL : (yL : K ⧸ O) = QuotientGroup.mk' O y :=
      layerRoot_coe S e K hSK O hO L hindex
    rw [hyL] at himage
    exact hsectionX (g : K ⧸ O) himage
  exact ⟨(affordingComplexRepresentation_spec β).1, (affordingComplexRepresentation_spec β).2,
    oddKernelQuotientCharacterRepresentation_degree_le β K O Q hβdegree, rfl,
    fun g => oddKernelQuotientCharacterRepresentation_layer β K O L g,
    fun g => oddKernelQuotientCharacterRepresentation_average β K O g, hsectionX, hsectionL,
    oddKernelQuotientCharacterRepresentation_degree_eq_iff (β := β) (K := K) (O := O) Q hβdegree⟩

theorem oddKernel_eq_bot_of_original_layer_character_degree [IsSimpleGroup G]
    (β : CFSG.BlocksIrr G) (Q : ℕ) (hQ : 1 < Q)
    (hβdegree : (β : G → ℂ) 1 = (Q : ℂ))
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O))
    (hθLdegree : Module.finrank ℂ
      (fixedSpaceLayerComplexRepresentation (affordingComplexRepresentation β).representation
        K O L).vector = Q) : O = ⊥ := by
  let ρ := affordingComplexRepresentation β
  let : ρ.representation.IsIrreducible := (affordingComplexRepresentation_spec β).1
  have hρdegree : ρ.character 1 = (Q : ℂ) := by
    rw [(affordingComplexRepresentation_spec β).2, hβdegree]
  have hρkernel : MonoidHom.ker ρ.representation = ⊥ :=
    irreducible_ker_eq_bot_of_degree_ne_one ρ.representation (by
      change ρ.character 1 ≠ 1
      rw [hρdegree]
      intro heq
      have hQone : Q = 1 := by exact_mod_cast heq
      omega)
  have hOimage := (oddKernelQuotientCharacterRepresentation_degree_eq_iff
    (β := β) (K := K) (O := O) Q hβdegree).mp hθLdegree
  exact subgroup_eq_bot_of_image_le_ker ρ.representation hρkernel K O hOimage

end CFSG.Wreathed.SameFieldOddKernel
