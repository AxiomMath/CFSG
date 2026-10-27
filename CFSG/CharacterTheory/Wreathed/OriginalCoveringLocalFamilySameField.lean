module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityFull
public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelCharacters
public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelLocalModel
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo

public noncomputable section
open scoped Classical
namespace CFSG.Wreathed.OriginalCoveringLocalFamily
open CFSG.Assembly.LowTwoRank CFSG.TwoRankLowerBound.Helpers
open SquareRootSmallCharacterRigidity SameFieldOddKernel WreathCentralSquare
open FullSylowCoveringObstruction
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem same_field_simple_odd_index_quotient_trivial_odd_kernel
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (O : Subgroup K) [O.Normal] (hO : Odd (Nat.card O))
    (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index) [IsSimpleGroup L]
    (hnonabL : ∃ a b : L, a * b ≠ b * a)
    (hmodel : (p ^ f % 4 = 1 ∧ StatedClassicalModel L .PSL 3 p f) ∨
      (p ^ f % 4 = 3 ∧ StatedClassicalModel L .PSU 3 p f)) : O = ⊥ := by
  let : Fintype G := Fintype.ofFinite G
  let : Fintype L := Fintype.ofFinite L
  have hpne : p ≠ 2 := by
    rintro rfl
    norm_num at hpodd
  obtain ⟨ideal, hmax, hres⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  let : ideal.IsMaximal := hmax
  let : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hres
  obtain ⟨Q, β, hQ, hβblock, hβne, hβdegree, hβactual, hβsection, hβmin, hβfloor, hβunique⟩ :=
    actual_root_unique_small_character_and_minimum hnonab n hn S e hfour p f hp hpne hf
      hlocal ideal
  let P := layerSylow S K hSK O L hindex
  let eP := layerCoordinates S e K hSK O hO L hindex
  have hlocalL := same_field_layer_local_data n hn S e K hSK O hO L hindex
    p f hp hpodd hf hq hmodel
  obtain ⟨QL, βL, hQL, hβLblock, hβLne, hβLdegree, hβLactual, hβLsection,
    hβLmin, hβLfloor, hβLunique⟩ :=
      actual_root_unique_small_character_and_minimum hnonabL n hn P eP hlocalL.1
        p f hp hpne hf hlocalL.2.2.2.2.2.1 ideal
  have hQLQ : QL = Q := by
    have h := hQL.trans hQ.symm
    exact_mod_cast h
  have hdegree : (β : G → ℂ) 1 = (Q : ℂ) := by
    rw [irreducibleDegree_cast, hβdegree]
  have hQone : 1 < Q := (square_root_degree_bounds hq (modFourSign_cases (p ^ f)) hQ).1
  let ρ := affordingComplexRepresentation β
  let θL := fixedSpaceLayerComplexRepresentation ρ.representation K O L
  let y := actualRoot (subgroupSylow S K hSK) (subgroupCoordinates S e K hSK)
  let yL := actualRoot P eP
  have hβsectionK : ∀ h : ℤ, Odd h → ∀ v : G, Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({(y : G)} : Set G) →
      (β : G → ℂ) ((y : G) ^ h * v) = -1 := by
    simpa only [y, coveringRoot_coe] using
      (fun h hh v hv hc => hβsection h v hh hv hc)
  have hρsection : ∀ h : ℤ, Odd h → ∀ v : G, Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({(y : G)} : Set G) →
      ρ.representation.character ((y : G) ^ h * v) = -1 := by
    simpa only [ρ, (affordingComplexRepresentation_spec β).2] using hβsectionK
  have hsectionL := fixedSpaceLayerRepresentation_cyclic_sections
    ρ.representation K O hO L y (n + 1) (by omega) (coveringRoot_order n hn S e K hSK)
    yL (layerRoot_coe S e K hSK O hO L hindex) (-1) hρsection
  have hθsection : ∀ (h : ℤ) (v : L), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot P eP} : Set L) →
      θL.character (actualRoot P eP ^ h * v) = -1 := by
    intro h v hh hv hc
    exact hsectionL h hh v hv hc
  have hbound : Module.finrank ℂ θL.vector ≤ Q :=
    oddKernelQuotientCharacterRepresentation_degree_le β K O Q hdegree
  have hfloor : Q ≤ Module.finrank ℂ θL.vector := by
    rw [← hQLQ]
    exact (hβLfloor θL hθsection).1
  exact oddKernel_eq_bot_of_original_layer_character_degree β Q hQone hdegree K O L
    (Nat.le_antisymm hbound hfloor)

end CFSG.Wreathed.OriginalCoveringLocalFamily
