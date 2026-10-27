module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Blocks
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.OrbitCongruence
public import Mathlib.Tactic.Polynomial.Basic

public section

open CFSG
open scoped Classical

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem centralizer_conj_mem {G : Type*} [Group G] (subgroup : Subgroup G)
    {element conjugator : G} (hconjugator : conjugator ∈ Subgroup.normalizer (subgroup : Set G))
    (helement : element ∈ Subgroup.centralizer (subgroup : Set G)) :
    conjugator * element * conjugator⁻¹ ∈ Subgroup.centralizer (subgroup : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at helement ⊢
  intro member hmember
  have hinverse := (Subgroup.mem_normalizer_iff''.mp hconjugator member).mp hmember
  have hcommute := helement (conjugator⁻¹ * member * conjugator) hinverse
  have hconjugated := congrArg (fun value : G => conjugator * value * conjugator⁻¹) hcommute
  convert hconjugated using 1 <;> group

theorem centralizer_conj_iff {G : Type*} [Group G] (subgroup : Subgroup G)
    {element conjugator : G} (hconjugator : conjugator ∈ Subgroup.normalizer (subgroup : Set G)) :
    conjugator * element * conjugator⁻¹ ∈ Subgroup.centralizer (subgroup : Set G) ↔
      element ∈ Subgroup.centralizer (subgroup : Set G) := by
  constructor
  · intro hconjugated
    have hinverse := centralizer_conj_mem subgroup
      ((Subgroup.normalizer (subgroup : Set G)).inv_mem hconjugator) hconjugated
    have hequal : conjugator⁻¹ * (conjugator * element * conjugator⁻¹) * conjugator =
        element := by group
    rwa [inv_inv, hequal] at hinverse
  · exact centralizer_conj_mem subgroup hconjugator

theorem brauerProj_apply {G : Type*} [Group G] (subgroup overgroup : Subgroup G)
    (value : G → ℂ) (element : overgroup) :
    BlocksBrauerProj subgroup overgroup value element =
      if (element : G) ∈ Subgroup.centralizer (subgroup : Set G) then value element else 0 := by
  classical
  simp only [BlocksBrauerProj, Set.indicator_apply, Set.mem_ofPred_eq]

theorem brauerProj_central {G : Type*} [Group G] (m : Ideal BlocksAlgInt)
    (hm : m.IsMaximal) (subgroup overgroup : Subgroup G)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    {value : G → ℂ} (hvalue : BlocksIsCentralR m value) :
    BlocksIsCentralR m (BlocksBrauerProj subgroup overgroup value) := by
  classical
  constructor
  · intro element
    rw [brauerProj_apply]
    split_ifs
    · exact hvalue.1 element
    · exact localRing_zero m hm
  · intro element conjugator
    simp only [brauerProj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [centralizer_conj_iff subgroup (hnormalizer conjugator.property), hvalue.2]

theorem centralChar_trivial {G : Type*} [Group G] (value : G → ℂ) :
    BlocksCentralChar (fun _ => 1) value = ∑ᶠ element : G, value element := by
  simp only [BlocksCentralChar, mul_one, div_one]

theorem brauerProj_augmentation {G : Type*} [Group G] [Finite G]
    (subgroup overgroup : Subgroup G)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    (value : G → ℂ) :
    (∑ᶠ element : overgroup, BlocksBrauerProj subgroup overgroup value element) =
      ∑ᶠ element : G, (Subgroup.centralizer (subgroup : Set G) : Set G).indicator value element := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype overgroup := Fintype.ofFinite overgroup
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [brauerProj_apply, Set.indicator_apply]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun (element : overgroup) _ => (element : G))
  · intro element helement
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp helement).2⟩
  · intro left _ right _ hequal
    exact Subtype.ext hequal
  · intro element helement
    have hmember := (Finset.mem_filter.mp helement).2
    refine ⟨⟨element, hcentralizer hmember⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmember⟩
  · intro _ _
    rfl

theorem principal_augmentation_congr {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (prime : ℕ) (hprime : prime.Prime)
    (hprimeMem : (prime : BlocksAlgInt) ∈ m) (subgroup overgroup : Subgroup G)
    (hpGroup : IsPGroup prime subgroup)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    {value : G → ℂ} (hvalue : BlocksIsCentralR m value) :
    BlocksCentralChar (fun _ => 1) value -
      BlocksCentralChar (fun _ => 1) (BlocksBrauerProj subgroup overgroup value) ∈
        BlocksLocalMaxIdeal m := by
  classical
  let conjugation : MulAction subgroup G := {
    smul member element := (member : G) * element * (member : G)⁻¹
    one_smul element := by
      change (1 : G) * element * (1 : G)⁻¹ = element
      group
    mul_smul left right element := by
      change ((left : G) * (right : G)) * element * ((left : G) * (right : G))⁻¹ =
        (left : G) * ((right : G) * element * (right : G)⁻¹) * (left : G)⁻¹
      group
  }
  let : MulAction subgroup G := conjugation
  have hfixed : MulAction.fixedPoints subgroup G =
      (Subgroup.centralizer (subgroup : Set G) : Set G) := by
    ext element
    rw [MulAction.mem_fixedPoints]
    change (∀ member : subgroup, member • element = element) ↔
      element ∈ Subgroup.centralizer (subgroup : Set G)
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hfixed member hmember
      have hequation := hfixed ⟨member, hmember⟩
      change member * element * member⁻¹ = element at hequation
      exact (mul_inv_eq_iff_eq_mul).mp hequation
    · intro hcentral member
      change (member : G) * element * (member : G)⁻¹ = element
      rw [hcentral member member.property, mul_inv_cancel_right]
  rw [centralChar_trivial, centralChar_trivial, brauerProj_augmentation subgroup overgroup hcentralizer]
  rw [← hfixed]
  exact invariant_sum_congr_fixed m hm prime hprime hprimeMem hpGroup value hvalue.1
    (fun member element => hvalue.2 element member)

theorem brauerCorr_trivial (m : Ideal BlocksAlgInt) {G : Type*} [Group G]
    (subgroup overgroup : Subgroup G) {block : Set (overgroup → ℂ)}
    (hcorrespondence : BlocksBrauerCorr m subgroup overgroup block (BlocksPrincipalBlock m G))
    {character : overgroup → ℂ} (hcharacter : character ∈ block)
    {value : G → ℂ} (hvalue : BlocksIsCentralR m value) :
    (∑ᶠ element : G, value element) -
      BlocksCentralChar character (BlocksBrauerProj subgroup overgroup value) ∈
        BlocksLocalMaxIdeal m := by
  simpa only [centralChar_trivial] using
    hcorrespondence value hvalue (fun _ => 1) (trivial_mem_principal m G) character hcharacter

end CFSG.BrauerThirdMainTheorem.Helpers
