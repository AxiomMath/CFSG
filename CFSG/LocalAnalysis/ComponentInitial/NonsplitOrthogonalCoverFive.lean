module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFiveModel
public import CFSG.LocalAnalysis.ComponentInitial.BinaryNonsingularStabilizer
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigher
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryRegular
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover

open Matrix QuadraticMap Module CFSG.ClassicalGroups.Orthogonal OrthogonalTail
open BinaryStabilizer (stabS mem_stabS binary_nonsingular_vector_stabilizer_symplectic_model)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry
  (derived_eq_elementary_isometry)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "Q₄" => quadTail 4 (minusTailForm (ZMod 2) 1 1)
local notation "V₄" => (Fin 4 ⊕ Fin 4 → ZMod 2) × (Fin 2 → ZMod 2)

section Stabilizer

theorem commutator_orthogonalGroup_quadTail_four :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q₄, TauCeti.QuadraticMap.orthogonalGroup Q₄⁆ =
      orthElementaryGroup Q₄ :=
  derived_eq_elementary_isometry (minusTailIsometry 5 (ZMod 2) 1 1).symm
    (commutator_orthogonalGroup_quadMinus (n := 5) (K := ZMod 2) (b := 1) (c := 1) (by norm_num)
      (by decide))

@[expose] def tailOne : V₄ :=
  (0, ![1, 0])

theorem quadTail_tailOne : Q₄ tailOne = 1 := by
  rw [tailOne, quadTail_tail, binTail_one]

theorem stabS_le_orthElementaryGroup : stabS Q₄ tailOne ≤ orthElementaryGroup Q₄ := fun g hg => by
  rw [← commutator_orthogonalGroup_quadTail_four]
  exact (mem_stabS.mp hg).1

theorem leviB_mem_stabS (g : GL (Fin 4) (ZMod 2)) :
    ((leviB (ZMod 2) 4 (by norm_num) g : orthElementaryGroup Q₄) : V₄ ≃ₗ[ZMod 2] V₄) ∈
      stabS Q₄ tailOne := by
  refine mem_stabS.mpr ⟨?_, ?_⟩
  · rw [commutator_orthogonalGroup_quadTail_four]
    exact (leviB (ZMod 2) 4 _ g).2
  · rw [coe_leviB, dMap_apply]
    simp [tailOne]

theorem isPerfect_stabS_and_lieModel :
    Group.IsPerfect (stabS Q₄ tailOne) ∧ CFSG.Blueprint.LieModel (stabS Q₄ tailOne) .PSp 4 2 1 := by
  obtain ⟨-, -, -, -, hperf, hLie⟩ := binary_nonsingular_vector_stabilizer_symplectic_model
    (r := 4) (by norm_num) (W := V₄) (by rw [finrank_tailSpace, finrank_fin_two_fun])
    (nondegenerate_polarBilin_quadTail (binTail_nondegenerate (Nat.card_zmod 2)))
    ⟨tailFlag (ZMod 2) (Fin 2 → ZMod 2) 4 3, finrank_tailFlag (by norm_num),
      fun _ hx => quadTail_eq_zero_of_mem_tailFlag hx⟩ quadTail_tailOne
  exact ⟨hperf, hLie⟩

end Stabilizer

section Lift

variable {E : Type*} [Group E] [Finite E] {θ : E →* orthElementaryGroup Q₄}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem exists_lift_four (h2 : IsPGroup 2 θ.ker) :
    ∃ U : Subgroup E,
      (∀ u ∈ U, θ u ∈ (LinearFlag.unitriangular 4 (ZMod 2)).map
        ((binShape (ZMod 2) 4 (Nat.card_zmod 2) (by norm_num)).ρ.comp
          SpecialLinearGroup.toGL)) ∧
      (∀ a ∈ (LinearFlag.unitriangular 4 (ZMod 2)).map
        ((binShape (ZMod 2) 4 (Nat.card_zmod 2) (by norm_num)).ρ.comp SpecialLinearGroup.toGL),
        ∃ u ∈ U, θ u = a) ∧ ∀ u ∈ U, θ u = 1 → u = 1 := by
  obtain ⟨hperf, hLie⟩ := isPerfect_stabS_and_lieModel
  set S := stabS Q₄ tailOne with hS
  set R : Subgroup (orthElementaryGroup Q₄) := S.subgroupOf (orthElementaryGroup Q₄) with hR
  let eR : R ≃* S := Subgroup.subgroupOfEquivOfLe stabS_le_orthElementaryGroup
  have : Group.IsPerfect R :=
    Group.IsPerfect.ofSurjective (f := eR.symm.toMonoidHom) eR.symm.surjective
  have : Finite (orthElementaryGroup Q₄) := Finite.of_surjective θ hθ
  have : Finite S := Finite.of_equiv R eR.toEquiv
  set F₀ := OrthogonalSplit.leviLift θ R with hF₀
  have : Group.IsPerfect F₀ := OrthogonalSplit.isPerfect_leviLift θ R hθ hC
  set η : F₀ →* S := eR.toMonoidHom.comp (OrthogonalSplit.leviLiftHom θ R) with hη
  have hηeq : ∀ u : F₀, η u = 1 ↔ θ u = 1 := fun u => by
    rw [hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      OrthogonalSplit.leviLiftHom_eq_one_iff]
  have hηsurj : Function.Surjective η :=
    eR.surjective.comp (OrthogonalSplit.leviLiftHom_surjective θ R hθ)
  have hηC : η.ker ≤ Subgroup.center F₀ := fun u hu => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hηeq u).mp hu)) g)
  have hη2 : IsPGroup 2 η.ker := fun k => by
    obtain ⟨n, hn⟩ := h2 ⟨((k : F₀) : E), (hηeq k).mp k.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩
  obtain ⟨hηbot, -⟩ :=
    SymplecticCoverHigher.even_higher_symplectic_prime_field_central_two_cover_trivial η hηsurj
      hηC hη2 le_rfl hLie
  have hF₀inj : ∀ u ∈ F₀, θ u = 1 → u = 1 := by
    intro u hu hθu
    have hk : (⟨u, hu⟩ : F₀) ∈ η.ker := (hηeq _).mpr hθu
    rw [hηbot, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  refine ⟨((LinearFlag.unitriangular 4 (ZMod 2)).map
    ((binShape (ZMod 2) 4 (Nat.card_zmod 2) (by norm_num)).ρ.comp
      SpecialLinearGroup.toGL)).comap θ ⊓ F₀, fun u hu => hu.1, fun a ha => ?_,
    fun u hu hθu => hF₀inj u hu.2 hθu⟩
  have haR : a ∈ F₀.map θ := by
    rw [hF₀, OrthogonalSplit.map_leviLift θ R hθ]
    obtain ⟨A, -, rfl⟩ := ha
    exact Subgroup.mem_subgroupOf.mpr (leviB_mem_stabS _)
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp haR
  exact ⟨u, ⟨ha, hu⟩, rfl⟩

end Lift

theorem ker_eq_bot_of_binShape_four {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (θ : E →* orthElementaryGroup Q₄) (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) : θ.ker = ⊥ := by
  refine UnitaryOddCover.ker_eq_bot_of_sq_reduction (fun θ' hθ' hC' hsq' => ?_) θ hθ hC h2
  have h2' : IsPGroup 2 θ'.ker := fun k => ⟨1, Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
    exact hsq' _ k.2)⟩
  obtain ⟨U, hU, hUsurj, hUinj⟩ := exists_lift_four hθ' hC' h2'
  exact Shape.ker_eq_bot_of_lift (S := binShape (ZMod 2) 4 (Nat.card_zmod 2) (by norm_num)) hθ'
    hC' (by norm_num) hsq' U hU hUsurj hUinj

end CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover

namespace CFSG.LocalAnalysis.ComponentInitial

open NonsplitOrthogonalCover

theorem even_nonsplit_orthogonal_five_prime_field_central_two_cover_trivial {E : Type*}
    {J : Type} [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (hJ : CFSG.Blueprint.LieModel J .POmegaMinus 5 2 1) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨-, ⟨e⟩⟩ := exists_mulEquiv_zmod_of_lieModel hJ
  set η' := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_binShape_four η' (e.surjective.comp hη) (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LocalAnalysis.ComponentInitial
