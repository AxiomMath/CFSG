module

public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterScalars
public import CFSG.CharacterTheory.Wreathed.ProjectiveTwoParameterUniqueness
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.Fitting.SelfCentralizingComponent

public noncomputable section

namespace CFSG.Wreathed.DegreeThreeModelFullCenter

open Matrix
open CFSG.Semidihedral.OddLinearNormals
open CFSG.Assembly.LowTwoRank

universe u v

variable {F : Type u} {E : Type v} [Field F] [Field E]

theorem specialInclusion_injective (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    Function.Injective (specialInclusion i b B hSB) := by
  intro x y hxy
  exact conjugatedEntrywiseSL_injective i i.injective b (congrArg Subtype.val hxy)

theorem specialInclusion_mem_scalars_iff (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) {x : SpecialLinearGroup (Fin 2) F} :
    specialInclusion i b B hSB x ∈ scalarSubgroup B ↔
      x ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  constructor
  · intro hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply specialInclusion_injective i b B hSB
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (scalarSubgroup_le_center B hx) _
  · intro hx
    apply centralizes_specialInclusion_scalar i b B hSB
    intro y
    change specialInclusion i b B hSB x * specialInclusion i b B hSB y =
      specialInclusion i b B hSB y * specialInclusion i b B hSB x
    simpa only [map_mul] using congrArg (specialInclusion i b B hSB)
      (Subgroup.mem_center_iff.mp hx y).symm

@[expose] def projectiveSpecialHom (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    SpecialLinearGroup (Fin 2) F →* B ⧸ scalarSubgroup B :=
  (QuotientGroup.mk' (scalarSubgroup B)).comp (specialInclusion i b B hSB)

theorem projectiveSpecialHom_ker (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    (projectiveSpecialHom i b B hSB).ker =
      Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  ext x
  change QuotientGroup.mk' (scalarSubgroup B) (specialInclusion i b B hSB x) = 1 ↔ _
  exact (QuotientGroup.eq_one_iff (N := scalarSubgroup B)
    (specialInclusion i b B hSB x)).trans (specialInclusion_mem_scalars_iff i b B hSB)

@[expose] def projectiveSpecialEquiv (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    ProjectiveSpecialLinearGroup (Fin 2) F ≃* (projectiveSpecialHom i b B hSB).range :=
  QuotientGroup.liftEquiv (Subgroup.center (SpecialLinearGroup (Fin 2) F))
    (φ := (projectiveSpecialHom i b B hSB).rangeRestrict)
    (projectiveSpecialHom i b B hSB).rangeRestrict_surjective (by
      rw [MonoidHom.ker_rangeRestrict, projectiveSpecialHom_ker])

theorem projectiveSpecialEquiv_mk (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    (x : SpecialLinearGroup (Fin 2) F) :
    (projectiveSpecialEquiv i b B hSB
      (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)) x) :
        B ⧸ scalarSubgroup B) =
          QuotientGroup.mk' (scalarSubgroup B) (specialInclusion i b B hSB x) := by
  unfold projectiveSpecialEquiv
  exact congrArg Subtype.val (QuotientGroup.liftEquiv_mk _ _ _ x)

theorem card_projectiveSpecialHom_range [Finite F] (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    (hSB : conjugatedImageSL i b ≤ B) :
    Nat.card (projectiveSpecialHom i b B hSB).range =
      Nat.card F * (Nat.card F ^ 2 - 1) / Nat.gcd 2 (Nat.card F - 1) := by
  rw [← Nat.card_congr (projectiveSpecialEquiv i b B hSB).toEquiv]
  exact ProjectiveTwoParameterUniqueness.card_projective_two_field F

theorem card_projectiveSpecialHom_range_of_odd [Finite F] (hFodd : Odd (Nat.card F))
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    Nat.card (projectiveSpecialHom i b B hSB).range =
      Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
  rw [card_projectiveSpecialHom_range i b B hSB]
  rw [Nat.gcd_eq_left ((hFodd.tsub_odd odd_one).two_dvd)]

theorem projectiveSpecialHom_range_isPerfect [Finite F] (hF : 4 ≤ Nat.card F)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    Group.IsPerfect (projectiveSpecialHom i b B hSB).range := by
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hF
  exact Group.IsPerfect.ofSurjective
    (f := (projectiveSpecialHom i b B hSB).rangeRestrict)
    (projectiveSpecialHom i b B hSB).rangeRestrict_surjective

theorem projectiveSpecialHom_range_isSimple (hF : 4 ≤ Nat.card F)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    IsSimpleGroup (projectiveSpecialHom i b B hSB).range := by
  let : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    ProjectiveSpecialLinearGroup.rank_two_simple hF
  exact (projectiveSpecialEquiv i b B hSB).symm.isSimpleGroup

theorem projectiveSpecialHom_range_statedClassicalModel
    {F E : Type} [Field F] [Finite F] [Field E] (p f : ℕ)
    (hp : p.Prime) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f) (hcard : Nat.card F = p ^ f)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    StatedClassicalModel (projectiveSpecialHom i b B hSB).range .PSL 2 p f := by
  refine ⟨⟨hp, hf, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hcard,
    ⟨(projectiveSpecialEquiv i b B hSB).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 F)⟩⟩
  · intro h
    have heq := (Prod.mk.inj h).2
    omega
  · intro h
    have heq := (Prod.mk.inj h).2
    omega

@[expose] def projectiveSpecialThreeEquivAlternating [Finite F] (hF : Nat.card F = 3)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    (projectiveSpecialHom i b B hSB).range ≃* alternatingGroup (Fin 4) := by
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact (projectiveSpecialEquiv i b B hSB).symm.trans
    ((CFSG.GorensteinWalter.psl2RingEquiv eF).symm.trans
      CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup)

theorem projectiveSpecialHom_range_three_isSolvable [Finite F] (hF : Nat.card F = 3)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B) :
    Group.IsSolvable (projectiveSpecialHom i b B hSB).range := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
  let : Group.IsSolvable (alternatingGroup (Fin 4)) := inferInstance
  exact Group.isSolvable_of_isSolvable_injective
    (f := (projectiveSpecialThreeEquivAlternating hF i b B hSB).toMonoidHom)
    (projectiveSpecialThreeEquivAlternating hF i b B hSB).injective


omit [Field F] in
theorem card_matrix_overgroup_scalar_quotient
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) [Finite B]
    (hB : Nat.card B = Nat.card F * (Nat.card F ^ 2 - 1) * Nat.card (scalarSubgroup B)) :
    Nat.card (B ⧸ scalarSubgroup B) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := scalarSubgroup B))
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (scalarSubgroup B)).symm.trans hB

theorem projectiveSpecialHom_range_index_two [Finite F] (hFodd : Odd (Nat.card F))
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) [Finite B]
    (hSB : conjugatedImageSL i b ≤ B)
    (hB : Nat.card B = Nat.card F * (Nat.card F ^ 2 - 1) * Nat.card (scalarSubgroup B)) :
    (projectiveSpecialHom i b B hSB).range.index = 2 := by
  apply Nat.eq_of_mul_eq_mul_right
    (Nat.card_pos (α := (projectiveSpecialHom i b B hSB).range))
  calc
    (projectiveSpecialHom i b B hSB).range.index *
        Nat.card (projectiveSpecialHom i b B hSB).range =
          Nat.card (B ⧸ scalarSubgroup B) := Subgroup.index_mul_card _
    _ = Nat.card F * (Nat.card F ^ 2 - 1) := card_matrix_overgroup_scalar_quotient B hB
    _ = 2 * Nat.card (projectiveSpecialHom i b B hSB).range := by
      rw [card_projectiveSpecialHom_range_of_odd hFodd i b B hSB]
      exact (Nat.mul_div_cancel'
        (ProjectiveTwoParameterUniqueness.numerator_even_of_odd hFodd)).symm

theorem matrix_overgroup_scalar_quotient_three [Finite F] (hF : Nat.card F = 3)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) [Finite B]
    (hSB : conjugatedImageSL i b ≤ B)
    (hB : Nat.card B = Nat.card F * (Nat.card F ^ 2 - 1) * Nat.card (scalarSubgroup B)) :
    Group.IsSolvable (B ⧸ scalarSubgroup B) ∧ Nat.card (B ⧸ scalarSubgroup B) = 24 := by
  have hFodd : Odd (Nat.card F) := by rw [hF]; decide
  have hi := projectiveSpecialHom_range_index_two hFodd i b B hSB hB
  let Q := (projectiveSpecialHom i b B hSB).range
  let : Q.Normal := Subgroup.normal_of_index_eq_two hi
  let : Group.IsSolvable Q := projectiveSpecialHom_range_three_isSolvable hF i b B hSB
  have hcard : Nat.card ((B ⧸ scalarSubgroup B) ⧸ Q) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hi
  let : IsCyclic ((B ⧸ scalarSubgroup B) ⧸ Q) := isCyclic_of_prime_card hcard
  refine ⟨(Group.isSolvable_iff_subgroup_quotient Q).mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  rw [card_matrix_overgroup_scalar_quotient B hB, hF]
  norm_num

theorem generalizedFitting_eq_of_selfCentralizing_component
    {G : Type u} [Group G] [Finite G] (Q : Subgroup G) (hQ : CFSG.IsComponent Q)
    (hC : Subgroup.centralizer (Q : Set G) = ⊥) : CFSG.generalizedFitting G = Q :=
  CFSG.generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot Q hQ hC

theorem generalizedFitting_eq_of_selfCentralizing_simple_normal
    {G : Type u} [Group G] [Finite G] (Q : Subgroup G) (hQn : Q.Normal)
    [IsSimpleGroup Q] (hQab : ∃ x y : Q, x * y ≠ y * x)
    (hC : Subgroup.centralizer (Q : Set G) = ⊥) : CFSG.generalizedFitting G = Q := by
  exact generalizedFitting_eq_of_selfCentralizing_component Q
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hQab).1, hQn.isSubnormal⟩ hC

theorem matrix_overgroup_generalizedFitting_eq_projectiveSpecial [Finite F]
    (hFodd : Odd (Nat.card F)) (hF : 5 ≤ Nat.card F) (i : F →+* E)
    (b : GeneralLinearGroup (Fin 2) E) (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    [Finite B] (hSB : conjugatedImageSL i b ≤ B)
    (hB : Nat.card B = Nat.card F * (Nat.card F ^ 2 - 1) * Nat.card (scalarSubgroup B)) :
    CFSG.generalizedFitting (B ⧸ scalarSubgroup B) =
      (projectiveSpecialHom i b B hSB).range := by
  let Q := (projectiveSpecialHom i b B hSB).range
  have hi := projectiveSpecialHom_range_index_two hFodd i b B hSB hB
  let : IsSimpleGroup Q := projectiveSpecialHom_range_isSimple (by omega) i b B hSB
  let : Group.IsPerfect Q := projectiveSpecialHom_range_isPerfect (by omega) i b B hSB
  have hnonab : ∃ x y : Q, x * y ≠ y * x := by
    simpa only [isMulCommutative_iff, not_forall] using Group.IsPerfect.not_isMulCommutative Q
  exact generalizedFitting_eq_of_selfCentralizing_simple_normal Q
    (Subgroup.normal_of_index_eq_two hi) hnonab
    (matrix_overgroup_projective_special_centralizer (by omega) i b B hSB)

theorem matrix_overgroup_generalizedFitting_full_conclusions
    {F E : Type} [Field F] [Finite F] [Field E] (p f : ℕ)
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hcard : Nat.card F = p ^ f) (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) [Finite B]
    (hSB : conjugatedImageSL i b ≤ B)
    (hB : Nat.card B = Nat.card F * (Nat.card F ^ 2 - 1) * Nat.card (scalarSubgroup B)) :
    let Gamma := B ⧸ scalarSubgroup B
    let L := CFSG.generalizedFitting Gamma
    IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
      Subgroup.centralizer (L : Set Gamma) = ⊥ ∧ L.index = 2 ∧
      StatedClassicalModel L .PSL 2 p f ∧ Nat.card L = p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∧
      ∀ (r a : ℕ), r.Prime → Odd r → 1 ≤ a → StatedClassicalModel L .PSL 2 r a →
        r ^ a = p ^ f ∧ r = p ∧ a = f := by
  dsimp only
  have hFodd : Odd (Nat.card F) := hcard ▸ hpodd.pow
  have hF : 5 ≤ Nat.card F := by rwa [hcard]
  rw [matrix_overgroup_generalizedFitting_eq_projectiveSpecial hFodd hF i b B hSB hB]
  let Q := (projectiveSpecialHom i b B hSB).range
  let : IsSimpleGroup Q := projectiveSpecialHom_range_isSimple (by omega) i b B hSB
  let : Group.IsPerfect Q := projectiveSpecialHom_range_isPerfect (by omega) i b B hSB
  have hnonab : ∃ x y : Q, x * y ≠ y * x := by
    simpa only [isMulCommutative_iff, not_forall] using Group.IsPerfect.not_isMulCommutative Q
  have hmodel := projectiveSpecialHom_range_statedClassicalModel p f hp hf hq hcard i b B hSB
  have hparams := ProjectiveTwoParameterUniqueness.stated_psl_two_order_and_parameter_uniqueness
    Q p f hp hpodd hf hq hmodel
  exact ⟨inferInstance, hnonab,
    matrix_overgroup_projective_special_centralizer (by omega) i b B hSB,
    projectiveSpecialHom_range_index_two hFodd i b B hSB hB, hmodel, hparams.2.1, hparams.2.2⟩

end CFSG.Wreathed.DegreeThreeModelFullCenter
