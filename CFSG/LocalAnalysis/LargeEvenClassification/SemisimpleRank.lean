module

public import CFSG.LocalAnalysis.LargeEvenClassification.BinaryRank
public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianIrreducible
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LargeEvenClassification.Helpers

universe fieldUniverse groupUniverse spaceUniverse

@[expose] noncomputable def groupAlgebraModuleAction {ScalarField : Type fieldUniverse} [Field ScalarField]
    {Acting : Type groupUniverse} [Group Acting] (Space : Type spaceUniverse)
    [AddCommGroup Space] [Module ScalarField Space]
    [Module (MonoidAlgebra ScalarField Acting) Space]
    [IsScalarTower ScalarField (MonoidAlgebra ScalarField Acting) Space] :
    Acting →* (Space ≃ₗ[ScalarField] Space) where
  toFun element :=
    { toFun := fun vector => (MonoidAlgebra.of ScalarField Acting) element • vector
      invFun := fun vector => (MonoidAlgebra.of ScalarField Acting) element⁻¹ • vector
      left_inv := by
        intro vector
        dsimp only
        rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      right_inv := by
        intro vector
        dsimp only
        rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
      map_add' := smul_add _
      map_smul' := by
        intro scalar vector
        exact smul_comm _ _ _ }
  map_one' := by
    ext vector
    change (MonoidAlgebra.of ScalarField Acting) 1 • vector = vector
    rw [map_one, one_smul]
  map_mul' := by
    intro first second
    ext vector
    change (MonoidAlgebra.of ScalarField Acting) (first * second) • vector =
      (MonoidAlgebra.of ScalarField Acting) first •
        (MonoidAlgebra.of ScalarField Acting) second • vector
    rw [map_mul, mul_smul]

theorem simple_groupAlgebra_action_cyclic {ScalarField : Type fieldUniverse} [Field ScalarField]
    {Acting : Type groupUniverse} [CommGroup Acting] [Finite Acting]
    (Space : Type spaceUniverse) [AddCommGroup Space] [Module ScalarField Space]
    [Module (MonoidAlgebra ScalarField Acting) Space]
    [IsScalarTower ScalarField (MonoidAlgebra ScalarField Acting) Space]
    [IsSimpleModule (MonoidAlgebra ScalarField Acting) Space] :
    IsCyclic (groupAlgebraModuleAction (ScalarField := ScalarField) (Acting := Acting) Space).range := by
  let annihilator := Module.annihilator (MonoidAlgebra ScalarField Acting) Space
  let : annihilator.IsMaximal := IsSimpleModule.annihilator_isMaximal
    (R := MonoidAlgebra ScalarField Acting) (M := Space)
  let : Field ((MonoidAlgebra ScalarField Acting) ⧸ annihilator) := Ideal.Quotient.field annihilator
  let scalarAction := ((Ideal.Quotient.mk annihilator).toMonoidHom.comp
    (MonoidAlgebra.of ScalarField Acting)).toHomUnits
  let action := groupAlgebraModuleAction (ScalarField := ScalarField) (Acting := Acting) Space
  have hkernel : scalarAction.ker = action.ker := by
    rw [MonoidHom.ker_toHomUnits]
    ext element
    change Ideal.Quotient.mk annihilator ((MonoidAlgebra.of ScalarField Acting) element) = 1 ↔
      action element = 1
    rw [← map_one (Ideal.Quotient.mk annihilator), Ideal.Quotient.eq, Module.mem_annihilator]
    constructor
    · intro hzero
      ext vector
      change (MonoidAlgebra.of ScalarField Acting) element • vector = vector
      exact sub_eq_zero.mp (by simpa only [sub_smul, one_smul] using hzero vector)
    · intro hzero vector
      have hfixed := congrArg (fun automorphism : Space ≃ₗ[ScalarField] Space =>
        automorphism vector) hzero
      change (MonoidAlgebra.of ScalarField Acting) element • vector = vector at hfixed
      simpa only [sub_smul, one_smul] using sub_eq_zero.mpr hfixed
  let equivalence := QuotientGroup.quotientMulEquivOfEq hkernel.symm
  let embedding := ((Units.coeHom ((MonoidAlgebra ScalarField Acting) ⧸ annihilator)).comp
    (QuotientGroup.kerLift scalarAction)).comp equivalence.toMonoidHom
  have hinjective : Function.Injective embedding :=
    Units.val_injective.comp
      ((QuotientGroup.kerLift_injective scalarAction).comp equivalence.injective)
  let : IsCyclic (Acting ⧸ action.ker) := isCyclic_of_injective_ringHom embedding hinjective
  exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange action).toMonoidHom
    (QuotientGroup.quotientKerEquivRange action).surjective

theorem binary_maschke_decomposition {Acting : Type groupUniverse} [Group Acting] [Finite Acting]
    [NeZero (Nat.card Acting : ZMod 2)] (Space : Type spaceUniverse)
    [AddCommGroup Space] [Module (ZMod 2) Space] [Finite Space]
    [Module (MonoidAlgebra (ZMod 2) Acting) Space]
    [IsScalarTower (ZMod 2) (MonoidAlgebra (ZMod 2) Acting) Space] :
    ∃ (count : ℕ) (summands : Fin count → Submodule (MonoidAlgebra (ZMod 2) Acting) Space)
      (_ : Space ≃ₗ[MonoidAlgebra (ZMod 2) Acting] Π₀ index, summands index),
      (∀ index, IsSimpleModule (MonoidAlgebra (ZMod 2) Acting) (summands index)) ∧
      Module.finrank (ZMod 2) Space = ∑ index, Module.finrank (ZMod 2) (summands index) := by
  let : Module.Finite (MonoidAlgebra (ZMod 2) Acting) Space :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) (MonoidAlgebra (ZMod 2) Acting) Space
  obtain ⟨count, summands, equivalence, hsimple⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (MonoidAlgebra (ZMod 2) Acting) Space
  refine ⟨count, summands, equivalence, hsimple, ?_⟩
  rw [(equivalence.restrictScalars (ZMod 2)).finrank_eq,
    (DFinsupp.linearEquivFunOnFintype (R := ZMod 2) (M := fun index => summands index)).finrank_eq,
    Module.finrank_pi_fintype]

theorem cyclic_action_card_dvd_exponent {Acting : Type groupUniverse} [Group Acting]
    {Target : Type spaceUniverse} [Group Target] (action : Acting →* Target)
    [IsCyclic action.range] {exponent : ℕ} (hexponent : ∀ element : Acting, element ^ exponent = 1) :
    Nat.card action.range ∣ exponent := by
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro element
  obtain ⟨source, hsource⟩ := element.property
  apply Subtype.ext
  change (element : Target) ^ exponent = 1
  rw [← hsource, ← map_pow, hexponent source, map_one]

theorem nontrivial_binary_action_dimension {Acting : Type groupUniverse} [Group Acting]
    {Space : Type spaceUniverse} [AddCommGroup Space] [Module (ZMod 2) Space] [Finite Space]
    (action : Acting →* (Space ≃ₗ[ZMod 2] Space)) (hnontrivial : Nat.card action.range ≠ 1) :
    2 ≤ Module.finrank (ZMod 2) Space := by
  by_contra hsmall
  have hdimension : Module.finrank (ZMod 2) Space = 0 ∨ Module.finrank (ZMod 2) Space = 1 := by omega
  have hautCard : Nat.card (Space ≃ₗ[ZMod 2] Space) = 1 := by
    rw [card_linear_aut_binary, Matrix.card_GL_field]
    rcases hdimension with hzero | hone
    · rw [hzero]
      norm_num
    · rw [hone]
      norm_num [Fin.prod_univ_succ]
  have hdivides := card_dvd_of_injective_hom action.range.subtype Subtype.val_injective
  rw [hautCard] at hdivides
  exact hnontrivial (Nat.eq_one_of_dvd_one hdivides)

theorem binary_simple_action_card_bound {Acting : Type groupUniverse} [CommGroup Acting]
    [Finite Acting] (Space : Type spaceUniverse) [AddCommGroup Space]
    [Module (ZMod 2) Space] [Finite Space] [Module (MonoidAlgebra (ZMod 2) Acting) Space]
    [IsScalarTower (ZMod 2) (MonoidAlgebra (ZMod 2) Acting) Space]
    [IsSimpleModule (MonoidAlgebra (ZMod 2) Acting) Space] {prime : ℕ}
    (hprime : prime.Prime) (hexponent : ∀ element : Acting, element ^ prime = 1) :
    let action := groupAlgebraModuleAction (ScalarField := ZMod 2) (Acting := Acting) Space
    let cost := if Nat.card action.range = 1 then 0 else 1
    Nat.card action.range ≤ prime ^ cost ∧ 2 * cost ≤ Module.finrank (ZMod 2) Space := by
  dsimp only
  let action := groupAlgebraModuleAction (ScalarField := ZMod 2) (Acting := Acting) Space
  let : IsCyclic action.range := simple_groupAlgebra_action_cyclic Space
  have hdivides := cyclic_action_card_dvd_exponent action hexponent
  split_ifs with htrivial
  · simp only [htrivial, pow_zero, mul_zero, le_refl, zero_le, and_self]
  · simp only [pow_one, mul_one]
    exact ⟨Nat.le_of_dvd hprime.pos hdivides, nontrivial_binary_action_dimension action htrivial⟩

theorem faithful_elementary_binary_module_dimension {Acting : Type groupUniverse}
    [CommGroup Acting] [Finite Acting] (Space : Type spaceUniverse) [AddCommGroup Space]
    [Module (ZMod 2) Space] [Finite Space] [Module (MonoidAlgebra (ZMod 2) Acting) Space]
    [IsScalarTower (ZMod 2) (MonoidAlgebra (ZMod 2) Acting) Space] {prime rank : ℕ}
    (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hexponent : ∀ element : Acting, element ^ prime = 1) (hcard : Nat.card Acting = prime ^ rank)
    (hinjective : Function.Injective
      (groupAlgebraModuleAction (ScalarField := ZMod 2) (Acting := Acting) Space)) :
    2 * rank ≤ Module.finrank (ZMod 2) Space := by
  classical
  let : NeZero (Nat.card Acting : ZMod 2) := ⟨by
    intro hzero
    have htwoDivides : 2 ∣ prime ^ rank := hcard ▸ (ZMod.natCast_eq_zero_iff _ _).mp hzero
    have htwoPrime : 2 ∣ prime := Nat.prime_two.dvd_of_dvd_pow htwoDivides
    exact hodd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp htwoPrime).symm⟩
  obtain ⟨count, summands, equivalence, hsimple, hdimension⟩ :=
    binary_maschke_decomposition (Acting := Acting) Space
  let : ∀ index, IsSimpleModule (MonoidAlgebra (ZMod 2) Acting) (summands index) := hsimple
  let actions := fun index =>
    groupAlgebraModuleAction (ScalarField := ZMod 2) (Acting := Acting) (summands index)
  let costs := fun index => if Nat.card (actions index).range = 1 then 0 else 1
  let : ∀ index, Finite (actions index).range := fun index =>
    Finite.of_surjective (actions index).rangeRestrict (actions index).rangeRestrict_surjective
  have hbounds : ∀ index, Nat.card (actions index).range ≤ prime ^ costs index ∧
      2 * costs index ≤ Module.finrank (ZMod 2) (summands index) := by
    intro index
    exact binary_simple_action_card_bound (summands index) hprime hexponent
  let embedding := MonoidHom.pi (fun index => (actions index).rangeRestrict)
  have hembedding : Function.Injective embedding := by
    intro first second heq
    apply hinjective
    ext vector
    change (MonoidAlgebra.of (ZMod 2) Acting) first • vector =
      (MonoidAlgebra.of (ZMod 2) Acting) second • vector
    apply equivalence.injective
    rw [equivalence.map_smul, equivalence.map_smul]
    apply DFinsupp.ext
    intro index
    have hcomponent : actions index first = actions index second :=
      congrArg (fun tuple => (tuple index : summands index ≃ₗ[ZMod 2] summands index)) heq
    exact congrArg (fun automorphism : summands index ≃ₗ[ZMod 2] summands index =>
      automorphism (equivalence vector index)) hcomponent
  have horder : prime ^ rank ≤ prime ^ ∑ index, costs index := by
    calc
      prime ^ rank = Nat.card Acting := hcard.symm
      _ ≤ Nat.card (∀ index, (actions index).range) :=
        Nat.card_le_card_of_injective embedding hembedding
      _ = ∏ index, Nat.card (actions index).range := Nat.card_pi
      _ ≤ ∏ index, prime ^ costs index := Finset.prod_le_prod (fun index _ => (hbounds index).1)
      _ = prime ^ ∑ index, costs index := Finset.prod_pow_eq_pow_sum _ _ _
  have hrank : rank ≤ ∑ index, costs index := (Nat.pow_le_pow_iff_right hprime.one_lt).mp horder
  calc
    2 * rank ≤ 2 * ∑ index, costs index := Nat.mul_le_mul_left 2 hrank
    _ = ∑ index, 2 * costs index := Finset.mul_sum _ _ _
    _ ≤ ∑ index, Module.finrank (ZMod 2) (summands index) :=
      Finset.sum_le_sum (fun index _ => (hbounds index).2)
    _ = Module.finrank (ZMod 2) Space := hdimension.symm

theorem faithful_elementary_binary_dimension {Acting : Type groupUniverse} [CommGroup Acting]
    [Finite Acting] {Space : Type spaceUniverse} [AddCommGroup Space] [Module (ZMod 2) Space]
    [Finite Space] {prime rank : ℕ} (hprime : prime.Prime) (hodd : prime ≠ 2)
    (hexponent : ∀ element : Acting, element ^ prime = 1) (hcard : Nat.card Acting = prime ^ rank)
    (action : Acting →* (Space ≃ₗ[ZMod 2] Space)) (hinjective : Function.Injective action) :
    2 * rank ≤ Module.finrank (ZMod 2) Space := by
  let representation := linearActionRepresentation action
  let : Finite representation.asModule :=
    Finite.of_equiv Space representation.asModuleEquiv.symm.toEquiv
  have hmoduleInjective : Function.Injective
      (groupAlgebraModuleAction (ScalarField := ZMod 2) (Acting := Acting) representation.asModule) := by
    intro first second heq
    apply hinjective
    ext vector
    have hfixed := congrArg (fun automorphism : representation.asModule ≃ₗ[ZMod 2]
        representation.asModule => representation.asModuleEquiv
          (automorphism (representation.asModuleEquiv.symm vector))) heq
    change representation.asModuleEquiv ((MonoidAlgebra.of (ZMod 2) Acting) first •
        representation.asModuleEquiv.symm vector) =
      representation.asModuleEquiv ((MonoidAlgebra.of (ZMod 2) Acting) second •
        representation.asModuleEquiv.symm vector) at hfixed
    rw [representation.asModuleEquiv_map_smul, representation.asModuleEquiv_map_smul,
      representation.asAlgebraHom_of, representation.asAlgebraHom_of,
      representation.asModuleEquiv.apply_symm_apply] at hfixed
    exact hfixed
  have hdimension := faithful_elementary_binary_module_dimension representation.asModule hprime hodd
    hexponent hcard hmoduleInjective
  exact representation.asModuleEquiv.finrank_eq ▸ hdimension

end CFSG.LargeEvenClassification.Helpers
