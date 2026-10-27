module

public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
public import CFSG.FeitThompson.Representations.SchurLemmaAlgebraicallyClosed
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module
open scoped ComplexConjugate

variable {P : Type*} [Group P]

section Scalars

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem Representation.apply_eq_smul_one_of_mem_center (ρ : Representation ℂ P V)
    [ρ.IsIrreducible] {z : P} (hz : z ∈ Subgroup.center P) :
    ρ z = (ρ.character z / ρ.character 1) • (1 : Module.End ℂ V) := by
  have hnt : Nontrivial V := Representation.nontrivial_of_isIrreducible ρ inferInstance
  have hcomm : ∀ g : P, Commute (ρ z) (ρ g) := by
    intro g
    have h1 : Commute z g := (Subgroup.mem_center_iff.mp hz g).symm
    exact h1.map ρ
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.exists_eq_smul_one_of_commute ρ (ρ z) hcomm
  have h1 : ρ.character 1 = (finrank ℂ V : ℂ) := ρ.char_one
  have hz' : ρ.character z = c * (finrank ℂ V : ℂ) := by
    rw [Representation.character, hc, map_smul, LinearMap.trace_one]
    simp
  have hne : (finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  rw [hc, hz', h1, mul_div_assoc, div_self hne, mul_one]

theorem Representation.character_mul_character_one_of_mem_center (ρ : Representation ℂ P V)
    [ρ.IsIrreducible] {y z : P} (hy : y ∈ Subgroup.center P) (hz : z ∈ Subgroup.center P) :
    ρ.character (y * z) * ρ.character 1 = ρ.character y * ρ.character z := by
  have hnt : Nontrivial V := Representation.nontrivial_of_isIrreducible ρ inferInstance
  have key : ρ (y * z) = ((ρ.character y / ρ.character 1) * (ρ.character z / ρ.character 1)) •
      (1 : Module.End ℂ V) := by
    rw [map_mul, Representation.apply_eq_smul_one_of_mem_center ρ hy,
      Representation.apply_eq_smul_one_of_mem_center ρ hz, smul_mul_smul_comm, mul_one]
  have h2 := Representation.apply_eq_smul_one_of_mem_center ρ (Subgroup.mul_mem _ hy hz)
  rw [key] at h2
  have hne : ρ.character 1 ≠ 0 := by
    rw [ρ.char_one]; exact Nat.cast_ne_zero.2 finrank_pos.ne'
  have h3 := (smul_left_injective ℂ (one_ne_zero (α := Module.End ℂ V)) h2).symm
  field_simp at h3
  linear_combination h3

end Scalars

noncomputable def scalarRep {X : Type*} [Group X] (l : X →* ℂ) : Representation ℂ X ℂ :=
  (Algebra.lsmul ℂ ℂ ℂ).toMonoidHom.comp l

theorem scalarRep_apply_eq_smul_one {X : Type*} [Group X] (l : X →* ℂ) (x : X) :
    scalarRep l x = l x • (1 : Module.End ℂ ℂ) := by
  ext; simp [scalarRep]

theorem character_scalarRep {X : Type*} [Group X] (l : X →* ℂ) :
    (scalarRep l).character = l := by
  funext x
  rw [Representation.character, scalarRep_apply_eq_smul_one, map_smul, LinearMap.trace_one]
  simp

theorem isIrreducible_scalarRep {X : Type*} [Group X] (l : X →* ℂ) :
    (scalarRep l).IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have h2 : finrank ℂ (scalarRep l).asModule = 1 := Module.finrank_self ℂ
  have := is_simple_module_of_finrank_eq_one (A := MonoidAlgebra ℂ X) h2
  exact ⟨⟩

theorem monoidHom_mem_Irr {X : Type*} [Group X] (l : X →* ℂ) : (l : X → ℂ) ∈ Irr X := by
  have := character_mem_Irr_of_isIrreducible (scalarRep l) (isIrreducible_scalarRep l)
  rwa [character_scalarRep] at this

theorem apply_mul_mul_apply_one_of_mem_center {θ : P → ℂ} (hθ : θ ∈ Irr P) {y z : P}
    (hy : y ∈ Subgroup.center P) (hz : z ∈ Subgroup.center P) :
    θ (y * z) * θ 1 = θ y * θ z := by
  obtain ⟨V, hV, rfl⟩ := mem_Irr.1 hθ
  have : Representation.IsIrreducible V.ρ := hV
  rw [fdRepCharacter_eq]
  exact Representation.character_mul_character_one_of_mem_center V.ρ hy hz

noncomputable def centralLinearChar {θ : P → ℂ} (hθ : θ ∈ Irr P) {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) : Z →* ℂ where
  toFun z := θ (z : P) / θ 1
  map_one' := by simp [div_self (apply_one_ne_zero_of_mem_Irr hθ)]
  map_mul' y z := by
    have h := apply_mul_mul_apply_one_of_mem_center hθ (hZ y.2) (hZ z.2)
    have hne : θ 1 ≠ 0 := apply_one_ne_zero_of_mem_Irr hθ
    field_simp
    push_cast
    linear_combination h

theorem centralLinearChar_apply {θ : P → ℂ} (hθ : θ ∈ Irr P) {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) (z : Z) :
    centralLinearChar hθ hZ z = θ (z : P) / θ 1 := (rfl)

theorem centralLinearChar_mem_Irr {θ : P → ℂ} (hθ : θ ∈ Irr P) {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) : ((centralLinearChar hθ hZ : Z → ℂ)) ∈ Irr Z :=
  monoidHom_mem_Irr _

theorem apply_eq_apply_one_mul_centralLinearChar {θ : P → ℂ} (hθ : θ ∈ Irr P) {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) (z : Z) :
    θ (z : P) = θ 1 * centralLinearChar hθ hZ z := by
  rw [centralLinearChar_apply, mul_div_cancel₀ _ (apply_one_ne_zero_of_mem_Irr hθ)]

theorem resClassFun_eq_smul_centralLinearChar {θ : P → ℂ} (hθ : θ ∈ Irr P) {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) :
    resClassFun Z θ = θ 1 • ((centralLinearChar hθ hZ : Z → ℂ)) := by
  funext z
  rw [resClassFun_apply, Pi.smul_apply, smul_eq_mul]
  exact apply_eq_apply_one_mul_centralLinearChar hθ hZ z

theorem existsUnique_linear_char_of_mem_Irr {θ : P → ℂ} (hθ : θ ∈ Irr P) {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) :
    ∃! l : Z → ℂ, l ∈ Irr Z ∧ l 1 = 1 ∧ ∀ z : Z, θ (z : P) = θ 1 * l z := by
  refine ⟨(centralLinearChar hθ hZ : Z → ℂ), ⟨centralLinearChar_mem_Irr hθ hZ, map_one _,
    apply_eq_apply_one_mul_centralLinearChar hθ hZ⟩, ?_⟩
  rintro l ⟨-, -, hl⟩
  funext z
  rw [centralLinearChar_apply, hl z, mul_div_cancel_left₀ _ (apply_one_ne_zero_of_mem_Irr hθ)]

theorem centralLinearChar_ne_one_iff {θ : P → ℂ} (hθ : θ ∈ Irr P) {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) :
    ((centralLinearChar hθ hZ : Z → ℂ)) ≠ 1 ↔ ¬ (Z : Set P) ⊆ charValueKernel θ := by
  have hne : θ 1 ≠ 0 := apply_one_ne_zero_of_mem_Irr hθ
  rw [not_iff_not, funext_iff]
  refine ⟨fun h x hx => mem_charValueKernel.2 ?_, fun h z => ?_⟩
  · have h2 := h ⟨x, hx⟩
    rwa [centralLinearChar_apply, Pi.one_apply, div_eq_one_iff_eq hne] at h2
  · rw [centralLinearChar_apply, Pi.one_apply, div_eq_one_iff_eq hne]
    exact mem_charValueKernel.1 (h z.2)

open scoped Classical in
noncomputable def centralIrrFinset [Finite P] (Z : Subgroup P) (l : Z → ℂ) : Finset (P → ℂ) :=
  {θ ∈ irrFinset P | ∀ z : Z, θ (z : P) = θ 1 * l z}

theorem mem_centralIrrFinset [Finite P] {Z : Subgroup P} {l : Z → ℂ} {θ : P → ℂ} :
    θ ∈ centralIrrFinset Z l ↔ θ ∈ Irr P ∧ ∀ z : Z, θ (z : P) = θ 1 * l z := by
  classical
  rw [centralIrrFinset, Finset.mem_filter, mem_irrFinset]

theorem centralIrrFinset_subset [Finite P] {Z : Subgroup P} (l : Z → ℂ) :
    centralIrrFinset Z l ⊆ irrFinset P := fun _ h =>
  mem_irrFinset.2 (mem_centralIrrFinset.1 h).1

theorem centralLinearChar_eq_iff_mem_centralIrrFinset [Finite P] {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) {l : Z → ℂ} {θ : P → ℂ} (hθ : θ ∈ Irr P) :
    ((centralLinearChar hθ hZ : Z → ℂ)) = l ↔ θ ∈ centralIrrFinset Z l := by
  rw [mem_centralIrrFinset]
  refine ⟨fun h => ⟨hθ, fun z => by
      rw [← h]; exact apply_eq_apply_one_mul_centralLinearChar hθ hZ z⟩,
    fun h => funext fun z => ?_⟩
  exact mul_left_cancel₀ (apply_one_ne_zero_of_mem_Irr hθ)
    ((apply_eq_apply_one_mul_centralLinearChar hθ hZ z).symm.trans (h.2 z))

theorem cfInner_indClassFun_eq_ite [Fintype P] {Z : Subgroup P} (hZ : Z ≤ Subgroup.center P)
    {lam : Z → ℂ} (hlam : lam ∈ Irr Z) {θ : P → ℂ} (hθ : θ ∈ Irr P) :
    cfInner (indClassFun Z lam) θ = if θ ∈ centralIrrFinset Z lam then θ 1 else 0 := by
  classical
  have : Fintype Z := Fintype.ofFinite _
  have hbase : cfInner (indClassFun Z lam) θ
      = θ 1 * (if lam = ((centralLinearChar hθ hZ : Z → ℂ)) then (1 : ℂ) else 0) := by
    rw [cfInner_indClassFun Z lam (Irr_subset_classFun hθ),
      resClassFun_eq_smul_centralLinearChar hθ hZ, cfInner_smul_right,
      cfInner_eq_ite_of_mem_Irr hlam (centralLinearChar_mem_Irr hθ hZ),
      conj_apply_one_of_mem_Irr hθ]
  by_cases h : θ ∈ centralIrrFinset Z lam
  · rw [if_pos h, hbase,
      if_pos ((centralLinearChar_eq_iff_mem_centralIrrFinset hZ hθ).2 h).symm, mul_one]
  · rw [if_neg h, hbase,
      if_neg fun h' => h ((centralLinearChar_eq_iff_mem_centralIrrFinset hZ hθ).1 h'.symm),
      mul_zero]

theorem indClassFun_eq_sum_centralIrrFinset [Fintype P] {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) {lam : Z → ℂ} (hlam : lam ∈ Irr Z) :
    indClassFun Z lam = ∑ θ ∈ centralIrrFinset Z lam, θ 1 • θ := by
  classical
  obtain ⟨V, -, hV⟩ := mem_Irr.1 hlam
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_indClassFun Z V
  rw [hV] at hW
  obtain ⟨m, hm⟩ := exists_character_eq_sum_nsmul (V := W.V) W.ρ
  rw [← fdRepCharacter_eq, hW] at hm
  have hmval : ∀ χ : irrFinset P, ((m χ : ℂ)) • (χ : P → ℂ)
      = if (χ : P → ℂ) ∈ centralIrrFinset Z lam then (χ : P → ℂ) 1 • (χ : P → ℂ) else 0 := by
    intro χ
    have hχ : (χ : P → ℂ) ∈ Irr P := mem_irrFinset.1 χ.2
    have h1 := cfInner_eq_multiplicity hm χ
    rw [cfInner_indClassFun_eq_ite hZ hlam hχ] at h1
    rw [← h1]
    by_cases h : (χ : P → ℂ) ∈ centralIrrFinset Z lam
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_smul]
  rw [hm, Finset.sum_congr rfl fun χ _ => hmval χ,
    Finset.sum_coe_sort (irrFinset P) fun χ =>
      if χ ∈ centralIrrFinset Z lam then χ 1 • χ else (0 : P → ℂ),
    Finset.sum_ite_mem, Finset.inter_eq_right.2 (centralIrrFinset_subset lam)]

theorem sum_sq_apply_one_centralIrrFinset [Finite P] {Z : Subgroup P}
    (hZ : Z ≤ Subgroup.center P) {lam : Z → ℂ} (hlam : lam ∈ Irr Z) (hlam1 : lam 1 = 1) :
    ∑ θ ∈ centralIrrFinset Z lam, θ 1 ^ 2 = (Z.index : ℂ) := by
  have : Fintype P := Fintype.ofFinite P
  have h := congrFun (indClassFun_eq_sum_centralIrrFinset hZ hlam) 1
  rw [NormalInducedFamily.indClassFun_one_eq_index_mul, hlam1, mul_one, Finset.sum_apply] at h
  rw [h]
  exact Finset.sum_congr rfl fun θ _ => by rw [Pi.smul_apply, smul_eq_mul, sq]

end CFSG.FeitThompson
