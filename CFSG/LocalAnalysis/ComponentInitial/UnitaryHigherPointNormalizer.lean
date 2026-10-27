module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIntrinsicPoints
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherStabilizerNormalizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.StabilizerNormalizer
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

abbrev lineNormalizer (h : UnitaryFieldData p f K) (r ε : ℕ) :
    Subgroup (Equiv.Perm (hypIsotropicLines h r ε)) :=
  Subgroup.normalizer ((hypProjLineAction h r ε).range : Set (Equiv.Perm (hypIsotropicLines h r ε)))

variable (h : UnitaryFieldData p f K)

@[expose, instance_reducible] noncomputable def hypProjLineMulAction :
    MulAction (hypPSU h r ε) (hypIsotropicLines h r ε) :=
  MulAction.compHom _ (hypProjLineAction h r ε)

attribute [local instance] hypProjLineMulAction

theorem toPermHom_hypProjLine :
    MulAction.toPermHom (hypPSU h r ε) (hypIsotropicLines h r ε) = hypProjLineAction h r ε :=
  MonoidHom.ext fun _ => Equiv.ext fun _ => rfl

theorem faithfulSMul_hypProjLine (hn : 2 ≤ 2 * r + ε) :
    FaithfulSMul (hypPSU h r ε) (hypIsotropicLines h r ε) :=
  ⟨fun hxy => hypProjLineAction_injective h hn (Equiv.ext hxy)⟩

theorem stabilizer_hypProjLine (L : hypIsotropicLines h r ε) :
    MulAction.stabilizer (hypPSU h r ε) L =
      projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K)) := by
  ext x
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε x
  rw [MulAction.mem_stabilizer_iff, ← Subgroup.mem_comap, comap_projIsoStabilizer,
    mem_isoStabilizer]
  exact ⟨fun hg => congrArg Subtype.val hg, fun hg => Subtype.ext hg⟩

theorem stabilizer_hypProjLine_injective (hr : 1 ≤ r) (hε : ε ≤ 1) :
    Function.Injective (MulAction.stabilizer (hypPSU h r ε) :
      hypIsotropicLines h r ε → Subgroup (hypPSU h r ε)) := by
  intro L L' hLL'
  obtain ⟨-, -, hinj⟩ := unitary_maximal_parabolics h hr hε
  refine Subtype.ext (hinj (ne_bot_and_isotropic_of_mem_hypIsotropicLines h L.2)
    (ne_bot_and_isotropic_of_mem_hypIsotropicLines h L'.2) ?_)
  rw [← stabilizer_hypProjLine, ← stabilizer_hypProjLine]
  exact hLL'

theorem exists_map_stabilizer_hypProjLine (hr : 1 ≤ r) (hε : ε ≤ 1)
    (α : MulAut (hypPSU h r ε)) (L : hypIsotropicLines h r ε) :
    ∃ L' : hypIsotropicLines h r ε, (MulAction.stabilizer (hypPSU h r ε) L).map α.toMonoidHom =
      MulAction.stabilizer (hypPSU h r ε) L' := by
  obtain ⟨-, -, -, hφ⟩ := unitary_intrinsic_point_stabilizers h hr hε
  obtain ⟨φ, hφ⟩ := hφ α
  refine ⟨φ L, ?_⟩
  rw [stabilizer_hypProjLine, stabilizer_hypProjLine]
  exact (hφ L (φ L)).mpr rfl

@[expose] noncomputable def linePerm (hr : 1 ≤ r) (hε : ε ≤ 1) :
    MulAut (hypPSU h r ε) →* Equiv.Perm (hypIsotropicLines h r ε) :=
  stabPerm (stabilizer_hypProjLine_injective h hr hε) (exists_map_stabilizer_hypProjLine h hr hε)

variable (hr : 1 ≤ r) (hε : ε ≤ 1)

theorem map_projIsoStabilizer_linePerm (α : MulAut (hypPSU h r ε))
    (L : hypIsotropicLines h r ε) :
    (projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K))).map α.toMonoidHom =
      projIsoStabilizer h r ε (linePerm h hr hε α L : Submodule K (HypIndex r ε → K)) := by
  rw [← stabilizer_hypProjLine, ← stabilizer_hypProjLine]
  exact map_stabilizer_stabPerm _ _ α L

theorem eq_linePerm_iff (α : MulAut (hypPSU h r ε)) (π : Equiv.Perm (hypIsotropicLines h r ε)) :
    π = linePerm h hr hε α ↔ ∀ L : hypIsotropicLines h r ε,
      (projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K))).map α.toMonoidHom =
        projIsoStabilizer h r ε (π L : Submodule K (HypIndex r ε → K)) := by
  rw [linePerm, eq_stabPerm_iff]
  simp only [stabilizer_hypProjLine]

theorem linePerm_conj (α : MulAut (hypPSU h r ε)) (g : hypPSU h r ε) :
    linePerm h hr hε α * hypProjLineAction h r ε g * (linePerm h hr hε α)⁻¹ =
      hypProjLineAction h r ε (α g) := by
  rw [← toPermHom_hypProjLine]
  exact stabPerm_conj _ _ α g

theorem linePerm_injective : Function.Injective (linePerm h hr hε) := by
  have := faithfulSMul_hypProjLine h (r := r) (ε := ε) (by omega)
  exact stabPerm_injective _ _

theorem range_linePerm : (linePerm h hr hε).range = lineNormalizer h r ε := by
  have := faithfulSMul_hypProjLine h (r := r) (ε := ε) (by omega)
  rw [lineNormalizer, ← toPermHom_hypProjLine]
  exact range_stabPerm _ _

theorem map_inner_linePerm :
    (inner (hypPSU h r ε)).map (linePerm h hr hε) = (hypProjLineAction h r ε).range := by
  rw [← toPermHom_hypProjLine]
  exact map_inner_stabPerm _ _

@[expose] noncomputable def linePermEquiv : MulAut (hypPSU h r ε) ≃* lineNormalizer h r ε :=
  (MonoidHom.ofInjective (linePerm_injective h hr hε)).trans
    (MulEquiv.subgroupCongr (range_linePerm h hr hε))

theorem coe_linePermEquiv (α : MulAut (hypPSU h r ε)) :
    (linePermEquiv h hr hε α : Equiv.Perm (hypIsotropicLines h r ε)) = linePerm h hr hε α :=
  rfl

theorem map_inner_linePermEquiv :
    (inner (hypPSU h r ε)).map (linePermEquiv h hr hε : MulAut (hypPSU h r ε) →* _) =
      (hypProjLineAction h r ε).range.subgroupOf (lineNormalizer h r ε) := by
  ext y
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact (map_inner_linePerm h hr hε).le ⟨α, hα, rfl⟩
  · intro hy
    obtain ⟨α, hα, hy'⟩ := (map_inner_linePerm h hr hε).ge hy
    exact ⟨α, hα, Subtype.ext hy'⟩

@[expose] noncomputable def linePermOuterEquiv :
    Outer (hypPSU h r ε) ≃*
      lineNormalizer h r ε ⧸ (hypProjLineAction h r ε).range.subgroupOf (lineNormalizer h r ε) :=
  QuotientGroup.congr (inner _) _ (linePermEquiv h hr hε) (map_inner_linePermEquiv h hr hε)

theorem linePermOuterEquiv_mk (α : MulAut (hypPSU h r ε)) :
    linePermOuterEquiv h hr hε (α : Outer (hypPSU h r ε)) =
      ((linePermEquiv h hr hε α : lineNormalizer h r ε) : lineNormalizer h r ε ⧸
        (hypProjLineAction h r ε).range.subgroupOf (lineNormalizer h r ε)) :=
  QuotientGroup.congr_mk _ _ _ _ α

theorem unitary_point_permutation_normalizer :
    Function.Injective (hypProjLineAction h r ε) ∧
    (∀ (α : MulAut (hypPSU h r ε)) (π : Equiv.Perm (hypIsotropicLines h r ε)),
      π = linePerm h hr hε α ↔ ∀ L : hypIsotropicLines h r ε,
        (projIsoStabilizer h r ε (L : Submodule K (HypIndex r ε → K))).map α.toMonoidHom =
          projIsoStabilizer h r ε (π L : Submodule K (HypIndex r ε → K))) ∧
    Function.Injective (linePerm h hr hε) ∧
    (linePerm h hr hε).range = lineNormalizer h r ε ∧
    (∀ α : MulAut (hypPSU h r ε),
      (linePermEquiv h hr hε α : Equiv.Perm (hypIsotropicLines h r ε)) = linePerm h hr hε α) ∧
    (∀ (α : MulAut (hypPSU h r ε)) (g : hypPSU h r ε),
      linePerm h hr hε α * hypProjLineAction h r ε g * (linePerm h hr hε α)⁻¹ =
        hypProjLineAction h r ε (α g)) ∧
    (inner (hypPSU h r ε)).map (linePerm h hr hε) = (hypProjLineAction h r ε).range ∧
    ∀ α : MulAut (hypPSU h r ε), linePermOuterEquiv h hr hε (α : Outer (hypPSU h r ε)) =
      ((linePermEquiv h hr hε α : lineNormalizer h r ε) : lineNormalizer h r ε ⧸
        (hypProjLineAction h r ε).range.subgroupOf (lineNormalizer h r ε)) :=
  ⟨hypProjLineAction_injective h (by omega), eq_linePerm_iff h hr hε, linePerm_injective h hr hε,
    range_linePerm h hr hε, coe_linePermEquiv h hr hε, linePerm_conj h hr hε,
    map_inner_linePerm h hr hε, linePermOuterEquiv_mk h hr hε⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
