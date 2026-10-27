module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionBasic
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointAction

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

@[expose] def scalarKernel : Subgroup (elementaryGroup Q) :=
  (scalars K V).subgroupOf (elementaryGroup Q)

instance scalarKernel_normal : (scalarKernel Q).Normal := by
  unfold scalarKernel
  infer_instance

abbrev ProjectiveGroup : Type _ := elementaryGroup Q ⧸ scalarKernel Q

theorem mem_scalarKernel_iff_units (g : elementaryGroup Q) :
    g ∈ scalarKernel Q ↔ ∃ a : Kˣ, ∀ x : V, (g : V ≃ₗ[K] V) x = (a : K) • x := by
  change (g : V ≃ₗ[K] V) ∈ scalars K V ↔ _
  rw [mem_scalars]
  constructor
  · rintro ⟨c, hc⟩
    rcases subsingleton_or_nontrivial V with hV | hV
    · exact ⟨1, fun x => hV.elim _ _⟩
    · let := hV
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      have hc0 : c ≠ 0 := by
        intro h
        have hg := hc x
        rw [h, zero_smul, LinearEquiv.map_eq_zero_iff] at hg
        exact hx hg
      exact ⟨Units.mk0 c hc0, hc⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩

theorem scalarKernel_le_actionKernel : scalarKernel Q ≤ (elementaryPointAction Q).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro L
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  obtain ⟨a, ha⟩ := (mem_scalarKernel_iff_units Q g).mp hg
  exact smul_pointMk_of_apply_eq_smul hx hx hQx hQx (ha x)

@[expose] noncomputable def projectivePointAction :
    ProjectiveGroup Q →* Equiv.Perm (Points Q) :=
  QuotientGroup.lift (scalarKernel Q) (elementaryPointAction Q)
    (scalarKernel_le_actionKernel Q)

noncomputable instance projectiveMulAction : MulAction (ProjectiveGroup Q) (Points Q) :=
  MulAction.compHom (Points Q) (projectivePointAction Q)

theorem quotient_smul (g : elementaryGroup Q) (L : Points Q) :
    (QuotientGroup.mk' (scalarKernel Q) g) • L = g • L := rfl

theorem projectivePointAction_mk (g : elementaryGroup Q) :
    projectivePointAction Q (QuotientGroup.mk' (scalarKernel Q) g) =
      elementaryPointAction Q g := rfl

theorem actionKernel_eq_of_hypPairs {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) :
    (elementaryPointAction Q).ker = scalarKernel Q := by
  apply le_antisymm
  · intro g hg
    change (g : V ≃ₗ[K] V) ∈ scalars K V
    apply mem_scalars_of_forall_singular h₁₂
      (elementaryGroup_le_orthogonalGroup Q g.property)
    intro x hx hQx
    have hfix : g • pointMk x hx hQx = pointMk x hx hQx := by
      have h := congrArg (fun p : Equiv.Perm (Points Q) => p (pointMk x hx hQx))
        (MonoidHom.mem_ker.mp hg)
      exact h
    rw [smul_pointMk, pointMk_eq_iff] at hfix
    obtain ⟨a, ha⟩ := hfix
    exact ⟨a, ha.symm⟩
  · exact scalarKernel_le_actionKernel Q

theorem projective_faithful_of_hypPairs {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) :
    FaithfulSMul (ProjectiveGroup Q) (Points Q) := by
  apply faithfulSMul_iff.mpr
  intro p hp
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
  rw [QuotientGroup.eq_one_iff, ← actionKernel_eq_of_hypPairs Q h₁₂,
    MonoidHom.mem_ker]
  apply Equiv.ext
  intro L
  exact hp L

theorem elementary_preprimitive_of_hypPairs (hQ : Q.polarBilin.Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) : MulAction.IsPreprimitive (elementaryGroup Q) (Points Q) := by
  let := isPreprimitive_singularLines h₁₂ h₁₃ h₂₃ hQ
  exact MulAction.IsPreprimitive.of_surjective
    (f := (⟨nativePointEquiv Q, nativePointEquiv_smul Q⟩ :
      singularLines Q →ₑ[(id : elementaryGroup Q → elementaryGroup Q)] Points Q))
    (nativePointEquiv Q).surjective

theorem projective_preprimitive_of_hypPairs (hQ : Q.polarBilin.Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) : MulAction.IsPreprimitive (ProjectiveGroup Q) (Points Q) := by
  let := elementary_preprimitive_of_hypPairs Q hQ h₁₂ h₁₃ h₂₃
  exact MulAction.IsPreprimitive.of_surjective
    (f := (⟨id, quotient_smul Q⟩ : Points Q →ₑ[QuotientGroup.mk' (scalarKernel Q)] Points Q))
    Function.surjective_id

theorem points_nontrivial_of_hypPair (P : HypPair Q) : Nontrivial (Points Q) := by
  refine ⟨⟨pointMk P.e P.e_ne_zero P.Q_e, pointMk P.f P.f_ne_zero P.Q_f, ?_⟩⟩
  intro h
  obtain ⟨a, ha⟩ := (pointMk_eq_iff P.e_ne_zero P.f_ne_zero P.Q_e P.Q_f).mp h
  have hpol := congrArg (fun z => polar Q z P.f) ha
  rw [polar_smul_left_eq, P.polar_ff, P.polar_ef, mul_zero] at hpol
  exact zero_ne_one hpol

theorem projective_nontrivial_of_hypPairs (hQ : Q.polarBilin.Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) : Nontrivial (ProjectiveGroup Q) := by
  let := isSimpleGroup_projElementary_of_hypPairs hQ h₁₂ h₁₃ h₂₃
  change Nontrivial (ProjElementary Q)
  infer_instance

theorem elementary_projective_action [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Nonempty (Points Q) ∧ Nontrivial (Points Q) ∧ Nontrivial (ProjectiveGroup Q) ∧
      FaithfulSMul (ProjectiveGroup Q) (Points Q) ∧
      MulAction.IsPreprimitive (ProjectiveGroup Q) (Points Q) ∧
      MulAction.IsPreprimitive (elementaryGroup Q) (Points Q) ∧
      (elementaryPointAction Q).ker = scalarKernel Q := by
  obtain ⟨T, hT3, hTs⟩ := hT
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ (by omega) hTs
  exact ⟨⟨pointMk P₁.e P₁.e_ne_zero P₁.Q_e⟩, points_nontrivial_of_hypPair Q P₁,
    projective_nontrivial_of_hypPairs Q hQ h₁₂ h₁₃ h₂₃,
    projective_faithful_of_hypPairs Q h₁₂,
    projective_preprimitive_of_hypPairs Q hQ h₁₂ h₁₃ h₂₃,
    elementary_preprimitive_of_hypPairs Q hQ h₁₂ h₁₃ h₂₃,
    actionKernel_eq_of_hypPairs Q h₁₂⟩

@[expose] noncomputable def elementaryStabilizer (L : Points Q) : Subgroup (elementaryGroup Q) :=
  MulAction.stabilizer (elementaryGroup Q) L

@[expose] noncomputable def projectiveStabilizer (L : Points Q) : Subgroup (ProjectiveGroup Q) :=
  MulAction.stabilizer (ProjectiveGroup Q) L

@[expose] noncomputable def stabilizerFamily : Set (Subgroup (ProjectiveGroup Q)) :=
  Set.range (projectiveStabilizer Q)

theorem projectiveStabilizer_comap (L : Points Q) :
    (projectiveStabilizer Q L).comap (QuotientGroup.mk' (scalarKernel Q)) =
      elementaryStabilizer Q L := rfl

theorem projectiveStabilizer_map (L : Points Q) :
    (elementaryStabilizer Q L).map (QuotientGroup.mk' (scalarKernel Q)) =
      projectiveStabilizer Q L := by
  rw [← projectiveStabilizer_comap]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

end CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
