module

public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Elements

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis


variable {K : Type} [Field K] [Finite K] (σe : K ≃+* K)

theorem nf_xC (g : ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom))
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σe.toRingHom a)ˣ)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σe.toRingHom a) :
    (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σe.toRingHom u * fieldActor (t := TwistTag.E6) σe σe)
        (xC TwistTag.E6 K σe.toRingHom a c) =
      g * xC TwistTag.E6 K σe.toRingHom a
        ((u a : orbitField TwistTag.E6 K σe.toRingHom a) *
          orbitFieldRestrict TwistTag.E6 σe σe a c) * g⁻¹ := by
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have h1 : fieldActor (t := TwistTag.E6) σe σe (xC TwistTag.E6 K σe.toRingHom a c) =
      xC TwistTag.E6 K σe.toRingHom a (orbitFieldRestrict TwistTag.E6 σe σe a c) :=
    fieldActor_fixedOrbitX σe σe a c
  rw [h1]
  have h2 := compatDiagAutHom_fixedOrbitX (t := TwistTag.E6) (σ := σe.toRingHom) u a
    (orbitFieldRestrict TwistTag.E6 σe σe a c)
  have h3 : compatDiagAutHom TwistTag.E6 K σe.toRingHom u
      (xC TwistTag.E6 K σe.toRingHom a (orbitFieldRestrict TwistTag.E6 σe σe a c)) =
      xC TwistTag.E6 K σe.toRingHom a ((u a : orbitField TwistTag.E6 K σe.toRingHom a) *
        orbitFieldRestrict TwistTag.E6 σe σe a c) := h2
  rw [h3, MulAut.conj_apply]

theorem nf_yC (g : ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom))
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σe.toRingHom a)ˣ)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σe.toRingHom a) :
    (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σe.toRingHom u * fieldActor (t := TwistTag.E6) σe σe)
        (yC TwistTag.E6 K σe.toRingHom a c) =
      g * yC TwistTag.E6 K σe.toRingHom a
        (((u a)⁻¹ : (orbitField TwistTag.E6 K σe.toRingHom a)ˣ) *
          orbitFieldRestrict TwistTag.E6 σe σe a c) * g⁻¹ := by
  rw [MulAut.mul_apply, MulAut.mul_apply]
  have h1 : fieldActor (t := TwistTag.E6) σe σe (yC TwistTag.E6 K σe.toRingHom a c) =
      yC TwistTag.E6 K σe.toRingHom a (orbitFieldRestrict TwistTag.E6 σe σe a c) :=
    fieldActor_fixedOrbitY σe σe a c
  rw [h1]
  have h2 := compatDiagAutHom_fixedOrbitY (t := TwistTag.E6) (σ := σe.toRingHom) u a
    (orbitFieldRestrict TwistTag.E6 σe σe a c)
  have h3 : compatDiagAutHom TwistTag.E6 K σe.toRingHom u
      (yC TwistTag.E6 K σe.toRingHom a (orbitFieldRestrict TwistTag.E6 σe σe a c)) =
      yC TwistTag.E6 K σe.toRingHom a
        (((u a)⁻¹ : (orbitField TwistTag.E6 K σe.toRingHom a)ˣ) *
          orbitFieldRestrict TwistTag.E6 σe σe a c) := h2
  rw [h3, MulAut.conj_apply]

theorem nf_mem_U (g : ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom))
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σe.toRingHom a)ˣ)
    {x : ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom)}
    (hx : x ∈ (graphFixedPosUnipotent TwistTag.E6 K σe.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σe.toRingHom)) :
    ∃ x' ∈ (graphFixedPosUnipotent TwistTag.E6 K σe.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σe.toRingHom),
      (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σe.toRingHom u *
        fieldActor (t := TwistTag.E6) σe σe) x = g * x' * g⁻¹ := by
  rw [Subgroup.mem_subgroupOf] at hx
  have h1 : ((fieldActor (t := TwistTag.E6) σe σe x :
      ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom)) : ModGL TwistTag.E6.tag K) ∈
      graphFixedPosUnipotent TwistTag.E6 K σe.toRingHom := by
    rw [coe_fieldActor]
    have := map_units_map_entrywiseHom_graphFixedPosUnipotent (t := TwistTag.E6)
      (σ := σe.toRingHom) (δ := σe) (fun c => rfl)
    rw [← this]
    exact ⟨_, hx, rfl⟩
  have h2 : ((compatDiagAutHom TwistTag.E6 K σe.toRingHom u
      (fieldActor (t := TwistTag.E6) σe σe x) : ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom)) :
      ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σe.toRingHom := by
    rw [coe_compatDiagAutHom]
    have := map_conj_rootDiagUnit_graphFixedPosUnipotent (t := TwistTag.E6) (σ := σe.toRingHom)
      (b := compatDiag TwistTag.E6 σe.toRingHom u) (fun i => compatDiag_perm u i)
    rw [← this]
    exact ⟨_, h1, by simp [MulAut.conj_apply]⟩
  refine ⟨compatDiagAutHom TwistTag.E6 K σe.toRingHom u (fieldActor (t := TwistTag.E6) σe σe x),
    h2, ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply]

theorem nf_exists_U (g : ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom))
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σe.toRingHom a)ˣ)
    {v : ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom)}
    (hv : v ∈ (graphFixedPosUnipotent TwistTag.E6 K σe.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σe.toRingHom)) :
    ∃ x ∈ (graphFixedPosUnipotent TwistTag.E6 K σe.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σe.toRingHom),
      (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σe.toRingHom u *
        fieldActor (t := TwistTag.E6) σe σe) x = g * v * g⁻¹ := by
  classical
  set U0 := (graphFixedPosUnipotent TwistTag.E6 K σe.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σe.toRingHom) with hU0
  set α := MulAut.conj g * compatDiagAutHom TwistTag.E6 K σe.toRingHom u *
        fieldActor (t := TwistTag.E6) σe σe with hα
  have : Finite ↥U0 := inferInstance
  let T : ↥U0 → ↥U0 := fun x => ⟨(nf_mem_U σe g u x.2).choose, (nf_mem_U σe g u x.2).choose_spec.1⟩
  have hT : ∀ x : ↥U0, α x = g * (T x : _) * g⁻¹ := fun x =>
    (nf_mem_U σe g u x.2).choose_spec.2
  have hinj : Function.Injective T := by
    intro x y hxy
    apply Subtype.ext
    apply α.injective
    rw [hT x, hT y, hxy]
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨v, hv⟩
  refine ⟨x, x.2, ?_⟩
  rw [hT x, hx]

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
