module

public import CFSG.LieType.Chevalley.C2E6FourthResidueOrder
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FourthResidue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal Module
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev baseFlag : Fin 3 → Submodule (ZMod 2) V0 := stdFlag (ZMod 2) (Fin 2 → ZMod 2) 3

theorem baseFlag_apply (k : Fin 3) :
    baseFlag k = tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 (k + 1) :=
  rfl

theorem baseFlag_mem : baseFlag ∈ singularFlags Qminus 3 :=
  tailFlag_mem_singularFlags

theorem smul_mem_singularFlags (g : orthElementaryGroup Qminus) :
    g • baseFlag ∈ singularFlags Qminus 3 := by
  rw [← orbit_stdFlag qBin_anisotropic ⟨a₀, a₀_ne_zero⟩]
  exact MulAction.mem_orbit _ g

@[expose] def leviFlag
    (l : stdLevi fourthJ) : singularFlags Qminus 3 :=
  ⟨leviEquiv l • baseFlag, smul_mem_singularFlags _⟩

theorem leviFlag_apply
    (l : stdLevi fourthJ) (k : Fin 3) :
    (leviFlag l : Fin 3 → Submodule (ZMod 2) V0) k =
      (baseFlag k).map (rhoMinus l : V0 →ₗ[ZMod 2] V0) :=
  rfl

theorem leviFlag_mul
    (l l' : stdLevi fourthJ) :
    (leviFlag (l * l') : Fin 3 → Submodule (ZMod 2) V0) =
      leviEquiv l • (leviFlag l' : Fin 3 → Submodule (ZMod 2) V0) := by
  change leviEquiv (l * l') • baseFlag = leviEquiv l • leviEquiv l' • baseFlag
  rw [map_mul, mul_smul]

theorem leviFlag_one
    : (leviFlag 1 : Fin 3 → Submodule (ZMod 2) V0) = baseFlag := by
  change leviEquiv 1 • baseFlag = baseFlag
  rw [map_one, one_smul]

theorem mem_tailBorel_iff_smul
    (l : stdLevi fourthJ) :
    rhoMinus l ∈ tailBorel 3 qBin ↔ leviEquiv l • baseFlag = baseFlag := by
  rw [← MulAction.mem_stabilizer_iff, ← tailBorel_subgroupOf_eq, Subgroup.mem_subgroupOf]
  rfl

theorem leviFlag_eq_iff
    (l l' : stdLevi fourthJ) :
    leviFlag l = leviFlag l' ↔
      ((l⁻¹ * l' : stdLevi fourthJ) : ModGL Tag.E6 K) ∈ stdLeviBorel fourthJ := by
  rw [mem_stdLeviBorel_iff, mem_tailBorel_iff_smul, Subtype.ext_iff, map_mul, map_inv, mul_smul,
    inv_smul_eq_iff, eq_comm]
  rfl

@[expose] def leviCosetFlag
    : LeviCosets fourthJ → singularFlags Qminus 3 :=
  Quotient.lift leviFlag fun x y hxy => by
    have h : x⁻¹ * y ∈ (stdLeviBorel fourthJ).subgroupOf (stdLevi fourthJ) :=
      QuotientGroup.leftRel_apply.mp hxy
    exact (leviFlag_eq_iff x y).mpr h

theorem leviCosetFlag_mk
    (l : stdLevi fourthJ) :
    leviCosetFlag (QuotientGroup.mk l) = leviFlag l :=
  rfl

theorem leviCosetFlag_bijective
    : Function.Bijective leviCosetFlag := by
  constructor
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [leviCosetFlag_mk, leviCosetFlag_mk, leviFlag_eq_iff] at hxy
    exact QuotientGroup.eq.mpr hxy
  · rintro ⟨W, hW⟩
    rw [← orbit_stdFlag qBin_anisotropic ⟨a₀, a₀_ne_zero⟩] at hW
    obtain ⟨g, rfl⟩ := hW
    refine ⟨QuotientGroup.mk (leviEquiv.symm g), ?_⟩
    rw [leviCosetFlag_mk]
    apply Subtype.ext
    change leviEquiv (leviEquiv.symm g) • baseFlag = g • baseFlag
    rw [MulEquiv.apply_symm_apply]

@[expose] def residueFlag
    : ParabolicCosets fourthJ ≃ singularFlags Qminus 3 :=
  Equiv.ofBijective (leviCosetFlag ∘ residueMap two_mem_fourthJ)
    (leviCosetFlag_bijective.comp (residueMap_bijective two_mem_fourthJ))

theorem residueFlag_mk
    (p : nativeParabolic fourthJ) :
    residueFlag (QuotientGroup.mk p) = leviFlag (leviProj two_mem_fourthJ p) :=
  rfl

theorem residueFlag_one :
    (residueFlag (QuotientGroup.mk 1) : Fin 3 → Submodule (ZMod 2) V0) = baseFlag := by
  rw [residueFlag_mk, map_one, leviFlag_one]

theorem residueFlag_smul
    (p : nativeParabolic fourthJ) (x : ParabolicCosets fourthJ) :
    (residueFlag (p • x) : Fin 3 → Submodule (ZMod 2) V0) =
      leviEquiv (leviProj two_mem_fourthJ p) • (residueFlag x : Fin 3 → Submodule (ZMod 2) V0) := by
  induction x using QuotientGroup.induction_on with | H x => ?_
  rw [MulAction.Quotient.smul_mk, residueFlag_mk, residueFlag_mk, smul_eq_mul, map_mul,
    leviFlag_mul]

theorem residueFlag_smul_apply
    (p : nativeParabolic fourthJ) (x : ParabolicCosets fourthJ)
    (k : Fin 3) :
    (residueFlag (p • x) : Fin 3 → Submodule (ZMod 2) V0) k =
      ((residueFlag x : Fin 3 → Submodule (ZMod 2) V0) k).map
        (rhoMinus (leviProj two_mem_fourthJ p) : V0 →ₗ[ZMod 2] V0) := by
  rw [residueFlag_smul]
  rfl

theorem eq_one_of_mem_scalars {g : V0 ≃ₗ[ZMod 2] V0} (hg : g ∈ scalars (ZMod 2) V0) : g = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.mp hg
  have hc1 : c = 1 := by
    have hne : c ≠ 0 := by
      rintro rfl
      have h := hc (tVec 0)
      rw [zero_smul, LinearEquiv.map_eq_zero_iff] at h
      have h2 := congrArg (fun v : V0 => v.2 0) h
      simp at h2
    have key : ∀ d : ZMod 2, d ≠ 0 → d = 1 := by decide
    exact key c hne
  refine LinearEquiv.ext fun v => ?_
  rw [hc, hc1, one_smul]
  rfl

theorem eq_one_of_forall_smul_flag {g : V0 ≃ₗ[ZMod 2] V0}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Qminus)
    (hg : ∀ W ∈ singularFlags Qminus 3, ∀ k, (W k).map (g : V0 →ₗ[ZMod 2] V0) = W k) :
    g = 1 := by
  have hT2 : ∃ T : Submodule (ZMod 2) V0, finrank (ZMod 2) T = 2 ∧ ∀ x ∈ T, Qminus x = 0 :=
    ⟨tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 2, finrank_tailFlag (by norm_num),
      fun _ hx => quadTail_eq_zero_of_mem_tailFlag hx⟩
  refine eq_one_of_mem_scalars ((orthogonal_singular_line_scalar_kernel regular_Qminus.1
    hT2).1 g hgO |>.mp fun v hv hQv => ?_)
  have hF1 : tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 1 ∈ singularSubspaces Qminus 1 :=
    ⟨finrank_tailFlag (by norm_num), fun _ hx => quadTail_eq_zero_of_mem_tailFlag hx⟩
  have hv1 : Submodule.span (ZMod 2) {v} ∈ singularSubspaces Qminus 1 := by
    refine ⟨finrank_span_singleton hv, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul_eq_sq, hQv, mul_zero]
  obtain ⟨h, hh, hhv⟩ := (orthogonal_geometry_tail_singular_flag_transitivity qBin_anisotropic
    ⟨a₀, a₀_ne_zero⟩).2 1 (by norm_num) _ hF1 _ hv1
  have := hg _ (smul_mem_singularFlags ⟨h, hh⟩) 0
  change ((tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 1).map (h : V0 →ₗ[ZMod 2] V0)).map
      (g : V0 →ₗ[ZMod 2] V0) = (tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 1).map
        (h : V0 →ₗ[ZMod 2] V0) at this
  rwa [hhv] at this

theorem smul_eq_self_iff
    (p : nativeParabolic fourthJ) :
    (∀ x : ParabolicCosets fourthJ, p • x = x) ↔ (p : ModGL Tag.E6 K) ∈ stdRadical fourthJ := by
  rw [← leviProj_eq_one_iff two_mem_fourthJ]
  constructor
  · intro H
    apply rhoMinus_injective
    rw [map_one]
    refine eq_one_of_forall_smul_flag (rhoMinus_mem_orthogonalGroup _) fun W hW k => ?_
    obtain ⟨x, hx⟩ := residueFlag.surjective ⟨W, hW⟩
    have h := residueFlag_smul_apply p x k
    rw [H x, hx] at h
    exact h.symm
  · intro h1 x
    apply residueFlag.injective
    apply Subtype.ext
    rw [residueFlag_smul, h1, map_one, one_smul]

end CFSG.LieType.Chevalley.C2E6Std.FourthResidue
