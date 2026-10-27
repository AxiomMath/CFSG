module

public import CFSG.LieType.Chevalley.C2E6A5CubeTwist

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.ExteriorCube exteriorPower Set Matrix
  CFSG.LocalAnalysis.ComponentInitial

theorem mem_scalars_iff (z : SpecialLinearGroup (Fin 6) K) :
    z ∈ LinearFlag.scalars 6 K ↔
      ∃ l : Kˣ, (z : Matrix (Fin 6) (Fin 6) K) = scalar (Fin 6) (l : K) := by
  rw [LinearFlag.mem_scalars]
  constructor
  · rintro ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, units_pow_three, one_pow], hc⟩

@[expose] def projEquivCube : LinearFlag.projectiveSL 6 K ≃* (cubeHom (K := K)).range :=
  (QuotientGroup.quotientMulEquivOfEq ker_cubeHom.symm).trans
    (QuotientGroup.quotientKerEquivRange cubeHom)

theorem projEquivCube_proj (h : SpecialLinearGroup (Fin 6) K) :
    (projEquivCube (LinearFlag.proj 6 K h) : (Module.End K (⋀[K]^3 (Fin 6 → K)))ˣ) =
      cubeHom h := rfl

theorem A5_exterior_cube_faithful_projective_linear_model :
    (∀ (g : groupA) (v : RootModule Tag.E6 K) (hv : v ∈ moduleA),
      (psiA g : Module.End K (⋀[K]^3 (Fin 6 → K))) (phiA ⟨v, hv⟩) =
        phiA ⟨((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v,
          mem_moduleA_of_mem_groupA g.2 v hv⟩) ∧
    Function.Injective psiA ∧ psiA.range = (cubeHom (K := K)).range ∧
    (∃ e : groupA ≃* (cubeHom (K := K)).range, ∀ g,
      (e g : (Module.End K (⋀[K]^3 (Fin 6 → K)))ˣ) = psiA g) ∧
    (cubeHom (K := K)).ker = LinearFlag.scalars 6 K ∧
    (∀ z : SpecialLinearGroup (Fin 6) K, z ∈ LinearFlag.scalars 6 K ↔
      ∃ l : Kˣ, (z : Matrix (Fin 6) (Fin 6) K) = scalar (Fin 6) (l : K)) ∧
    (∃ e : LinearFlag.projectiveSL 6 K ≃* (cubeHom (K := K)).range, ∀ h,
      (e (LinearFlag.proj 6 K h) : (Module.End K (⋀[K]^3 (Fin 6 → K)))ˣ) = cubeHom h) ∧
    (∀ i j : Fin 6, J6 i j = if j = Fin.rev i then 1 else 0) ∧
    (∀ g : groupA, diagE6GL * (g : ModGL Tag.E6 K) * diagE6GL⁻¹ ∈ groupA) ∧
    (∀ (g : groupA) (h : SpecialLinearGroup (Fin 6) K), psiA g = cubeHom h →
      ((conjA g : groupA) : ModGL Tag.E6 K) = diagE6GL * g * diagE6GL⁻¹ ∧
        psiA (conjA g) = cubeHom (thetaSL h)) ∧
    (∀ h : SpecialLinearGroup (Fin 6) K, (thetaSL h : Matrix (Fin 6) (Fin 6) K) =
      J6 * ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ * J6) ∧
    (∀ (g : groupA) (h : SpecialLinearGroup (Fin 6) K), psiA g = cubeHom h →
      ((betaA g : groupA) : ModGL Tag.E6 K) = betaGL g ∧ psiA (betaA g) = cubeHom (barSL h)) ∧
    (∀ h : SpecialLinearGroup (Fin 6) K,
      (barSL h : Matrix (Fin 6) (Fin 6) K) = (h : Matrix (Fin 6) (Fin 6) K).map bar) ∧
    (∀ (g : groupA) (h : SpecialLinearGroup (Fin 6) K), psiA g = cubeHom h →
      ((g : ModGL Tag.E6 K) ∈ stdFixedGroup ↔ h ∈ SU6)) ∧
    (∀ h : SpecialLinearGroup (Fin 6) K, h ∈ SU6 ↔
      ((h : Matrix (Fin 6) (Fin 6) K).map bar)ᵀ * J6 * (h : Matrix (Fin 6) (Fin 6) K) = J6) ∧
    LinearFlag.scalars 6 K ≤ SU6 ∧
    (stdFixedGroup.subgroupOf groupA).map psiA = SU6.map (cubeHom (K := K)) ∧
    (unipotentA.subgroupOf groupA).map psiA =
      (LinearFlag.unitriangular 6 K).map (cubeHom (K := K)) ∧
    (torusA.subgroupOf groupA).map psiA = diagSL.map (cubeHom (K := K)) ∧
    (∀ g : SpecialLinearGroup (Fin 6) K,
      g ∈ diagSL ↔ ∃ d : Fin 6 → K, (g : Matrix (Fin 6) (Fin 6) K) = diagonal d) ∧
    LinearFlag.scalars 6 K ≤ diagSL :=
  ⟨fun g v hv => by rw [psiA_apply, LinearEquiv.symm_apply_apply]; rfl,
    psiA_injective, range_psiA, ⟨psiAEquiv, coe_psiAEquiv⟩, ker_cubeHom, mem_scalars_iff,
    ⟨projEquivCube, projEquivCube_proj⟩, fun _ _ => rfl, fun g => conj_mem_groupA g.2,
    fun _ _ hgh => ⟨rfl, psiA_conjA hgh⟩, coe_thetaSL, fun _ _ hgh => ⟨rfl, psiA_betaA hgh⟩,
    coe_barSL, fun _ _ hgh => mem_stdFixedGroup_iff hgh, mem_SU6_iff, scalars_le_SU6,
    map_psiA_stdFixedGroup, map_psiA_unipotentA, map_psiA_torusA, fun _ => mem_diagSL,
    scalars_le_diagSL⟩

end CFSG.LieType.Chevalley.C2E6Std
