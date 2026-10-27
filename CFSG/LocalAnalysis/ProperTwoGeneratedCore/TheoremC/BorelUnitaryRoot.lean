module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelFacts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryKernel

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] (J : HermitianForm 3 K) {f : ℕ}

theorem inCenterOf_unitaryCoverRoot_iff (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {w : ProjectiveSpecialUnitaryMatrixGroup J} :
    InCenterOf (unitaryCoverRoot J hJ) w ↔
      ∃ z : hermitianUnipotentCoord J, z.1.1 = 0 ∧ hermitianUnipotentPSU J hJ z = w := by
  constructor
  · rintro ⟨⟨z, rfl⟩, hw⟩
    refine ⟨z, ?_, rfl⟩
    have hz : z ∈ Subgroup.center (hermitianUnipotentCoord J) := by
      rw [Subgroup.mem_center_iff]
      intro v
      apply CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
      rw [map_mul, map_mul]
      exact hw _ ⟨v, rfl⟩
    rw [center_eq_ker_firstCoord J (2 ^ f) hcard hfixed] at hz
    exact hz
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, rfl⟩, ?_⟩
    rintro _ ⟨v, rfl⟩
    change _ * _ = _ * _
    rw [← map_mul, ← map_mul, mul_comm_of_fst_eq_zero J hz v]

theorem unitaryCoverRoot_commutator_central (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∀ a ∈ unitaryCoverRoot J hJ, ∀ b ∈ unitaryCoverRoot J hJ,
      InCenterOf (unitaryCoverRoot J hJ) (a * b * a⁻¹ * b⁻¹) := by
  rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
  refine (inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ).2
    ⟨⁅z, w⁆, fst_commutator J z w, ?_⟩
  simp only [commutatorElement_def, map_mul, map_inv]

theorem unitaryCoverRoot_sq_central (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∀ a ∈ unitaryCoverRoot J hJ, InCenterOf (unitaryCoverRoot J hJ) (a * a) := by
  rintro _ ⟨z, rfl⟩
  refine (inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ).2 ⟨z * z, ?_, map_mul _ _ _⟩
  rw [fst_mul, CharTwo.add_self_eq_zero]

theorem card_inCenterOf_unitaryCoverRoot (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card {w // InCenterOf (unitaryCoverRoot J hJ) w} = 2 ^ f := by
  rw [← card_ker_firstCoord J hfixed]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun z => ⟨hermitianUnipotentPSU J hJ z.1,
      (inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ).2 ⟨z.1, z.2, rfl⟩⟩) ⟨?_, ?_⟩)
  · intro z w h
    exact Subtype.ext (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ (congrArg Subtype.val h))
  · rintro ⟨w, hw⟩
    obtain ⟨z, hz, rfl⟩ := (inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ).1 hw
    exact ⟨⟨z, hz⟩, rfl⟩

theorem unitaryCoverRoot_aut_inner (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (σ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hσ : ∀ x ∈ unitaryCoverRoot J hJ, σ x = x) :
    ∃ r ∈ unitaryCoverRoot J hJ, ∀ k, σ k = r * k * r⁻¹ := by
  have hσQ : (unitaryCoverRoot J hJ).map σ.toMonoidHom = unitaryCoverRoot J hJ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change σ y ∈ unitaryCoverRoot J hJ
      rw [hσ y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hσ x hx⟩
  obtain ⟨r, hr, hσr⟩ := RootCenter.unitary_rank_one_Sylow_layer_kernel_of_mulEquiv J f hf
    hcard hfixed hJ (MulEquiv.refl _) (unitaryCoverSylow J f hf hcard hfixed hJ) _ rfl σ hσQ
    (by rintro _ ⟨y, -, rfl⟩; exact hσ _ y.2)
    (fun x hx => by rw [hσ x hx, inv_mul_cancel]; exact one_mem _)
  exact ⟨r, hr, fun k => by rw [hσr, MulAut.conj_apply]⟩

end CFSG.ProperTwoGeneratedCore.TheoremC
