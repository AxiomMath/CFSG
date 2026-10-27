module

public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwap

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O

open CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open scoped Pointwise

section Orbit

variable {A T : Type*} [Group A] [MulAction A T]

theorem conj_smul_eq_of_orbit_three_of_smul_eq {x y z : T}
    (hmem : ∀ w ∈ MulAction.orbit A x, w = x ∨ w = y ∨ w = z) (hyz : y ≠ z) {γ : A}
    (hγx : γ • x = x) (hγy : γ • y = z) {α : A} (hα : α * α = 1) (hαx : α • x = y)
    (hxy : x ≠ y) : ((γ * α)⁻¹ * α * (γ * α)) • x = x := by
  have hxz : x ≠ z := fun h => hxy (smul_left_cancel γ (by rw [hγx, hγy, h]))
  have hαy : α • y = x := by rw [← hαx, smul_smul, hα, one_smul]
  have hz : (γ * α) • x = z := by rw [mul_smul, hαx, hγy]
  have hαz : α • z = z := by
    have hO : (α * (γ * α)) • x ∈ MulAction.orbit A x := MulAction.mem_orbit x _
    rw [mul_smul, hz] at hO
    rcases hmem _ hO with h1 | h1 | h1
    · exact absurd (smul_left_cancel α (h1.trans hαy.symm)) hyz.symm
    · exact absurd (smul_left_cancel α (h1.trans hαx.symm)) hxz.symm
    · exact h1
  calc ((γ * α)⁻¹ * α * (γ * α)) • x = (γ * α)⁻¹ • α • (γ * α) • x := by simp only [mul_smul]
    _ = x := by rw [hz, hαz, ← hz, inv_smul_smul]

theorem exists_conj_smul_eq_of_orbit_three {x y z : T}
    (hO : MulAction.orbit A x ⊆ {x, y, z}) (hyz : y ≠ z) {γ : A} (hγx : γ • x = x)
    (hγy : γ • y = z) (hγz : γ • z = y) {α : A} (hα : α * α = 1) :
    ∃ β : A, (β * α * β⁻¹) • x = x := by
  by_cases h : α • x = x
  · exact ⟨1, by rwa [one_mul, inv_one, mul_one]⟩
  have hmem : ∀ w ∈ MulAction.orbit A x, w = x ∨ w = y ∨ w = z := fun w hw => hO hw
  refine ⟨(γ * α)⁻¹, ?_⟩
  rw [inv_inv]
  rcases hmem _ (MulAction.mem_orbit x α) with h1 | h1 | h1
  · exact absurd h1 h
  · exact conj_smul_eq_of_orbit_three_of_smul_eq hmem hyz hγx hγy hα h1
      (fun e => h (h1.trans e.symm))
  · exact conj_smul_eq_of_orbit_three_of_smul_eq (fun w hw => (hmem w hw).imp_right Or.symm)
      hyz.symm hγx hγz hα h1 (fun e => h (h1.trans e.symm))

end Orbit

section Swap

variable (K : Type) [Field K]

theorem d4_swap_smul_pointFamily :
    MulAut.congr (plusCoordinateEquiv 4 K) (plusSwapAut 4 K (by norm_num)) •
        projectivePointFamily (coordinateQuadPlus 4 K) =
      projectivePointFamily (coordinateQuadPlus 4 K) := by
  rw [← plusCoordinate_pointFamily, ← familyTransport_automorphism,
    plusSwapAut_smul_statedPointFamily]

theorem d4_swap_smul_plusCX :
    MulAut.congr (plusCoordinateEquiv 4 K) (plusSwapAut 4 K (by norm_num)) • plusCX 4 K =
      plusCXstar 4 K (by norm_num) := by
  rw [plusCX, plusCXstar, ← familyTransport_conjugacy, ← familyTransport_conjugacy,
    ← familyTransport_automorphism, plusSwapAut_smul_conjugacyFamily_flag]

theorem d4_swap_smul_plusCXstar :
    MulAut.congr (plusCoordinateEquiv 4 K) (plusSwapAut 4 K (by norm_num)) •
        plusCXstar 4 K (by norm_num) = plusCX 4 K := by
  rw [plusCX, plusCXstar, ← familyTransport_conjugacy, ← familyTransport_conjugacy,
    ← familyTransport_automorphism, plusSwapAut_smul_conjugacyFamily_Xstar]

theorem d4_plusCX_ne_plusCXstar [Finite K] : plusCX 4 K ≠ plusCXstar 4 K (by norm_num) := by
  rw [plusCX, plusCXstar, ← familyTransport_conjugacy, ← familyTransport_conjugacy]
  exact fun h => conjugacyFamily_flag_ne_Xstar 4 K (by norm_num) ((familyTransport _).injective h)

end Swap

section D4

variable (K : Type) [Field K] [Finite K]

theorem d4_exists_conj_mem_matrixProjectiveImage
    (α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) (hα : α * α = 1) :
    ∃ β, β * α * β⁻¹ ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_pow K
  have hp : (ringChar K).Prime := CharP.char_is_prime K _
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4
      (ringChar K) f := ⟨⟨hp, hf, by norm_num⟩, K, inferInstance, inferInstance, hK,
    ⟨MulEquiv.refl _⟩⟩
  rw [← coordinate_plus_family_eq_matrixImage hmod K hK (MulEquiv.refl _)]
  exact exists_conj_smul_eq_of_orbit_three
    (coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl) (d4_plusCX_ne_plusCXstar K)
    (d4_swap_smul_pointFamily K) (d4_swap_smul_plusCX K) (d4_swap_smul_plusCXstar K) hα

theorem d4_exists_conj_induced (α : MulAut (ProjOrthDerived (coordinateQuadPlus 4 K)))
    (hα : α * α = 1) : ∃ β, InducedBySemilinear (coordinateQuadPlus 4 K) (β * α * β⁻¹) := by
  set e := coordBridge (coordinateQuadPlus 4 K) (by norm_num : 0 < 2 * 4) with he
  obtain ⟨β', hβ'⟩ := d4_exists_conj_mem_matrixProjectiveImage K ((MulAut.congr e).symm α)
    (by rw [← map_mul, hα, map_one])
  refine ⟨MulAut.congr e β', ?_⟩
  have key : (MulAut.congr e).symm (MulAut.congr e β' * α * (MulAut.congr e β')⁻¹) =
      β' * (MulAut.congr e).symm α * β'⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  have hmem : MulAut.congr e.symm (MulAut.congr e β' * α * (MulAut.congr e β')⁻¹) ∈
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    have h1 : MulAut.congr e.symm (MulAut.congr e β' * α * (MulAut.congr e β')⁻¹) =
        (MulAut.congr e).symm (MulAut.congr e β' * α * (MulAut.congr e β')⁻¹) := rfl
    rw [h1, key]
    exact hβ'
  obtain ⟨σ, F, hF, μ, hμ, hQ, hind⟩ :=
    exists_semilin_of_mem_matrixProjectiveImage (coordinateQuadPlus 4 K) (by norm_num) _ hmem
  exact ⟨σ, F, hF, μ, hμ, hQ, hind⟩

end D4

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O
