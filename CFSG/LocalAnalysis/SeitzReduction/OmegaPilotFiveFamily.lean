module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv statedProjectiveReindexEquiv_mk)
open scoped Pointwise

section Orbit

variable {A T : Type*} [Group A] [MulAction A T]

theorem smul_eq_or_conj_smul_eq_of_orbit_three {x y z : T}
    (hO : MulAction.orbit A x ⊆ {x, y, z}) (hyz : y ≠ z) {γ : A} (hγx : γ • x = x)
    (hγy : γ • y = z) (hγz : γ • z = y) (δ : A) :
    δ • x = x ∨ (δ * γ * δ⁻¹ * γ * δ) • x = x := by
  by_cases h : δ • x = x
  · exact Or.inl h
  right
  have hexp : (δ * γ * δ⁻¹ * γ * δ) • x = δ • γ • δ⁻¹ • γ • δ • x := by
    simp only [mul_smul]
  rw [hexp]
  have hxy : x ≠ y := by
    intro hxy
    apply hyz
    rw [← hγy, ← hxy, hγx, hxy]
  have hxz : x ≠ z := by
    intro hxz
    apply hyz
    rw [← hγz, ← hxz, hγx, hxz]
  have hmem : ∀ w ∈ MulAction.orbit A x, w = x ∨ w = y ∨ w = z := fun w hw => hO hw
  have hsmul : ∀ (a : A) (w : T), w ∈ MulAction.orbit A x → a • w ∈ MulAction.orbit A x := by
    rintro a w ⟨b, rfl⟩
    exact ⟨a * b, mul_smul a b x⟩
  have hxO : x ∈ MulAction.orbit A x := MulAction.mem_orbit_self x
  rcases hmem _ (hsmul δ x hxO) with h1 | h1 | h1
  · exact absurd h1 h
  ·
    have hyO : y ∈ MulAction.orbit A x := h1 ▸ hsmul δ x hxO
    have hzO : z ∈ MulAction.orbit A x := hγy ▸ hsmul γ y hyO
    rw [h1, hγy]
    rcases hmem _ (hsmul δ⁻¹ z hzO) with hu | hu | hu
    · exfalso
      apply hyz
      rw [← h1, ← hu, smul_inv_smul]
    · rw [hu, hγy]
      have hδy : δ • y = z := by rw [← hu, smul_inv_smul]
      rcases hmem _ (hsmul δ z hzO) with h2 | h2 | h2
      · exact h2
      · exact absurd (smul_left_cancel δ (h2.trans h1.symm)) hxz.symm
      · exact absurd (smul_left_cancel δ (h2.trans hδy.symm)) hyz.symm
    · rw [hu, hγz]
      have hδz : δ • z = z := by
        conv_lhs => rw [← hu]
        exact smul_inv_smul δ z
      rcases hmem _ (hsmul δ y hyO) with h2 | h2 | h2
      · exact h2
      · exact absurd (smul_left_cancel δ (h2.trans h1.symm)) hxy.symm
      · exact absurd (smul_left_cancel δ (h2.trans hδz.symm)) hyz
  ·
    have hzO : z ∈ MulAction.orbit A x := h1 ▸ hsmul δ x hxO
    have hyO : y ∈ MulAction.orbit A x := hγz ▸ hsmul γ z hzO
    rw [h1, hγz]
    rcases hmem _ (hsmul δ⁻¹ y hyO) with hu | hu | hu
    · exfalso
      apply hyz
      rw [← smul_inv_smul δ y, hu, h1]
    · rw [hu, hγy]
      have hδy : δ • y = y := by
        conv_lhs => rw [← hu]
        exact smul_inv_smul δ y
      rcases hmem _ (hsmul δ z hzO) with h2 | h2 | h2
      · exact h2
      · exact absurd (smul_left_cancel δ (h2.trans hδy.symm)) hyz.symm
      · exact absurd (smul_left_cancel δ (h2.trans h1.symm)) hxz.symm
    · rw [hu, hγz]
      have hδz : δ • z = y := by rw [← hu, smul_inv_smul]
      rcases hmem _ (hsmul δ y hyO) with h2 | h2 | h2
      · exact h2
      · exact absurd (smul_left_cancel δ (h2.trans hδz.symm)) hyz
      · exact absurd (smul_left_cancel δ (h2.trans h1.symm)) hxy.symm

end Orbit

section Flip

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def plusFlipAut (hn : 0 < n) :
    MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  MulAut.congr (plusCoordinateEquiv n K) (plusSwapAut n K hn)

theorem plusCoordinateEquiv_mk [CharP K 2] (hn : 1 ≤ n) (A : StatedOmega (StatedQuadPlus n K)) :
    plusCoordinateEquiv n K (QuotientGroup.mk' _ A) = statedOmegaPlusEquiv K n hn A := by
  exact statedProjectiveReindexEquiv_mk (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K) A

theorem plusFlipAut_statedOmegaPlusEquiv [CharP K 2] (hn : 1 ≤ n)
    (A : StatedOmega (StatedQuadPlus n K)) :
    plusFlipAut n K (by omega) (statedOmegaPlusEquiv K n hn A) =
      statedOmegaPlusEquiv K n hn (plusSwapDerived n K (by omega) A) := by
  rw [plusFlipAut, automorphismTransport_apply, ← plusCoordinateEquiv_mk n K hn,
    MulEquiv.symm_apply_apply, plusSwapAut_mk, plusCoordinateEquiv_mk n K hn]

theorem plusFlipAut_smul_pointFamily (hn : 0 < n) :
    plusFlipAut n K hn • projectivePointFamily (coordinateQuadPlus n K) =
      projectivePointFamily (coordinateQuadPlus n K) := by
  rw [plusFlipAut, ← plusCoordinate_pointFamily, ← familyTransport_automorphism,
    plusSwapAut_smul_statedPointFamily]

theorem plusCX_eq_familyTransport :
    plusCX n K = familyTransport (plusCoordinateEquiv n K) (conjugacyFamily
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (flag n K n))) :=
  (familyTransport_conjugacy (plusCoordinateEquiv n K) _).symm

theorem plusCXstar_eq_familyTransport (hn : 0 < n) :
    plusCXstar n K hn = familyTransport (plusCoordinateEquiv n K) (conjugacyFamily
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus n K) (Xstar n K hn))) :=
  (familyTransport_conjugacy (plusCoordinateEquiv n K) _).symm

theorem plusFlipAut_smul_plusCX (hn : 0 < n) :
    plusFlipAut n K hn • plusCX n K = plusCXstar n K hn := by
  rw [plusCX_eq_familyTransport, plusCXstar_eq_familyTransport n K hn, plusFlipAut,
    ← familyTransport_automorphism, plusSwapAut_smul_conjugacyFamily_flag]

theorem plusFlipAut_smul_plusCXstar (hn : 0 < n) :
    plusFlipAut n K hn • plusCXstar n K hn = plusCX n K := by
  rw [plusCX_eq_familyTransport, plusCXstar_eq_familyTransport n K hn, plusFlipAut,
    ← familyTransport_automorphism, plusSwapAut_smul_conjugacyFamily_Xstar]

theorem plusCX_ne_plusCXstar [Finite K] (hn : 3 ≤ n) :
    plusCX n K ≠ plusCXstar n K (by omega) := by
  rw [plusCX_eq_familyTransport, plusCXstar_eq_familyTransport n K (by omega)]
  exact fun h => conjugacyFamily_flag_ne_Xstar n K hn ((familyTransport _).injective h)

end Flip

section Image

variable {k : Type} [Field k] [Finite k]

theorem mem_image_iff_smul_pointFamily {n : ℕ} (hn : 4 ≤ n) [CharP k 2]
    (δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n k))) :
    δ ∈ matrixProjectiveImage (coordinateQuadPlus n k) ↔
      δ • projectivePointFamily (coordinateQuadPlus n k) =
        projectivePointFamily (coordinateQuadPlus n k) := by
  obtain ⟨f, hf, hk⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := k)
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n k)))
      .POmegaPlus n 2 f :=
    ⟨⟨Nat.prime_two, hf, hn⟩, k, inferInstance, inferInstance, hk, ⟨MulEquiv.refl _⟩⟩
  rw [← coordinate_plus_family_eq_matrixImage hmod k hk (MulEquiv.refl _)]
  exact Iff.rfl

theorem mem_image_or_conj_mem_image_four [CharP k 2]
    (δ γ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 k)))
    (hγF : γ • projectivePointFamily (coordinateQuadPlus 4 k) =
      projectivePointFamily (coordinateQuadPlus 4 k))
    (hγX : γ • plusCX 4 k = plusCXstar 4 k (by norm_num))
    (hγX' : γ • plusCXstar 4 k (by norm_num) = plusCX 4 k) :
    δ ∈ matrixProjectiveImage (coordinateQuadPlus 4 k) ∨
      δ * γ * δ⁻¹ * γ * δ ∈ matrixProjectiveImage (coordinateQuadPlus 4 k) := by
  rw [mem_image_iff_smul_pointFamily le_rfl, mem_image_iff_smul_pointFamily le_rfl]
  exact smul_eq_or_conj_smul_eq_of_orbit_three
    (coordinate_plus_pointFamily_orbit_subset (n := 4) (K := k) rfl)
    (plusCX_ne_plusCXstar 4 k (by norm_num)) hγF hγX hγX' δ

theorem plusFlipAut_mem_image {n : ℕ} (hn : 4 ≤ n) [CharP k 2] :
    plusFlipAut n k (by omega) ∈ matrixProjectiveImage (coordinateQuadPlus n k) :=
  (mem_image_iff_smul_pointFamily hn _).2 (plusFlipAut_smul_pointFamily n k _)

end Image

end CFSG.SeitzReduction.OmegaPilot
