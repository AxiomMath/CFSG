module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelUnitaryRoot

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

variable {K : Type} [Field K] [Finite K] [CharP K 2] (J : HermitianForm 3 K) {f : ℕ}

omit [CharP K 2] in
theorem unitaryCoverRoot_sup_torus_eq_normalizer (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    unitaryCoverRoot J hJ ⊔ unitaryCoverTorus J hJ =
      Subgroup.normalizer
        (unitaryCoverRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  obtain ⟨-, -, -, -, -, -, -, hN, -⟩ :=
    TwoCoreGrowth.unitary_entire_root_point_structure J f hf hcard hfixed hJ
  rw [unitaryCoverRoot, hN, unitaryCoverTorus, ← UnitaryModel.range_torusPSU]
  exact UnitaryModel.root_sup_torus J f hf hcard hfixed hJ

theorem unitaryCoverTorus_transitive_center (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {w w' : ProjectiveSpecialUnitaryMatrixGroup J}
    (hw : InCenterOf (unitaryCoverRoot J hJ) w) (hw1 : w ≠ 1)
    (hw' : InCenterOf (unitaryCoverRoot J hJ) w') (hw'1 : w' ≠ 1) :
    ∃ d ∈ unitaryCoverTorus J hJ, d⁻¹ * w * d = w' := by
  obtain ⟨z, hz, rfl⟩ := (inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ).1 hw
  obtain ⟨z', hz', rfl⟩ := (inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ).1 hw'
  have hb : z.1.2 ≠ 0 := fun h => hw1 (by rw [show z = 1 from coord_ext hz h, map_one])
  have hb' : z'.1.2 ≠ 0 := fun h => hw'1 (by rw [show z' = 1 from coord_ext hz' h, map_one])
  have hc : J.conj (z'.1.2 / z.1.2) = z'.1.2 / z.1.2 := by
    rw [map_div₀, conj_snd_of_fst_eq_zero J hz, conj_snd_of_fst_eq_zero J hz']
  obtain ⟨k, hk0, hk⟩ :=
    huppert_II_10_4_norm_surjective J (2 ^ f) hcard hfixed _ hc (div_ne_zero hb' hb)
  have hact : hermitianTorusAction J (Units.mk0 k hk0) z' = z := by
    apply coord_ext
    · rw [hermitianTorusAction_fst, hz', hz, zero_mul, zero_mul]
    · rw [hermitianTorusAction_snd, Units.val_mk0, mul_assoc, ← mul_inv, mul_comm (J.conj k) k,
        hk, ← div_eq_mul_inv, div_div_cancel₀ hb']
  refine ⟨hermitianTorusPSU J hJ (Units.mk0 k hk0), ⟨_, rfl⟩, ?_⟩
  rw [← hact, ← unitaryCoverTorus_conj_root]
  group

omit [Finite K] [CharP K 2] in
theorem hermitianTorusAction_fst_eq_scalar (k : Kˣ) (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z).1.1 = (unitaryCoverScalar J k : K) * z.1.1 := by
  rw [hermitianTorusAction_fst, unitaryCoverScalar_val]
  ring

theorem unitaryCoverRoot_forms_eq_zero (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (β : ProjectiveSpecialUnitaryMatrixGroup J → ProjectiveSpecialUnitaryMatrixGroup J → ZMod 2)
    (hβ₁ : ∀ a ∈ unitaryCoverRoot J hJ, ∀ b ∈ unitaryCoverRoot J hJ,
      ∀ c ∈ unitaryCoverRoot J hJ, β (a * b) c = β a c + β b c)
    (hβ₂ : ∀ a ∈ unitaryCoverRoot J hJ, ∀ b ∈ unitaryCoverRoot J hJ,
      ∀ c ∈ unitaryCoverRoot J hJ, β a (b * c) = β a b + β a c)
    (hβ₃ : ∀ a ∈ unitaryCoverRoot J hJ, β a a = 0)
    (hβ₄ : ∀ a ∈ unitaryCoverRoot J hJ, ∀ b, InCenterOf (unitaryCoverRoot J hJ) b → β a b = 0)
    (hβ₅ : ∀ d ∈ unitaryCoverTorus J hJ, ∀ a ∈ unitaryCoverRoot J hJ,
      ∀ b ∈ unitaryCoverRoot J hJ, β (d⁻¹ * a * d) (d⁻¹ * b * d) = β a b) :
    ∀ a ∈ unitaryCoverRoot J hJ, ∀ b ∈ unitaryCoverRoot J hJ, β a b = 0 := by
  set Q := unitaryCoverRoot J hJ
  set ψ := hermitianUnipotentPSU J hJ
  have hQ (z : hermitianUnipotentCoord J) : ψ z ∈ Q := ⟨z, rfl⟩
  have hsymm : ∀ a ∈ Q, ∀ b ∈ Q, β a b = β b a := by
    intro a ha b hb
    have h := hβ₃ (a * b) (Q.mul_mem ha hb)
    rw [hβ₁ a ha b hb _ (Q.mul_mem ha hb), hβ₂ a ha a ha b hb, hβ₂ b hb a ha b hb, hβ₃ a ha,
      hβ₃ b hb, zero_add, add_zero] at h
    exact CharTwo.add_eq_zero.1 h
  have hcentral (z w : hermitianUnipotentCoord J) (h : z.1.1 = w.1.1) :
      ∃ c, InCenterOf Q (ψ c) ∧ ψ z = ψ w * ψ c := by
    refine ⟨w⁻¹ * z, (inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ).2
      ⟨_, by rw [fst_mul, fst_inv, h, neg_add_cancel], rfl⟩, ?_⟩
    rw [← map_mul, mul_inv_cancel_left]
  have hleft (z w : hermitianUnipotentCoord J) (h : z.1.1 = w.1.1) (a : _) (ha : a ∈ Q) :
      β (ψ z) a = β (ψ w) a := by
    obtain ⟨c, hc, hzc⟩ := hcentral z w h
    rw [hzc, hβ₁ _ (hQ w) _ (hQ c) _ ha, hsymm _ (hQ c) _ ha, hβ₄ _ ha _ hc, add_zero]
  have hright (z w : hermitianUnipotentCoord J) (h : z.1.1 = w.1.1) (a : _) (ha : a ∈ Q) :
      β a (ψ z) = β a (ψ w) := by
    obtain ⟨c, hc, hzc⟩ := hcentral z w h
    rw [hzc, hβ₂ _ ha _ (hQ w) _ (hQ c), hβ₄ _ ha _ hc, add_zero]
  choose s hs using exists_fst_eq J (2 ^ f) hcard hfixed
  let B : K → K → ZMod 2 := fun x y => β (ψ (s x)) (ψ (s y))
  have hB (z w : hermitianUnipotentCoord J) : β (ψ z) (ψ w) = B z.1.1 w.1.1 := by
    rw [hleft z (s z.1.1) (hs _).symm _ (hQ w), hright w (s w.1.1) (hs _).symm _ (hQ _)]
  have hB₁ (x x' y : K) : B (x + x') y = B x y + B x' y := by
    have h := hB (s x * s x') (s y)
    rw [fst_mul, hs, hs, hs] at h
    rw [← h, map_mul, hβ₁ _ (hQ _) _ (hQ _) _ (hQ _)]
  have hB₂ (x y y' : K) : B x (y + y') = B x y + B x y' := by
    have h := hB (s x) (s y * s y')
    rw [fst_mul, hs, hs, hs] at h
    rw [← h, map_mul, hβ₂ _ (hQ _) _ (hQ _) _ (hQ _)]
  have hBinv (h : unitaryCoverScalarImage J) (x y : K) :
      B (((h : Kˣ) : K) * x) (((h : Kˣ) : K) * y) = B x y := by
    obtain ⟨k, hk⟩ := h.2
    have h₁ := hβ₅ (hermitianTorusPSU J hJ k)⁻¹ (inv_mem ⟨k, rfl⟩) (ψ (s x)) (hQ _) (ψ (s y))
      (hQ _)
    rw [inv_inv, unitaryCoverTorus_conj_root, unitaryCoverTorus_conj_root, hB, hB,
      hermitianTorusAction_fst_eq_scalar, hermitianTorusAction_fst_eq_scalar, hs, hs, hk] at h₁
    exact h₁
  have hzero := binaryUnitaryTorusInvariantBiadditive_eq_zero f hf hcard
    (unitaryCoverScalarImage J) (unitaryCoverScalarImage_card J (2 ^ f) hcard hfixed hJ) B hB₁
    hB₂ hBinv
  rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
  rw [hB]
  exact hzero _ _

end CFSG.ProperTwoGeneratedCore.TheoremC
