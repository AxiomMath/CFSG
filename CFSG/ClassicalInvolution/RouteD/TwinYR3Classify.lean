module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthStd
public import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.GroupTheory.WeirSylow
open CFSG.ClassicalInvolution.RouteD.NonClassical (card_frame_of_isometry card_frame_plus
  card_frame_minus card_frame_odd)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

@[expose] def framesPlus (q j : ℕ) : ℕ :=
  ((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1)) * q ^ (2 * (j + 1)) *
    (((q ^ (j + 1) - 1) * (q ^ j + 1)) * q ^ (2 * j))

@[expose] def framesMinus (q j : ℕ) : ℕ :=
  ((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1)) * q ^ (2 * (j + 1 + 1)) *
    (((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)) * q ^ (2 * (j + 1)))

@[expose] def framesOdd (q j : ℕ) : ℕ :=
  (q ^ (2 * (j + 1 + 1)) - 1) * q ^ (2 * (j + 1) + 1) *
    ((q ^ (2 * (j + 1)) - 1) * q ^ (2 * j + 1))

section Smul

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {c : K}

theorem polar_smul_form (c : K) (x y : V) : polar (c • Q) x y = c * polar Q x y := by
  unfold polar
  simp only [smul_apply, smul_eq_mul]
  ring

@[expose] def hypPairSmul (hc : c ≠ 0) (P : HypPair Q) : HypPair (c • Q) where
  e := P.e
  f := c⁻¹ • P.f
  Q_e := by rw [smul_apply, P.Q_e, smul_zero]
  Q_f := by
    rw [smul_apply, QuadraticMap.map_smul, P.Q_f]
    simp
  polar_ef := by
    rw [polar_smul_form, polar_smul_right, P.polar_ef]
    simp [hc]

@[expose] def hypPairUnsmul (hc : c ≠ 0) (P : HypPair (c • Q)) : HypPair Q where
  e := P.e
  f := c • P.f
  Q_e := by
    have h := P.Q_e
    rw [smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  Q_f := by
    have h := P.Q_f
    rw [smul_apply, smul_eq_mul] at h
    have h' := (mul_eq_zero.mp h).resolve_left hc
    rw [QuadraticMap.map_smul, h', smul_zero]
  polar_ef := by
    have h := P.polar_ef
    rw [polar_smul_form] at h
    rw [polar_smul_right, smul_eq_mul]
    exact h

theorem orth_hypPairSmul (hc : c ≠ 0) {P P' : HypPair Q} (h : P.Orth P') :
    (hypPairSmul hc P).Orth (hypPairSmul hc P') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show polar (c • Q) P.e P'.e = 0
    rw [polar_smul_form, h.ee, mul_zero]
  · show polar (c • Q) P.e (c⁻¹ • P'.f) = 0
    rw [polar_smul_form, polar_smul_right, h.ef]
    simp
  · show polar (c • Q) (c⁻¹ • P.f) P'.e = 0
    rw [polar_smul_form, polar_smul_left, h.fe]
    simp
  · show polar (c • Q) (c⁻¹ • P.f) (c⁻¹ • P'.f) = 0
    rw [polar_smul_form, polar_smul_left, polar_smul_right, h.ff]
    simp

theorem orth_hypPairUnsmul (hc : c ≠ 0) {P P' : HypPair (c • Q)} (h : P.Orth P') :
    (hypPairUnsmul hc P).Orth (hypPairUnsmul hc P') := by
  have key : ∀ x y : V, polar (c • Q) x y = 0 → polar Q x y = 0 := fun x y hxy => by
    rw [polar_smul_form] at hxy
    exact (mul_eq_zero.mp hxy).resolve_left hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact key _ _ h.ee
  · show polar Q P.e (c • P'.f) = 0
    rw [polar_smul_right, key _ _ h.ef, smul_zero]
  · show polar Q (c • P.f) P'.e = 0
    rw [polar_smul_left, key _ _ h.fe, smul_zero]
  · show polar Q (c • P.f) (c • P'.f) = 0
    rw [polar_smul_left, polar_smul_right, key _ _ h.ff]
    simp

theorem card_frame_smul (hc : c ≠ 0) : Nat.card (OFrame (c • Q)) = Nat.card (OFrame Q) :=
  Nat.card_congr
    { toFun := fun F => ⟨hypPairUnsmul hc F.P, hypPairUnsmul hc F.P', orth_hypPairUnsmul hc F.orth⟩
      invFun := fun F => ⟨hypPairSmul hc F.P, hypPairSmul hc F.P', orth_hypPairSmul hc F.orth⟩
      left_inv := fun F => CFSG.ClassicalInvolution.ModelFacts.Frame.ext_vec rfl
        (inv_smul_smul₀ hc _) rfl (inv_smul_smul₀ hc _)
      right_inv := fun F => CFSG.ClassicalInvolution.ModelFacts.Frame.ext_vec rfl
        (smul_inv_smul₀ hc _) rfl (smul_inv_smul₀ hc _) }

end Smul

section Classify

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem card_frame_eq_zero_of_finrank_lt (h : Module.finrank K V < 4) :
    Nat.card (OFrame Q) = 0 := by
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun F => ?_⟩
  have h1 := Submodule.finrank_le F.span
  rw [Frame.finrank_span] at h1
  omega

theorem ringChar_ne_two_of_two_ne_zero (h2 : (2 : K) ≠ 0) : ringChar K ≠ 2 := fun h => by
  have := ringChar.Nat.cast_ringChar (R := K)
  rw [h] at this
  exact h2 (by exact_mod_cast this)

theorem card_frame_regular_plus (hQ : (polarBilin Q).Nondegenerate) {j : ℕ}
    (hdim : Module.finrank K V = 2 * (j + 2)) (h : IsPlusType Q) :
    Nat.card (OFrame Q) = framesPlus (Nat.card K) j := by
  obtain ⟨e⟩ := nonempty_isometry_quadPlus hQ (n := j + 1 + 1) (by omega) h
  rw [card_frame_of_isometry e]
  exact card_frame_plus K j

theorem card_frame_regular_minus (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    {j : ℕ} (hdim : Module.finrank K V = 2 * (j + 3)) (h : ¬ IsPlusType Q) :
    Nat.card (OFrame Q) = framesMinus (Nat.card K) j := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  rcases exists_isometry_quadPlus_or_quadMinus Q hQ (n := j + 1 + 1 + 1) (by omega)
    (by omega) with he | ⟨b, c, hirr, he⟩
  · obtain ⟨e⟩ := he
    exact absurd ((isPlusType_congr e).2 (isPlusType_quadPlus K _)) h
  · obtain ⟨e⟩ := he
    rw [card_frame_of_isometry e]
    exact card_frame_minus K h2 hirr j

theorem card_frame_regular_odd (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    {j : ℕ} (hdim : Module.finrank K V = 2 * (j + 2) + 1) :
    Nat.card (OFrame Q) = framesOdd (Nat.card K) j := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_smul_isometry_quadOdd (ringChar_ne_two_of_two_ne_zero h2) Q hQ
    (n := j + 1 + 1) (by omega)
  rw [← card_frame_smul hd, card_frame_of_isometry e]
  exact card_frame_odd K h2 j

end Classify

end CFSG.ClassicalInvolution.RouteD.TwinY
