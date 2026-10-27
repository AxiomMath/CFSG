module

import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF2
public import CFSG.LieType.SeitzGeneration.ExcWideThree.G2
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityModel
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19
open scoped MatrixGroups

section Model


theorem triOdd_diagramMap_comm_thetaHom (L : Type) [Field L] (Y : Matrix.SpecialLinearGroup (Fin 2) L) :
    diagramMap TwistTag.D4 L * KS11Lie6Proof.thetaHom L Y =
      KS11Lie6Proof.thetaHom L Y * diagramMap TwistTag.D4 L := by
  have hfix : twistHom TwistTag.D4 L (RingHom.id L) (KS11Lie6Proof.thetaConj L) =
      KS11Lie6Proof.thetaConj L :=
    KS11Lie6Proof.twistHom_thetaConj (K := L) (RingEquiv.refl L) (RingHom.id L)
      (RingHom.ext fun _ => rfl)
  have h := KS11Lie6Proof.twistHom_thetaHom (RingHom.id L) hfix Y
  have hmap : Matrix.SpecialLinearGroup.map (RingHom.id L) Y = Y := by
    ext i j
    rfl
  have hid : Units.map (entrywiseHom (RingHom.id L)) (KS11Lie6Proof.thetaHom L Y) =
      KS11Lie6Proof.thetaHom L Y :=
    Units.ext (entrywise_id _)
  rw [hmap, CFSG.LieType.Chevalley.twistHom_apply, hid] at h
  calc diagramMap TwistTag.D4 L * KS11Lie6Proof.thetaHom L Y =
      diagramMap TwistTag.D4 L * KS11Lie6Proof.thetaHom L Y * (diagramMap TwistTag.D4 L)⁻¹ *
        diagramMap TwistTag.D4 L := by group
    _ = KS11Lie6Proof.thetaHom L Y * diagramMap TwistTag.D4 L := by rw [h]

variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem triOdd_charP_closure {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hX : Nat.card X = (ℓ ^ f) ^ 3) :
    CharP (AlgebraicClosure X) ℓ :=
  haveI : CharP X ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := f * 3) (by omega) (by rw [hX, pow_mul])
  charP_of_injective_algebraMap (algebraMap X (AlgebraicClosure X)).injective ℓ

theorem triOdd_exists_thetaHom_of_mem_bsub {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) {b : C0 σ}
    (hb : b ∈ Bsub σ) :
    ∃ Y : Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure X),
      KS11Lie6Proof.thetaHom (AlgebraicClosure X) Y =
        CFSG.RankThree.PartOne.KGD.triEmb X σ (AlgebraicClosure X) b := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP (AlgebraicClosure X) ℓ := triOdd_charP_closure hℓ hf hX
  exact KS11Lie6Proof.exists_thetaHom_of_mem_centralizer hf hℓ3 hX hσ (AlgebraicClosure X)
    (Fr := iterateFrobenius (AlgebraicClosure X) ℓ f) (fun c => iterateFrobenius_def ℓ f c) hb

theorem triOdd_bsub_tau {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) :
    ∀ b ∈ Bsub σ, tauAut σ b = b := by
  intro b hb
  obtain ⟨Y, hY⟩ := triOdd_exists_thetaHom_of_mem_bsub σ hℓ hℓ3 hf hX hσ hb
  have hPb : diagramMap TwistTag.D4 X * (b : ModGL TwistTag.D4.tag X) =
      (b : ModGL TwistTag.D4.tag X) * diagramMap TwistTag.D4 X := by
    apply baseChangeGL_injective (algebraMap X (AlgebraicClosure X))
    have hb' : baseChangeGL (algebraMap X (AlgebraicClosure X)) (b : ModGL TwistTag.D4.tag X) =
        KS11Lie6Proof.thetaHom (AlgebraicClosure X) Y := by
      rw [hY]
      rfl
    rw [map_mul, map_mul, baseChangeGL_diagramMap, hb']
    exact triOdd_diagramMap_comm_thetaHom (AlgebraicClosure X) Y
  have htw : twistHom TwistTag.D4 X σ.toRingHom (b : ModGL TwistTag.D4.tag X) = b :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ b.2)).2
  rw [CFSG.LieType.Chevalley.twistHom_apply] at htw
  apply Subtype.ext
  rw [coe_fieldActor]
  have h2 : diagramMap TwistTag.D4 X * Units.map (entrywiseHom σ.toRingHom)
      (b : ModGL TwistTag.D4.tag X) * (diagramMap TwistTag.D4 X)⁻¹ =
        diagramMap TwistTag.D4 X * (b : ModGL TwistTag.D4.tag X) *
          (diagramMap TwistTag.D4 X)⁻¹ := by
    rw [htw, hPb, mul_inv_cancel_right]
  exact mul_left_cancel (mul_right_cancel h2)

theorem triOdd_bsub_zpowers {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f)) :
    ∀ u ∈ Bsub σ, ∀ v ∈ Bsub σ, u ^ 3 = 1 → u ≠ 1 → v ^ 3 = 1 → u * v = v * u →
      v ∈ Subgroup.zpowers u := by
  intro u hu v hv hu3 hu1 hv3 huv
  haveI : CharP (AlgebraicClosure X) ℓ := triOdd_charP_closure hℓ hf hX
  have h3L : (3 : AlgebraicClosure X) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : AlgebraicClosure X) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure X) ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨Yu, hYu⟩ := triOdd_exists_thetaHom_of_mem_bsub σ hℓ hℓ3 hf hX hσ hu
  obtain ⟨Yv, hYv⟩ := triOdd_exists_thetaHom_of_mem_bsub σ hℓ hℓ3 hf hX hσ hv
  have hYu3 : Yu ^ 3 = 1 := KS11Lie6Proof.thetaHom_injective (by
    rw [map_pow, hYu, ← map_pow, hu3, map_one, map_one])
  have hYu1 : Yu ≠ 1 := fun h => hu1 (CFSG.RankThree.PartOne.KGD.triEmb_injective
    (L := AlgebraicClosure X) (by rw [← hYu, h, map_one, map_one]))
  have hYv3 : Yv ^ 3 = 1 := KS11Lie6Proof.thetaHom_injective (by
    rw [map_pow, hYv, ← map_pow, hv3, map_one, map_one])
  have hYuv : Yu * Yv = Yv * Yu := KS11Lie6Proof.thetaHom_injective (by
    rw [map_mul, map_mul, hYu, hYv, ← map_mul, ← map_mul, huv])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (sl2_commuting_cube_one h3L hYu3 hYu1 hYv3 hYuv)
  refine Subgroup.mem_zpowers_iff.2 ⟨k, CFSG.RankThree.PartOne.KGD.triEmb_injective
    (L := AlgebraicClosure X) ?_⟩
  rw [map_zpow, ← hYu, ← map_zpow, hk, hYv]

end Model

end CFSG.LieType.SeitzGeneration.ExcWideThree
