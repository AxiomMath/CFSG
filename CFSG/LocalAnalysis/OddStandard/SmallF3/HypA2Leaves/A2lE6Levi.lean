module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogue

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Open (StatedSU)

variable {K : Type} [Field K] [Finite K]

theorem a2lE6_leviHom_injective [CharP K 3] (σ : K ≃+* K) {ζ : K} (hζ : ζ ≠ 0)
    (hσζ : σ ζ = -ζ) : Function.Injective (leviHom σ hζ hσζ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : leviHomA σ hζ x = 1 := congrArg Subtype.val hx
  rw [leviHomA, MonoidHom.comp_apply] at h1
  have h2 : CFSG.LieType.Chevalley.ExteriorCube.cubeHom (conjSU σ hζ x) = 1 := by
    rw [← psiA_liftA, h1, map_one]
  obtain ⟨l, hl3, hl⟩ :=
    (CFSG.LieType.Chevalley.ExteriorCube.cubeHom_eq_one_iff _).1 h2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hl1 : l = 1 :=
    CFSG.LieType.BorelTits.eq_one_of_pow_char_pow_eq_one (F := K) (x := l) (e := 1) 3
      (by simpa using hl3)
  have he := eDiag_ne_zero (K := K) hζ
  have hx' : (conjSU σ hζ x : Matrix (Fin 6) (Fin 6) K) =
      Matrix.diagonal (eDiag K ζ) * ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        Matrix.diagonal (fun i => (eDiag K ζ i)⁻¹) := rfl
  have hX : ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [hx', hl1, one_smul] at hl
    calc ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
        = (Matrix.diagonal (fun i => (eDiag K ζ i)⁻¹) * Matrix.diagonal (eDiag K ζ)) *
            ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
              (Matrix.diagonal (fun i => (eDiag K ζ i)⁻¹) * Matrix.diagonal (eDiag K ζ)) := by
          rw [diag_inv_mul _ he, one_mul, mul_one]
      _ = Matrix.diagonal (fun i => (eDiag K ζ i)⁻¹) * (Matrix.diagonal (eDiag K ζ) *
            ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
              Matrix.diagonal (fun i => (eDiag K ζ i)⁻¹)) * Matrix.diagonal (eDiag K ζ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hl, Matrix.mul_one, diag_inv_mul _ he]
  apply Subtype.ext
  apply Units.ext
  simpa using hX

theorem a2lE6_twE6LeviSA_le (σ : K ≃+* K) (hK : Nat.card K = 9) (hσ : ∀ c, σ c = c ^ 3) :
    twE6LeviSA K σ ≤ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  have hK3 : Nat.card K = 3 ^ 2 := by rw [hK]; norm_num
  let Q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, one_pos⟩
  have hQ : Q.card = 3 := by rw [TauCeti.PrimePower.card_def]; rfl
  have hperf : ⁅subsystemGroup Tag.E6 K C2E6Std.setA ⊓
      twistedFixedGroup TwistTag.E6 K σ.toRingHom,
      subsystemGroup Tag.E6 K C2E6Std.setA ⊓
        twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ =
      subsystemGroup Tag.E6 K C2E6Std.setA ⊓
        twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
    simpa only [twE6LeviSA, groupA] using twE6LeviSA_perfect (q := 3) σ hK3 hσ Q hQ
  have h := (twE6LongRootLevi_eq_subsystem (p := 3) (f := 1) σ Nat.prime_three le_rfl hK3
    hσ hperf).1
  simpa only [twE6LeviSA, groupA] using h

theorem a2lE6_groupA_inf (σ : K ≃+* K) (hK : Nat.card K = 9) (hσ : ∀ c, σ c = c ^ 3) :
    groupA K ⊓ graphFixedRootGroup TwistTag.E6 K σ.toRingHom = twE6LeviSA K σ := by
  refine le_antisymm ?_ ?_
  · rw [twE6LeviSA]
    exact inf_le_inf_left _ (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom)
  · rw [twE6LeviSA]
    exact le_inf inf_le_left (a2lE6_twE6LeviSA_le σ hK hσ)

@[expose] def a2lE6_leviEquiv [CharP K 3] (σ : K ≃+* K) {ζ : K} (hζ : ζ ≠ 0)
    (hσζ : σ ζ = -ζ) (hσσ : ∀ c, σ (σ c) = c) :
    SU σ 6 ≃* ↥(twE6LeviSA K σ) :=
  ((MulEquiv.ofBijective (leviHom σ hζ hσζ)
      ⟨a2lE6_leviHom_injective σ hζ hσζ, leviHom_surjective σ hζ hσσ hσζ⟩).trans
    (MonoidHom.ofInjective (fixAToMod_injective σ))).trans
    (MulEquiv.subgroupCongr (range_fixAToMod σ))

theorem a2lE6_coe_leviEquiv [CharP K 3] (σ : K ≃+* K) {ζ : K} (hζ : ζ ≠ 0)
    (hσζ : σ ζ = -ζ) (hσσ : ∀ c, σ (σ c) = c) (x : SU σ 6) :
    ((a2lE6_leviEquiv σ hζ hσζ hσσ x : twE6LeviSA K σ) : ModGL Tag.E6 K) =
      ((leviHomA σ hζ x : groupA K) : ModGL Tag.E6 K) := rfl

theorem a2lE6_twE6LeviSA_quasisimple (σ : K ≃+* K) (hK : Nat.card K = 9)
    (hσ : ∀ c, σ c = c ^ 3) : CFSG.Assembly.IsQuasisimple ↥(twE6LeviSA K σ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : Nat.card K = 3 ^ 2 := by rw [hK]; norm_num
  haveI : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three (by norm_num) hK3
  have hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution K 3 1 :=
    RingEquiv.ext fun c => by
      rw [hσ c, CFSG.LieType.BorelTits.unitaryInvolution_apply]
      norm_num
  subst σ
  obtain ⟨ζ, hζ, hσζ⟩ :=
    exists_trace_zero (CFSG.LieType.BorelTits.unitaryInvolution K 3 1) (by norm_num) hK3
      (fun c => by rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]; norm_num)
  have hK3' : Nat.card K = (3 ^ 1) ^ 2 := by simpa using hK3
  have hσσ : ∀ c, CFSG.LieType.BorelTits.unitaryInvolution K 3 1
      (CFSG.LieType.BorelTits.unitaryInvolution K 3 1 c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive (K := K) (p := 3) (f := 1) hK3'
  have hQS : CFSG.IsQuasisimple
      (SU (CFSG.LieType.BorelTits.unitaryInvolution K 3 1) 6) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_SU (p := 3) (f := 1)
      hK3' (by norm_num) (by simp)
  have hQS' : CFSG.IsQuasisimple
      ↥(twE6LeviSA K (CFSG.LieType.BorelTits.unitaryInvolution K 3 1)) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (a2lE6_leviEquiv (CFSG.LieType.BorelTits.unitaryInvolution K 3 1) hζ hσζ hσσ).symm hQS
  exact ⟨hQS'.1.commutator_eq_top, hQS'.2.1⟩

theorem a2lE6_exists_equiv_statedSU (σ : K ≃+* K) (hK : Nat.card K = 9)
    (hσ : ∀ c, σ c = c ^ 3) {ζ : K} (hζ : ζ ≠ 0) (hσζ : σ ζ = -ζ) :
    ∃ e₀ : twE6LeviSA K σ ≃* StatedSU 6 3 K,
      ∀ (x : SU σ 6),
        (x : GL (Fin 6) K) = Matrix.GeneralLinearGroup.scalar (Fin 6) (-1 : Kˣ) →
        ∀ y : twE6LeviSA K σ,
          (y : ModGL Tag.E6 K) = ((leviHomA σ hζ x : groupA K) : ModGL Tag.E6 K) →
          ((e₀ y : StatedSU 6 3 K) : GL (Fin 6) K) =
            Matrix.GeneralLinearGroup.scalar (Fin 6) (-1 : Kˣ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : Nat.card K = 3 ^ 2 := by rw [hK]; norm_num
  haveI : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three (by norm_num) hK3
  have hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution K 3 1 :=
    RingEquiv.ext fun c => by
      rw [hσ c, CFSG.LieType.BorelTits.unitaryInvolution_apply]
      norm_num
  subst σ
  have hK3' : Nat.card K = (3 ^ 1) ^ 2 := by simpa using hK3
  have hσσ : ∀ c, CFSG.LieType.BorelTits.unitaryInvolution K 3 1
      (CFSG.LieType.BorelTits.unitaryInvolution K 3 1 c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive (K := K) (p := 3) (f := 1) hK3'
  let e : SU (CFSG.LieType.BorelTits.unitaryInvolution K 3 1) 6 ≃*
      ↥(twE6LeviSA K (CFSG.LieType.BorelTits.unitaryInvolution K 3 1)) :=
    a2lE6_leviEquiv (CFSG.LieType.BorelTits.unitaryInvolution K 3 1) hζ hσζ hσσ
  set P : GL (Fin 6) K :=
    (CFSG.LieType.Universal.Unitary.exists_wittMatrix (p := 3) (f := 1) hK3' 6).choose with hPdef
  let eW : SU (CFSG.LieType.BorelTits.unitaryInvolution K 3 1) 6 ≃*
      StatedSU 6 (3 ^ 1) K :=
    (CFSG.LieType.Universal.Unitary.conjEquiv P
        ((CFSG.LieType.Universal.Unitary.exists_wittMatrix
          (p := 3) (f := 1) hK3' 6).choose_spec)).trans
      (MulEquiv.subgroupCongr
        (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 3) (f := 1) hK3' 6))
  refine ⟨e.symm.trans eW, ?_⟩
  intro x hx y hy
  have hyx : y = e x := by
    apply Subtype.ext
    rw [hy, a2lE6_coe_leviEquiv]
  have heq : (e.symm.trans eW) y = eW x := by
    rw [hyx, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [heq]
  have hcoe : ((eW x : StatedSU 6 (3 ^ 1) K) : GL (Fin 6) K) =
      P * (x : GL (Fin 6) K) * P⁻¹ := rfl
  rw [hcoe]
  have hxCen : (x : GL (Fin 6) K) ∈ Subgroup.center (GL (Fin 6) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨-1, hx.symm⟩
  have hcomm : P * (x : GL (Fin 6) K) = (x : GL (Fin 6) K) * P :=
    Subgroup.mem_center_iff.mp hxCen P
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  exact hx

end CFSG.OddStandard.SmallF3.HypA2Leaves
