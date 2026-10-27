module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValSU5U
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapUOMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValSU4U

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.LieType.Universal.Unitary
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.SeitzReduction.SymplecticPilot (ctuEmbed ctuCoord ctuEmbed_apply_ctuCoord
  coe_ctuEmbed_elt_positiveLong)

section Mat

variable {N ε : ℕ} {K F : Type} [Field K] [Field F] [CharP K 2] {hε : ε ≤ 1} {σ : F ≃+* F}
  {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

theorem coe_ctuEmbed_elt_positiveSum (p p' : Fin N) (hpp : p < p') (c : K) :
    (((ctuEmbed ε hε σ ι hι (elt (.positiveSum p p' hpp) c) : SU σ (2 * N + ε)) :
      GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
        1 + single (ctuCoord N ε (Sum.inl (Sum.inl p))) (ctuCoord N ε (Sum.inl (Sum.inr p')))
          (ι c) + single (ctuCoord N ε (Sum.inl (Sum.inl p')))
            (ctuCoord N ε (Sum.inl (Sum.inr p))) (ι c) := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [ctuEmbed_apply_ctuCoord, mat_elt, Matrix.add_apply, Matrix.add_apply, single_apply,
    single_apply, one_apply]
  simp only [(ctuCoord N ε).injective.eq_iff]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, map_apply, Matrix.add_apply, Matrix.smul_apply, one_apply]
    simp only [E, Matrix.add_apply, single_apply, Sum.inl.injEq, smul_eq_mul]
    split_ifs <;> simp_all <;> ring
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₂, one_apply]
    simp

end Mat

section Transport

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def ringEquivF4c (hF : Nat.card F = (2 ^ 1) ^ 2) : F ≃+* F4c :=
  letI := Fintype.ofFinite F
  FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, hF, CFSG.GH74.Uniqueness.SU.SU5.F4c.card_eq]
    norm_num)

theorem ringEquivF4c_frob (hF : Nat.card F = (2 ^ 1) ^ 2) (c : F) :
    ringEquivF4c hF (unitaryInvolution F 2 1 c) = f4Frob (ringEquivF4c hF c) := by
  rw [unitaryInvolution_apply, f4Frob_apply, pow_one, sq, map_mul]

theorem mapMatrix_one_add_single (φ : F ≃+* F4c) {n : ℕ} (a b : Fin n) :
    φ.mapMatrix (1 + single a b (1 : F)) = 1 + single a b 1 := by
  rw [map_add, map_one]
  congr 1
  ext i j
  simp [single_apply]

theorem mapMatrix_one_add_single_add_single (φ : F ≃+* F4c) {n : ℕ} (a b a' b' : Fin n) :
    φ.mapMatrix (1 + single a b (1 : F) + single a' b' 1) = 1 + single a b 1 + single a' b' 1 := by
  rw [map_add, mapMatrix_one_add_single]
  congr 1
  ext i j
  simp [single_apply]

end Transport

section U6

variable {K F : Type} [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2]

theorem ctuCoord_two_e0 {ε : ℕ} : ctuCoord 2 ε (Sum.inl (Sum.inl 0)) = ⟨0, by omega⟩ :=
  Fin.ext rfl

theorem ctuCoord_two_e1 {ε : ℕ} : ctuCoord 2 ε (Sum.inl (Sum.inl 1)) = ⟨1, by omega⟩ :=
  Fin.ext rfl

theorem ctuCoord_two_f0 {ε : ℕ} : ctuCoord 2 ε (Sum.inl (Sum.inr 0)) = ⟨3 + ε, by omega⟩ :=
  Fin.ext (by simp only [SymplecticPilot.ctuCoord_inl_inr]; omega)

theorem ctuCoord_two_f1 {ε : ℕ} : ctuCoord 2 ε (Sum.inl (Sum.inr 1)) = ⟨2 + ε, by omega⟩ :=
  Fin.ext (by simp only [SymplecticPilot.ctuCoord_inl_inr]; omega)

theorem coe_twoSUTransvection {ε : ℕ} (hε : ε ≤ 1) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    (((twoSUTransvection hε ι hι : SU (unitaryInvolution F 2 1) (2 * 2 + ε)) :
      GL (Fin (2 * 2 + ε)) F) : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) F) =
        1 + single ⟨0, by omega⟩ ⟨3 + ε, by omega⟩ 1 := by
  rw [twoSUTransvection, coe_ctuEmbed_elt_positiveLong, map_one, ctuCoord_two_e0,
    ctuCoord_two_f0]

theorem coe_twoSURankTwo {ε : ℕ} (hε : ε ≤ 1) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    (((twoSURankTwo hε ι hι : SU (unitaryInvolution F 2 1) (2 * 2 + ε)) :
      GL (Fin (2 * 2 + ε)) F) : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) F) =
        1 + single ⟨0, by omega⟩ ⟨2 + ε, by omega⟩ 1 +
          single ⟨1, by omega⟩ ⟨3 + ε, by omega⟩ 1 := by
  rw [twoSURankTwo, coe_ctuEmbed_elt_positiveSum, map_one, ctuCoord_two_e0, ctuCoord_two_e1,
    ctuCoord_two_f0, ctuCoord_two_f1]

theorem suCongr_twoSUTransvection_zero (hF : Nat.card F = (2 ^ 1) ^ 2) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    suCongr (ringEquivF4c hF) (ringEquivF4c_frob hF) (2 * 2 + 0)
      (twoSUTransvection (Nat.zero_le 1) ι hι) = su4T := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_suCongr]
  change (ringEquivF4c hF).mapMatrix _ = su4TM
  rw [coe_twoSUTransvection, mapMatrix_one_add_single]
  decide

theorem suCongr_twoSURankTwo_zero (hF : Nat.card F = (2 ^ 1) ^ 2) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    suCongr (ringEquivF4c hF) (ringEquivF4c_frob hF) (2 * 2 + 0)
      (twoSURankTwo (Nat.zero_le 1) ι hι) = su4U := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_suCongr]
  change (ringEquivF4c hF).mapMatrix _ = su4UM
  rw [coe_twoSURankTwo, mapMatrix_one_add_single_add_single]
  decide

theorem twoSUCentValues_unitary6 (hF : Nat.card F = (2 ^ 1) ^ 2) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    TwoSUCentValues .unitary6 (Nat.zero_le 1) ι hι := by
  refine ⟨?_, ?_⟩
  · rw [← card_centralizer_mulEquiv (suCongr (ringEquivF4c hF) (ringEquivF4c_frob hF)
      (2 * 2 + 0)), suCongr_twoSUTransvection_zero]
    exact su4_card_centralizer_t
  · rw [← card_centralizer_mulEquiv (suCongr (ringEquivF4c hF) (ringEquivF4c_frob hF)
      (2 * 2 + 0)), suCongr_twoSURankTwo_zero]
    exact su4_card_centralizer_u

theorem twoUnitary6CentInput_holds : TwoUnitary6CentInput :=
  fun _ _ _ _ _ _ _ _ hF ι hι => twoSUCentValues_unitary6 hF ι hι

end U6

section U7

variable {K F : Type} [Field K] [CharP K 2] [Field F] [Finite F] [CharP F 2]

theorem suCongr_twoSUTransvection_one (hF : Nat.card F = (2 ^ 1) ^ 2) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    suCongr (ringEquivF4c hF) (ringEquivF4c_frob hF) (2 * 2 + 1)
      (twoSUTransvection le_rfl ι hι) = su5T := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_suCongr]
  change (ringEquivF4c hF).mapMatrix _ = su5TM
  rw [coe_twoSUTransvection, mapMatrix_one_add_single]
  decide

theorem suCongr_twoSURankTwo_one (hF : Nat.card F = (2 ^ 1) ^ 2) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    suCongr (ringEquivF4c hF) (ringEquivF4c_frob hF) (2 * 2 + 1)
      (twoSURankTwo le_rfl ι hι) = su5U := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_suCongr]
  change (ringEquivF4c hF).mapMatrix _ = su5UM
  rw [coe_twoSURankTwo, mapMatrix_one_add_single_add_single]
  decide

theorem twoSUCentValues_unitary7 (hF : Nat.card F = (2 ^ 1) ^ 2) (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c) :
    TwoSUCentValues .unitary7 le_rfl ι hι := by
  refine ⟨?_, ?_⟩
  · rw [← card_centralizer_mulEquiv (suCongr (ringEquivF4c hF) (ringEquivF4c_frob hF)
      (2 * 2 + 1)), suCongr_twoSUTransvection_one]
    exact su5_card_centralizer_t
  · rw [← card_centralizer_mulEquiv (suCongr (ringEquivF4c hF) (ringEquivF4c_frob hF)
      (2 * 2 + 1)), suCongr_twoSURankTwo_one]
    exact su5_card_centralizer_u

theorem twoUnitary7CentInput_holds : TwoUnitary7CentInput :=
  fun _ _ _ _ _ _ _ _ hF ι hι => twoSUCentValues_unitary7 hF ι hι

end U7

section Assembly

theorem twoOverlapInvGraphInput_of_omegaValues (hVp : TwoOmegaPlusModelValues)
    (hVm : TwoOmegaMinusModelValues) : TwoOverlapInvGraphInput :=
  twoOverlapInvGraphInput_of_values twoUnitary6CentInput_holds twoUnitary7CentInput_holds hVp hVm

theorem twoRowsCatInput_of_omegaValues (hVp : TwoOmegaPlusModelValues)
    (hVm : TwoOmegaMinusModelValues) (hF : TwoFieldPairInput) (hS : TwoSwapPairInput)
    (hE : TwoE6PairInput) (hT : TwoTwistedE6PairInput) : TwoRowsCatInput :=
  twoRowsCatInput_of_overlapInvGraphInput (twoOverlapInvGraphInput_of_omegaValues hVp hVm) hF hS
    hE hT

end Assembly

end CFSG.SeitzReduction.F4Pilot
