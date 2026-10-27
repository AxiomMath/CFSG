module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Six

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace TwA5Eight

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)

theorem twA5_card_F (h : UnitaryFieldData 2 3 F) : Nat.card F = 64 := by
  rw [h.card]
  norm_num

theorem twA5_card_rootsOfUnity_nine (h : UnitaryFieldData 2 3 F) :
    Nat.card (rootsOfUnity 9 F) = 9 := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [twA5_card_F h]; norm_num)
  apply CFSG.LinearGroups.card_rootsOfUnity_of_dvd
  rw [twA5_card_F h]
  norm_num

noncomputable def twA5Lambda : rootsOfUnity 9 F :=
  Classical.choose (IsCyclic.exists_generator (α := rootsOfUnity 9 F))

theorem twA5Lambda_gen : Subgroup.zpowers (twA5Lambda (F := F)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact Classical.choose_spec (IsCyclic.exists_generator (α := rootsOfUnity 9 F)) x

theorem orderOf_twA5Lambda (h : UnitaryFieldData 2 3 F) :
    orderOf (twA5Lambda (F := F)) = 9 := by
  rw [orderOf_eq_card_of_zpowers_eq_top (twA5Lambda_gen (F := F)),
    twA5_card_rootsOfUnity_nine h]

theorem pow_nine_twA5Lambda : ((twA5Lambda (F := F) : Fˣ) : F) ^ 9 = 1 := by
  have h := (mem_rootsOfUnity (M := F) 9 (twA5Lambda (F := F) : Fˣ)).mp
    (twA5Lambda (F := F)).2
  simpa using congrArg (fun u : Fˣ => (u : F)) h

theorem norm_twA5Lambda : h.norm ((twA5Lambda (F := F) : Fˣ) : F) = 1 :=
  norm_eq_one_of_pow_nine h (pow_nine_twA5Lambda (F := F))

theorem pow_six_twA5Lambda_ne_one (h : UnitaryFieldData 2 3 F) :
    ((twA5Lambda (F := F) : Fˣ) : F) ^ 6 ≠ 1 := by
  intro h6
  have h6u : (twA5Lambda (F := F) : Fˣ) ^ 6 = 1 := by
    apply Units.ext
    simpa using h6
  have hord_u : orderOf ((twA5Lambda (F := F) : Fˣ)) = 9 := by
    rw [Subgroup.orderOf_coe (twA5Lambda (F := F))]
    exact orderOf_twA5Lambda h
  have hdvd := orderOf_dvd_of_pow_eq_one h6u
  rw [hord_u] at hdvd
  norm_num at hdvd

theorem twA5XParam_mem : ((twA5Lambda (F := F) : Fˣ), 1, 1, 1) ∈ twA5Param (F := F) := by
  rw [mem_twA5Param]
  refine ⟨?_, by simp, by simp, by simp⟩
  exact (mem_rootsOfUnity (M := F) 9 (twA5Lambda (F := F) : Fˣ)).mp
    (twA5Lambda (F := F)).2

noncomputable abbrev twA5XParam : twA5Param (F := F) :=
  ⟨((twA5Lambda (F := F) : Fˣ), 1, 1, 1), twA5XParam_mem (F := F)⟩

theorem twA5Hom_X_eq_diagFiveLast :
    twA5Hom h (twA5XParam (F := F)) =
      diagFiveLast h ((twA5Lambda (F := F) : Fˣ) : F) (norm_twA5Lambda h) := by
  rw [twA5Hom_apply]
  unfold twA5Diag diagFiveLast
  congr 3
  · funext i
    fin_cases i <;> simp [twA5Entries, diagFiveLastEntries]
  all_goals apply Subsingleton.elim

@[expose] noncomputable def twA5X : unitaryPSU h 6 :=
  unitaryProj h 6 (twA5Hom h (twA5XParam (F := F)))

theorem twA5X_mem_B : twA5X h ∈ (twA5Hom h).range.map (unitaryProj h 6) :=
  Subgroup.mem_map_of_mem _ ⟨twA5XParam (F := F), rfl⟩

theorem twA5X_ne_one : twA5X h ≠ 1 := by
  intro hx1
  have hmemker : twA5Hom h (twA5XParam (F := F)) ∈ (unitaryProj h 6).ker := by
    rw [MonoidHom.mem_ker]
    exact hx1
  rw [ker_unitaryProj] at hmemker
  rw [twA5Hom_X_eq_diagFiveLast h] at hmemker
  rw [mem_unitaryScalars] at hmemker
  obtain ⟨c, hc, -, hmat⟩ := hmemker
  have hmat' := congrArg (fun z : GL (Fin 6) F => ((z : Matrix (Fin 6) (Fin 6) F))) hmat
  have h0 := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M 0 0) hmat'
  have h5 := congrArg (fun M : Matrix (Fin 6) (Fin 6) F => M 5 5) hmat'
  simp only [coe_diagFiveLast, Matrix.diagonal_apply_eq] at h0 h5
  simp [diagFiveLastEntries] at h0 h5
  have h0c : ((twA5Lambda (F := F) : Fˣ) : F) = (c : F) := by
    simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply] using h0
  have h5c : (((twA5Lambda (F := F) : Fˣ) : F) ^ 5)⁻¹ = (c : F) := by
    simpa [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply] using h5
  have h5c' : ((c : F) ^ 5)⁻¹ = (c : F) := by
    simpa [h0c] using h5c
  have h6c : (c : F) ^ 6 = 1 := by
    have h : (c : F) ^ 6 = (c : F) ^ 5 * (c : F) := by ring
    rw [h]
    nth_rewrite 2 [← h5c']
    exact mul_inv_cancel₀ (pow_ne_zero 5 (Units.ne_zero c))
  have h6 : ((twA5Lambda (F := F) : Fˣ) : F) ^ 6 = 1 := by
    rw [h0c]
    exact h6c
  exact pow_six_twA5Lambda_ne_one h h6

theorem twA5X_pow_three : (twA5X h) ^ 3 = 1 := by
  change ((unitaryProj h 6) (twA5Hom h (twA5XParam (F := F)))) ^ 3 = 1
  rw [← map_pow]
  have hmem : (twA5Hom h (twA5XParam (F := F))) ^ 3 ∈ (unitaryProj h 6).ker := by
    rw [ker_unitaryProj]
    exact twA5Hom_pow_three_mem h (twA5XParam (F := F))
  exact MonoidHom.mem_ker.mp hmem

theorem isQuasisimple_blockSU_five :
    CFSG.IsQuasisimple ↥(blockSU h suFiveIndex) := by
  apply isQuasisimple_blockSU h
  · rw [card_suFiveIndex]; norm_num
  · rw [card_suFiveIndex]; norm_num

theorem hasLabel_blockSU_five :
    HasLabel ↥(blockSU h suFiveIndex) (· = (⟨.twA, 4, 3⟩ : GLALabel)) := by
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [twA5_card_F h]; norm_num)
  have hI : suFiveIndex.card < 6 := by rw [card_suFiveIndex]; norm_num
  have hSU : HasLabel (unitarySU 2 3 F 5) (· = (⟨.twA, 4, 3⟩ : GLALabel)) := by
    refine hasLabel_of_statedClassicalModel_PSU (r := 4) (n := 3)
      (isQuasisimple_unitarySU h (by norm_num) (by norm_num)) ?_
    have hStated : StatedClassicalModel (unitaryPSU h 5) .PSU 5 2 3 := by
      refine ⟨⟨Nat.prime_two, h.one_le, by norm_num, by norm_num⟩, ?_⟩
      exact ⟨F, inferInstance, inferInstance, by rw [twA5_card_F h]; norm_num,
        ⟨unitaryPSUEquiv h (by norm_num)⟩⟩
    have hiso : unitarySU 2 3 F 5 ⧸ Subgroup.center (unitarySU 2 3 F 5) ≃* unitaryPSU h 5 :=
      QuotientGroup.quotientMulEquivOfEq (center_unitarySU_eq_unitaryScalars h 5)
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv hiso.symm hStated
  exact (hasLabel_congr (blockSUEquiv h hI) _).1 hSU

theorem twA5X_eq_proj_diagFiveLast :
    twA5X h =
      unitaryProj h 6 (diagFiveLast h ((twA5Lambda (F := F) : Fˣ) : F) (norm_twA5Lambda h)) := by
  rw [twA5X, twA5Hom_X_eq_diagFiveLast h]

theorem blockSU_five_le_centralizer_X :
    blockSU h suFiveIndex ≤ Subgroup.centralizer ({twA5X h} : Set (unitaryPSU h 6)) := by
  rw [twA5X_eq_proj_diagFiveLast h]
  rw [centralizer_unitaryProj_diagFiveLast h (norm_twA5Lambda h)
    (pow_six_twA5Lambda_ne_one h)]
  exact Subgroup.map_mono (unitaryBlock_le_unitaryBlockDiag h suFiveIndex)

theorem commutator_mem_blockSU_five_of_centralizer_X
    {g k : unitaryPSU h 6}
    (hg : g ∈ Subgroup.centralizer ({twA5X h} : Set (unitaryPSU h 6)))
    (hk : k ∈ Subgroup.centralizer ({twA5X h} : Set (unitaryPSU h 6))) :
    g * k * g⁻¹ * k⁻¹ ∈ blockSU h suFiveIndex := by
  have hC := centralizer_unitaryProj_diagFiveLast h (norm_twA5Lambda h)
    (pow_six_twA5Lambda_ne_one h)
  rw [twA5X_eq_proj_diagFiveLast h] at hg hk
  rw [hC] at hg hk
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.1 hk
  have hcomm := commutator_unitaryBlockDiag_le_unitaryBlock h (compl_suFiveIndex)
    (Subgroup.commutator_mem_commutator hA hB)
  have hgoal : (unitaryProj h 6) (A * B * A⁻¹ * B⁻¹) ∈ blockSU h suFiveIndex :=
    unitaryProj_mem_blockSU h hcomm
  simpa only [map_mul, map_inv] using hgoal

theorem twA5Lambda_pow_nine : ((twA5Lambda (F := F) : Fˣ)) ^ 9 = 1 :=
  (mem_rootsOfUnity (M := F) 9 (twA5Lambda (F := F) : Fˣ)).mp (twA5Lambda (F := F)).2

theorem zpowers_lambda_eq_roots (h : UnitaryFieldData 2 3 F) :
    Subgroup.zpowers ((twA5Lambda (F := F) : Fˣ)) = rootsOfUnity 9 F := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hm]
    exact Subgroup.zpow_mem _ (twA5Lambda (F := F)).2 m
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, orderOf_twA5Lambda h,
      twA5_card_rootsOfUnity_nine h]

theorem mem_zpowers_lambda_nat {a : Fˣ}
    (ha : a ∈ Subgroup.zpowers ((twA5Lambda (F := F) : Fˣ))) :
    ∃ n : ℕ, a = ((twA5Lambda (F := F) : Fˣ)) ^ n := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
  refine ⟨(m % 9).toNat, ?_⟩
  rw [← hm]
  rw [zpow_eq_zpow_emod' m (twA5Lambda_pow_nine (F := F))]
  rw [← zpow_natCast]
  congr 1
  exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))).symm

end TwA5Eight

end CFSG.LocalAnalysis.GLTheoremA.Y10F
