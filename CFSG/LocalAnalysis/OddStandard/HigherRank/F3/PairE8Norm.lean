module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Main

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi

variable {F : Type} [Field F]

noncomputable def dTheta (F : Type) [Field F] : ↥(adjointGroup .E8 F) :=
  ⟨rootSL2 .E8 F thetaE8 (HSL (-1)), rootSL2_mem_adjointGroup _ _⟩

theorem rootSL2_thetaE8_injective (hF : ringChar F ≠ 2) :
    Function.Injective (rootSL2 .E8 F thetaE8) :=
  ((exceptional_Lang_root_rank_one_data .E8 F thetaE8).2.2.2.2.2.2.2.1 hF).1

theorem dTheta_mem : dTheta F ∈ stdRankOne (e8Datum F) thetaE8 :=
  (mem_stdRankOne_e8_iff _).2 ⟨HSL (-1), rfl⟩

theorem coe_HSL_neg_one : ((HSL (-1 : Fˣ) : SL2 F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem HSL_neg_one_comm (B : SL2 F) : HSL (-1 : Fˣ) * B = B * HSL (-1 : Fˣ) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL_neg_one]
  simp

theorem dTheta_comm {r : ↥(adjointGroup .E8 F)} (hr : r ∈ stdRankOne (e8Datum F) thetaE8) :
    dTheta F * r = r * dTheta F := by
  obtain ⟨B, hB⟩ := (mem_stdRankOne_e8_iff r).1 hr
  refine Subtype.ext ?_
  simp only [dTheta, Subgroup.coe_mul, hB]
  rw [← map_mul, ← map_mul, HSL_neg_one_comm]

theorem dTheta_ne_one (hF : ringChar F ≠ 2) : dTheta F ≠ 1 := by
  intro h
  have h1 : rootSL2 .E8 F thetaE8 (HSL (-1)) = rootSL2 .E8 F thetaE8 1 := by
    rw [map_one]
    exact congrArg Subtype.val h
  have h2 := rootSL2_thetaE8_injective hF h1
  have h3 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) h2
  simp only [coe_HSL_neg_one, Matrix.SpecialLinearGroup.coe_one] at h3
  simp at h3
  exact Ring.neg_one_ne_one_of_char_ne_two hF h3

theorem parabolicLevi_le_normalizer_rootRankOne :
    parabolicLevi .E8 F JE8 ≤
      Subgroup.normalizer (rootRankOneGroup .E8 F thetaE8 : Set (ModGL .E8 F)) := by
  intro n hn
  have h1 : ∀ m ∈ parabolicLevi .E8 F JE8, ∀ y ∈ rootRankOneGroup .E8 F thetaE8,
      m * y * m⁻¹ ∈ rootRankOneGroup .E8 F thetaE8 := by
    intro m hm y hy
    obtain ⟨A, rfl⟩ := hy
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq hm A
    exact ⟨A', hA'.symm⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact h1 n hn y hy
  · intro hy
    have := h1 n⁻¹ (inv_mem hn) _ hy
    simpa [mul_assoc] using this

theorem toralRootGroup_le_normalizer_rootRankOne (hF : ringChar F ≠ 2) :
    toralRootGroup .E8 F (thetaDiag thetaE8 (-1 : Fˣ)) ≤
      Subgroup.normalizer (rootRankOneGroup .E8 F thetaE8 : Set (ModGL .E8 F)) := by
  refine sup_le (fun t ht => parabolicLevi_le_normalizer_rootRankOne
    (torusGroup_le_parabolicLevi JE8 ht)) ?_
  refine iSup₂_le fun σ hσ => ?_
  obtain ⟨hσr, hσ1⟩ := hσ
  have hev : Even (iform thetaE8 σ) := by
    refine even_of_neg_one_zpow_eq_one hF ?_
    rw [← rootChar_thetaDiag]
    exact hσ1
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E8 F isRoot_thetaE8).1
  rcases eq_or_iform_eq_zero_of_even hσr hev with rfl | rfl | h0
  · intro x hx
    have : x ∈ rootRankOneGroup .E8 F thetaE8 := by
      rw [hL]
      exact Subgroup.mem_sup_left hx
    exact Subgroup.le_normalizer this
  · intro x hx
    have : x ∈ rootRankOneGroup .E8 F thetaE8 := by
      rw [hL]
      exact Subgroup.mem_sup_right hx
    exact Subgroup.le_normalizer this
  · intro x hx
    exact parabolicLevi_le_normalizer_rootRankOne
      (rootSubgroup_le_parabolicLevi' (mem_parabolicRoots_E8 hσr h0) hx)

theorem conj_stdRankOne_of_commute_dTheta (hF : ringChar F ≠ 2) {x : ↥(adjointGroup .E8 F)}
    (hx : x * dTheta F = dTheta F * x) {r : ↥(adjointGroup .E8 F)}
    (hr : r ∈ stdRankOne (e8Datum F) thetaE8) : x * r * x⁻¹ ∈ stdRankOne (e8Datum F) thetaE8 := by
  obtain ⟨B, hB⟩ := (mem_stdRankOne_e8_iff r).1 hr
  have hdθ : rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : Fˣ)) =
      rootSL2 .E8 F thetaE8 (HSL (-1)) := (rootTorusSL2_thetaE8 (-1)).symm
  have hxT : (x : ModGL .E8 F) ∈ toralCentralizer .E8 F (thetaDiag thetaE8 (-1 : Fˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨x.2, ?_⟩
    rw [hdθ, mul_inv_eq_iff_eq_mul]
    exact (congrArg Subtype.val hx).symm
  have hM := toralCentralizer_le_toralRootGroup_of_sign (Or.inr (Or.inr (Or.inr rfl))) hF
    (thetaDiag_neg_one_sign thetaE8) hxT
  have hN := toralRootGroup_le_normalizer_rootRankOne hF hM
  rw [Subgroup.mem_normalizer_iff] at hN
  refine (mem_stdRankOne_e8_iff _).2 ?_
  have h1 : (rootSL2 .E8 F thetaE8) B ∈ rootRankOneGroup .E8 F thetaE8 := ⟨B, rfl⟩
  obtain ⟨A', hA'⟩ := (hN _).1 h1
  refine ⟨A', ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hB]
  exact hA'.symm

end CFSG.OddStandard.HigherRank.F3
