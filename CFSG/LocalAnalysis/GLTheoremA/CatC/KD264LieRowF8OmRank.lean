module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8OmCoreAbs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open QuadraticMap Module

local notation "Ω[" Q "]" =>
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆

@[expose] def BigElem (T : Type) [Group T] : Prop :=
  ∃ E : Subgroup T, IsElemAbelian 3 E ∧ 3 ^ 4 ≤ Nat.card E

theorem bigElem_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T') (h : BigElem T) :
    BigElem T' := by
  obtain ⟨E, hE, hcard⟩ := h
  refine ⟨E.map (e : T →* T'), isElemAbelian_of_map 3 e hE, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective]
  exact hcard

section Derived

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_big_torus (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hn : 5 ≤ n) :
    ∃ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ Ω[Q] ∧ IsElemAbelian 3 E ∧ 3 ^ 4 ≤ Nat.card E := by
  classical
  let s : Set (Subgroup (V ≃ₗ[ZMod 2] V)) := {E | E ≤ Ω[Q] ∧ IsElemAbelian 3 E}
  have hbot : (⊥ : Subgroup (V ≃ₗ[ZMod 2] V)) ∈ s :=
    ⟨bot_le, ⟨⟨⟨fun a b => by rw [Subsingleton.elim a b]⟩⟩, fun x hx => by
      rw [Subgroup.mem_bot.1 hx]
      simp⟩⟩
  have hfin : s.Finite := Set.toFinite s
  obtain ⟨E, ⟨hEΩ, hE⟩, hmaxE⟩ := Set.exists_max_image s (fun E => Nat.card E) hfin ⟨⊥, hbot⟩
  have hmax : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V), E' ≤ Ω[Q] → IsElemAbelian 3 E' →
      Nat.card E' ≤ Nat.card E := fun E' h1 h2 => hmaxE E' ⟨h1, h2⟩
  obtain ⟨l, hl, hEeq, hno⟩ := exists_frame_max hQ hEΩ hE hmax
  have hPd : finrank (ZMod 2) (perpL Q l) = 2 * n - 2 * l.length := by
    rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hl.finrank_Wspan]
  have hle2 := hl.finrank_perpL_le hQ hno
  have hWle : finrank (ZMod 2) (Wspan l) ≤ finrank (ZMod 2) V := Submodule.finrank_le _
  rw [hl.finrank_Wspan, hdim] at hWle
  have hlen : 4 ≤ l.length := by omega
  refine ⟨E, hEΩ, hE, ?_⟩
  rw [hEeq, card_torus hl]
  exact Nat.pow_le_pow_right (by norm_num) hlen

theorem bigElem_derived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hn : 5 ≤ n) : BigElem ↥(Ω[Q]) := by
  obtain ⟨E, hEΩ, hE, hcard⟩ := exists_big_torus hQ hdim hn
  refine ⟨E.subgroupOf (Ω[Q]), ?_, ?_⟩
  · exact om_isElemAbelian_of_map_injective (Ω[Q]).subtype Subtype.val_injective (by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hEΩ]
      exact hE)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΩ).toEquiv]
    exact hcard

end Derived

section Transport

open CFSG.Adapters.RankTwoModelTransports (glCongr statedProjCongr glCongr_statedScalars)

theorem bigElem_minus_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ} (hn : 5 ≤ n)
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    BigElem (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  let σ : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hZ2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hirr' : ∀ s : ZMod 2, s ^ 2 + σ b * s + σ c ≠ 0 := by
    intro s hs
    apply hirr (σ.symm s)
    apply σ.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  let e1 : StatedProj (StatedOmega (StatedQuadMinus n K b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus n (ZMod 2) (σ b) (σ c))) :=
    statedProjCongr (glCongr σ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
        (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp σ rfl rfl v))
      (glCongr_statedScalars σ)
  let e2 := (omStatedProjEquivOfCardTwo hZ2
    (StatedOmega (StatedQuadMinus n (ZMod 2) (σ b) (σ c)))).symm
  let e3 := CFSG.ComponentClassification.RankTwoClassical.statedOmegaEquivCommutator
    (quadMinus n (ZMod 2) (σ b) (σ c)) (coe_quadMinus n (ZMod 2) (σ b) (σ c))
  have hn1 : 1 ≤ n := by omega
  refine bigElem_of_mulEquiv (((e1.trans e2).trans e3).symm) ?_
  exact bigElem_derived (Q := quadMinus n (ZMod 2) (σ b) (σ c))
    (nondegenerate_polarBilin_quadMinus_of_finite n (ZMod 2) hirr')
    (finrank_quadMinus_space hn1) hn

theorem bigElem_plus_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (hn : 5 ≤ n) : BigElem (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  let σ : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hZ2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  let e1 : StatedProj (StatedOmega (StatedQuadPlus n K)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus n (ZMod 2))) :=
    statedProjCongr (glCongr σ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
        (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp σ))
      (glCongr_statedScalars σ)
  let e2 := (omStatedProjEquivOfCardTwo hZ2
    (StatedOmega (StatedQuadPlus n (ZMod 2)))).symm
  let e3 := CFSG.ComponentClassification.RankTwoClassical.statedOmegaEquivCommutator
    (quadPlus n (ZMod 2)) (coe_quadPlus n (ZMod 2))
  refine bigElem_of_mulEquiv (((e1.trans e2).trans e3).symm) ?_
  exact bigElem_derived (Q := quadPlus n (ZMod 2))
    (nondegenerate_polarBilin_quadPlus n (ZMod 2)) (finrank_quadPlus_space n) hn

theorem bigElem_matrixProj_minus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (hn : 5 ≤ n) (hn1 : 1 ≤ n) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    BigElem (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
  bigElem_of_mulEquiv (coordinateMinusWitnessEquiv K hn1 b c (MulEquiv.refl _))
    (bigElem_minus_two K hK hn b c hirr)

theorem bigElem_matrixProj_plus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    (hn : 5 ≤ n) : BigElem (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  bigElem_of_mulEquiv (coordinatePlusWitnessEquiv K (MulEquiv.refl _))
    (bigElem_plus_two K hK hn)

end Transport

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

end
