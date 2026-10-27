module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8OmRank
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open QuadraticMap Module CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

local notation "Ω[" Q "]" =>
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆

section Derived

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_big_torus_plus_four (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 8) (hplus : IsPlusType Q) :
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
  have hPd : finrank (ZMod 2) (perpL Q l) = 8 - 2 * l.length := by
    rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hl.finrank_Wspan]
  have hle2 := hl.finrank_perpL_le hQ hno
  have hWle : finrank (ZMod 2) (Wspan l) ≤ finrank (ZMod 2) V := Submodule.finrank_le _
  rw [hl.finrank_Wspan, hdim] at hWle
  have hlen : l.length = 3 ∨ l.length = 4 := by omega
  have hlen4 : l.length = 4 := by
    rcases hlen with h3 | h4
    · exfalso
      have hperp2 : finrank (ZMod 2) (perpL Q l) = 2 := by rw [hPd, h3]
      have hV0plus : IsPlusType (Q.comp (perpL Q l).subtype) :=
        isPlusType_of_no_minusPair hperp2 hno
      have hcompl := hl.isCompl
      have hsup : Wspan l ⊔ perpL Q l = ⊤ := hcompl.sup_eq_top
      have hdisj : Disjoint (Wspan l) (perpL Q l) := hcompl.disjoint
      have horth : ∀ a ∈ Wspan l, ∀ b ∈ perpL Q l, polar Q a b = 0 := by
        intro a ha b hb
        have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hb) a ha
        rw [QuadraticMap.polarBilin_apply_apply] at h1
        exact h1
      have hndB : (QuadraticMap.polarBilin (Q.comp (perpL Q l).subtype)).Nondegenerate :=
        nondeg_comp_subtype (hl.perpL_nondeg hQ)
      have h := isPlusType_sup_iff hdisj horth (nondeg_Wspan hl) hndB (d₁ := 3) (d₂ := 1)
        (by norm_num) (by norm_num) (by rw [hl.finrank_Wspan, h3]) (by rw [hperp2])
      have hQtop : IsPlusType (Q.comp (Wspan l ⊔ perpL Q l).subtype) :=
        (isPlusType_congr (Q := Q.comp (Wspan l ⊔ perpL Q l).subtype) (Q' := Q)
          { toLinearEquiv := LinearEquiv.ofTop _ hsup, map_app' := fun m => rfl }).2 hplus
      have hA : ¬ IsPlusType (Q.comp (Wspan l).subtype) := by
        rw [isPlusType_Wspan_iff hl, h3]
        decide
      exact hA (h.1 hQtop |>.2 hV0plus |> fun hh => hh)
    · exact h4
  refine ⟨E, hEΩ, hE, ?_⟩
  rw [hEeq, card_torus hl, hlen4]

theorem bigElem_derived_plus_four (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 8) (hplus : IsPlusType Q) : BigElem ↥(Ω[Q]) := by
  obtain ⟨E, hEΩ, hE, hcard⟩ := exists_big_torus_plus_four hQ hdim hplus
  refine ⟨E.subgroupOf (Ω[Q]), ?_, ?_⟩
  · exact om_isElemAbelian_of_map_injective (Ω[Q]).subtype Subtype.val_injective (by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hEΩ]
      exact hE)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΩ).toEquiv]
    exact hcard

end Derived

section Transport

open CFSG.Adapters.RankTwoModelTransports (glCongr statedProjCongr glCongr_statedScalars)

theorem bigElem_plus_two_four (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    BigElem (StatedProj (StatedOmega (StatedQuadPlus 4 K))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  let σ : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hZ2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  let e1 : StatedProj (StatedOmega (StatedQuadPlus 4 K)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2))) :=
    statedProjCongr (glCongr σ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
        (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp σ))
      (glCongr_statedScalars σ)
  let e2 := (omStatedProjEquivOfCardTwo hZ2
    (StatedOmega (StatedQuadPlus 4 (ZMod 2)))).symm
  let e3 := CFSG.ComponentClassification.RankTwoClassical.statedOmegaEquivCommutator
    (quadPlus 4 (ZMod 2)) (coe_quadPlus 4 (ZMod 2))
  refine bigElem_of_mulEquiv (((e1.trans e2).trans e3).symm) ?_
  exact bigElem_derived_plus_four (Q := quadPlus 4 (ZMod 2))
    (nondegenerate_polarBilin_quadPlus 4 (ZMod 2)) (finrank_quadPlus_space 4)
    (isPlusType_quadPlus (ZMod 2) 4)

theorem bigElem_matrixProj_plus_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    BigElem (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
  bigElem_of_mulEquiv (coordinatePlusWitnessEquiv K (MulEquiv.refl _))
    (bigElem_plus_two_four K hK)

section Adjoint


theorem bigElem_adjoint_D4_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    BigElem (adjointGroup Tag.D4 K) := by
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup (F := K)
  exact bigElem_of_mulEquiv e (bigElem_plus_two_four K hK)

end Adjoint

end Transport

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

end
