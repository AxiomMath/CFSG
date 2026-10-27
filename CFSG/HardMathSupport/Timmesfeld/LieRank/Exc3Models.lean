module

public import CFSG.Blueprint.Catalog
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ClassicalInvolution.Upgrade (statedClassicalModel_unique fieldIsoOfCard)

theorem statedClassicalModel_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h1 : t ∉ CFSG.Blueprint.chevalleyExceptionalTags) (h2 : t ∉ CFSG.Blueprint.reeTitsTags)
    (h3 : t ≠ .twistedB2) (h : CFSG.Blueprint.LieModel X t n p f) :
    StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by revert h1 h2 h3; cases t <;> decide)

theorem pRank_le_two_of_lieModel_PSL_two_three_two {X : Type} [Group X] [Finite X]
    (h : CFSG.Blueprint.LieModel X .PSL 2 3 2) : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    statedClassicalModel_of_lieModel (by decide) (by decide) (by decide) h
  have := Fintype.ofFinite K
  have hq : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  have hGL : Nat.card (GL (Fin 2) K) = 5760 := by
    rw [Matrix.card_GL_field, hq, Fin.prod_univ_two]
    norm_num
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  have hdvd : 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup X) ∣ 5760 := by
    rw [← hE, ← hGL]
    refine (Subgroup.card_subgroup_dvd_card E).trans ?_
    rw [Nat.card_congr e.toEquiv]
    exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)
  by_contra hlt
  have h27 : 3 ^ 3 ∣ 5760 := (Nat.pow_dvd_pow 3 (by omega)).trans hdvd
  norm_num at h27

@[expose] noncomputable def statedProjOmegaOpenEquiv (K : Type) [Field K] :
    StatedProj (StatedOmega (StatedQuadOdd 3 K)) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 K)) :=
  MulEquiv.refl _

theorem nonempty_mulEquiv_openOmega_of_lieModel {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .POmegaOdd 3 3 1) :
    Nonempty (X ≃* CFSG.Open.StatedProj
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadOdd 3 (ZMod 3)))) := by
  have hc := statedClassicalModel_of_lieModel (by decide) (by decide) (by decide) h
  have hY : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd 3 (ZMod 3))))
      .POmegaOdd 3 3 1 :=
    ⟨hc.1, ZMod 3, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num,
      ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e⟩ := statedClassicalModel_unique (by norm_num) hc hY
  exact ⟨e.trans (statedProjOmegaOpenEquiv (ZMod 3))⟩

section G2


theorem map_baseChangeGL_adjointGroup_eq_of_ringEquiv {τ : Tag} {K K' : Type} [Field K]
    [Field K'] (f : K ≃+* K') :
    (adjointGroup τ K).map (baseChangeGL (f : K →+* K')) = adjointGroup τ K' := by
  rw [map_baseChangeGL_adjointGroup, adjointGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨i, c, rfl | rfl⟩
    · exact ⟨i, _, Or.inl rfl⟩
    · exact ⟨i, _, Or.inr rfl⟩
  · rintro ⟨i, c, hg | hg⟩
    · refine ⟨i, f.symm c, Or.inl (Units.ext ?_)⟩
      rw [coe_xUnit, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
      exact hg
    · refine ⟨i, f.symm c, Or.inr (Units.ext ?_)⟩
      rw [coe_yUnit, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
      exact hg


theorem nonempty_mulEquiv_adjointGroup_G2_of_lieModel {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .G2 0 3 1) : Nonempty (X ≃* adjointGroup .G2 (ZMod 3)) := by
  rcases h with ⟨ht, -⟩ | ⟨-, -, -, K, _, _, hK, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · have f : K ≃+* ZMod 3 := fieldIsoOfCard (by rw [hK, Nat.card_zmod]; norm_num)
    have hinj := baseChangeGL_injective (τ := .G2) (f : K →+* ZMod 3)
    exact ⟨(e.trans ((QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans QuotientGroup.quotientBot)).trans
      (((adjointGroup .G2 K).equivMapOfInjective _ hinj).trans
        (MulEquiv.subgroupCongr (map_baseChangeGL_adjointGroup_eq_of_ringEquiv f)))⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end G2

theorem nonempty_mulEquiv_X₀_of_lieModel {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSU 4 3 1) :
    Nonempty (X ≃* CFSG.LieType.Multipliers.U43.X₀) := by
  have hc := statedClassicalModel_of_lieModel (by decide) (by decide) (by decide) h
  have hY : StatedClassicalModel CFSG.LieType.Multipliers.U43.X₀ .PSU 4 3 1 :=
    ⟨hc.1, CFSG.LieType.Multipliers.U43.F9, inferInstance, inferInstance,
      by rw [Nat.card_eq_fintype_card, CFSG.LieType.Multipliers.U43.F9.card_eq]; norm_num,
      ⟨MulEquiv.refl _⟩⟩
  exact statedClassicalModel_unique (by norm_num) hc hY

end CFSG.HardMathSupport.Timmesfeld.LieRank
