module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem pairConfig_psp_four {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {x : StatedProj (StatedSp 2 F)} {K K' : Subgroup (StatedProj (StatedSp 2 F))}
    (hc : PairConfig _ x K K') :
    Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧ 5 ≤ Nat.card F := by
  classical
  have h2 := CatFactsSp4.two_ne_zero_of_odd_card hodd
  obtain ⟨g, hg⟩ := CatFactsSp4.exists_conj_of_orderOf_eq_two hodd hc.orderOf_x
  set φ : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F) := MulAut.conj g⁻¹ with hφ
  have hφx : φ x = g⁻¹ * x * g := by simp [hφ]
  have hC : (centralizer ({x} : Set _)).map φ.toMonoidHom = centralizer ({g⁻¹ * x * g} : Set _) :=
    by rw [map_centralizer_singleton_equiv, hφx]
  have hK1 : IsPComponent 2 ((K.map φ.toMonoidHom).subgroupOf (centralizer {g⁻¹ * x * g})) := by
    rw [← hC]
    exact (isPComponent_subgroupOf_map_iff φ hc.K_le).mp hc.isPComponent_K
  have hK2 : IsPComponent 2 ((K'.map φ.toMonoidHom).subgroupOf (centralizer {g⁻¹ * x * g})) := by
    rw [← hC]
    exact (isPComponent_subgroupOf_map_iff φ hc.K'_le).mp hc.isPComponent_K'
  have hle1 : K.map φ.toMonoidHom ≤ centralizer {g⁻¹ * x * g} := hC ▸ map_mono hc.K_le
  have hle2 : K'.map φ.toMonoidHom ≤ centralizer {g⁻¹ * x * g} := hC ▸ map_mono hc.K'_le
  have eK : K ≃* K.map φ.toMonoidHom := K.equivMapOfInjective _ φ.injective
  rcases hg with h | h
  · rw [h] at hK1 hle1
    obtain ⟨h'', h5⟩ := CatFactsSp4.pComponent_centralizer_u1 hodd hle1 hK1
    rcases h'' with h' | h'
    · exact ⟨⟨eK.trans ((MulEquiv.subgroupCongr h').trans (CatFactsSp4.E1Equiv h2).symm)⟩, h5⟩
    · exact ⟨⟨eK.trans ((MulEquiv.subgroupCongr h').trans (CatFactsSp4.E2Equiv h2).symm)⟩, h5⟩
  · exfalso
    rw [h] at hK1 hK2 hle1 hle2
    have h1 := (CatFactsSp4.pComponent_centralizer_u2 hodd hle1 hK1).1
    have h2' := (CatFactsSp4.pComponent_centralizer_u2 hodd hle2 hK2).1
    exact hc.ne (Subgroup.map_injective φ.injective (h1.trans h2'.symm))

@[expose] def slZStarEquiv {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) :
    Matrix.SpecialLinearGroup (Fin 2) F ⧸
        Open.fusionZStar (Matrix.SpecialLinearGroup (Fin 2) F) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  (GSThmB.oddBarCenterEquiv _).symm.trans
    (QuotientGroup.congr _ _ ((QuotientGroup.quotientMulEquivOfEq
      (CatFactsSp4.pPrimeCore_SL2 h2 h4)).trans QuotientGroup.quotientBot)
      (Subgroup.map_center_eq _))

theorem lieModel_projectiveSL_two {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (h5 : 5 ≤ p ^ f) :
    Blueprint.LieModel (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) .PSL 2 p f :=
  Or.inl ⟨by decide, SectionRank.statedClassicalModel_of_mulEquiv
    (projectiveSpecialLinearGroupEquivStatedProj 2 F)
    (OddSelector.statedClassicalModel_psl_two hp hf hF (by omega) (by omega))⟩

theorem Config.lieModel_J_of_psp {H : Type} [Group H] [Finite H] (c : Config H) {p f : ℕ}
    (hp2 : p ≠ 2) (hG : Blueprint.LieModel ↥(generalizedFitting H) .PSp 2 p f) :
    Blueprint.LieModel (c.J ⧸ pPrimeCore 2 c.J) .PSL 2 p f := by
  obtain ⟨hp, hf, F, _, _, hF, ⟨θ⟩⟩ := GH74.Generic.lieModel_psp_data hG
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h2 := CatFactsSp4.two_ne_zero_of_odd_card hodd
  obtain ⟨⟨eK₁⟩, h5⟩ := pairConfig_psp_four hodd (c.pairConfig θ)
  have eK : c.K ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (subgroupOfEquivOfLe c.K_le_G).symm.trans
      (((c.K.subgroupOf (generalizedFitting H)).equivMapOfInjective _ θ.injective).trans eK₁)
  obtain ⟨eJ⟩ := c.quotient_J_K
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    ((eJ.trans (zStarQuotientCongr eK)).trans (slZStarEquiv h2 (by omega))).symm
    (lieModel_projectiveSL_two hp hf hF (hF ▸ h5))

end CFSG.ComponentClassification.Sp4Rec
