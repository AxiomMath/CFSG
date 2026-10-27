module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAut
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdInputs

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

theorem statedPSL2_of_lieModel {X : Type} [Group X] {p f : ℕ}
    (h : Blueprint.LieModel X .PSL 2 p f) :
    Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

section Layer

variable {Y : Type} [Group Y]

theorem layerIn_subgroupOf (C : Subgroup Y) :
    (GSThmB.layerIn C).subgroupOf C = pLayer ↥C 2 :=
  Subgroup.comap_map_eq_self_of_injective C.subtype_injective _

variable [Finite Y] {C : Subgroup Y} {p m : ℕ}

theorem layerIn_subgroupOf_normal (C : Subgroup Y) :
    ((GSThmB.layerIn C).subgroupOf C).Normal := by
  rw [layerIn_subgroupOf]
  exact pLayer_two_normal C

theorem isComponentOf_layerIn (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    Assembly.IsComponentOf (GSThmB.layerIn C) C := by
  refine (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    (map_subtype_le _)).mpr ?_
  change IsComponent ((GSThmB.layerIn C).subgroupOf C)
  rw [layerIn_subgroupOf]
  exact isComponent_pLayer hL

omit [Finite Y] in
theorem smallSource_layerIn (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h16 : 16 ∣ p ^ (2 * m) - 1) (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    RestrictedStd.SmallSource (GSThmB.layerIn C) := by
  have hs := isSimpleGroup_of_lieModel_psl2 hL
  have hZ : center ↥(GSThmB.layerIn C) = ⊥ :=
    (LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_of_lieModel_psl2 hL)).2
  refine Or.inl ⟨p, m, hp, hp2, hm, ?_, lieModel_psl2_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hL, ?_⟩
  · have := seven_le_of_sixteen_dvd hp hp2 hm h16
    omega
  · rw [hZ, card_bot]
    exact odd_one

end Layer

section Aut

variable {Y : Type} [Group Y] [Finite Y]

theorem finite_mulAut : Finite (MulAut Y) :=
  Finite.of_injective (fun σ : MulAut Y => (σ : Y → Y)) fun _ _ h => MulEquiv.ext (congrFun h)

variable [IsSimpleGroup Y]

theorem autSocle (hnab : ∃ a b : Y, a * b ≠ b * a) :
    ∃ _eW : Y ≃* ↥(generalizedFitting (MulAut Y)),
      (generalizedFitting (MulAut Y)).Normal ∧ IsSimpleGroup ↥(generalizedFitting (MulAut Y)) ∧
      (∃ x y : ↥(generalizedFitting (MulAut Y)), x * y ≠ y * x) ∧
      centralizer (generalizedFitting (MulAut Y) : Set (MulAut Y)) = ⊥ ∧
      ∀ τ : MulAut Y, (GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y) ≤
        generalizedFitting (MulAut Y) := by
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have hF := CatLeaf.generalizedFitting_mulAut_eq_range hnab
  let eW : Y ≃* ↥(generalizedFitting (MulAut Y)) :=
    (MonoidHom.ofInjective (conj_injective_of_center hZ)).trans (MulEquiv.subgroupCongr hF.symm)
  refine ⟨eW, ?_, eW.symm.isSimpleGroup, ?_, ?_, fun τ => hF ▸ map_le_range _ _⟩
  · rw [hF]
    exact OuterAutomorphisms.inner_normal Y
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eW a, eW b, fun h => hab (eW.injective (by rw [map_mul, map_mul, h]))⟩
  · rw [hF, eq_bot_iff]
    intro σ hσ
    rw [mem_bot]
    ext s
    have h := mem_centralizer_iff.mp hσ (MulAut.conj s) ⟨s, rfl⟩
    have h' : MulAut.conj (σ s) = MulAut.conj s := by
      rw [conj_apply_eq, ← h, mul_inv_cancel_right]
    exact conj_injective_of_center hZ h'

end Aut

section Image

variable {Y : Type} [Group Y] {p m : ℕ}

noncomputable def layerMapEquiv (hZ : center Y = ⊥) (C : Subgroup Y) :
    ↥(GSThmB.layerIn C) ≃* ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)) :=
  (GSThmB.layerIn C).equivMapOfInjective _ (conj_injective_of_center hZ)

variable {C : Subgroup Y}

theorem center_layerMap_eq_bot (hZ : center Y = ⊥)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    center ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)) = ⊥ := by
  have hs := isSimpleGroup_of_lieModel_psl2 hL
  have : IsSimpleGroup ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)) :=
    (layerMapEquiv hZ C).symm.isSimpleGroup
  obtain ⟨u, v, huv⟩ := nonabelian_of_lieModel_psl2 hL
  refine CatLeaf.center_eq_bot_of_simple ⟨layerMapEquiv hZ C u, layerMapEquiv hZ C v, fun h => ?_⟩
  exact huv ((layerMapEquiv hZ C).injective (by rw [map_mul, map_mul, h]))

theorem lieModel_layerMap (hZ : center Y = ⊥)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    Blueprint.LieModel (↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)) ⧸
      center ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y))) .PSL 2 p m :=
  lieModel_psl2_of_mulEquiv (((QuotientGroup.quotientMulEquivOfEq
    (center_layerMap_eq_bot hZ hL)).trans QuotientGroup.quotientBot).trans
      (layerMapEquiv hZ C).symm) hL

theorem statedSrc_layerMap (hZ : center Y = ⊥)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    Assembly.LowTwoRank.StatedClassicalModel
      (↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)) ⧸
        center ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y))) .PSL 2 p m :=
  statedPSL2_of_lieModel (lieModel_layerMap hZ hL)

theorem smallSource_layerMap (hZ : center Y = ⊥) (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h16 : 16 ∣ p ^ (2 * m) - 1) (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    RestrictedStd.SmallSource ((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)) := by
  refine Or.inl ⟨p, m, hp, hp2, hm, ?_, lieModel_layerMap hZ hL, ?_⟩
  · have := seven_le_of_sixteen_dvd hp hp2 hm h16
    omega
  · rw [center_layerMap_eq_bot hZ hL, card_bot]
    exact odd_one

theorem pPrimeCore_layerMap_eq_bot [Finite Y] (hZ : center Y = ⊥) (hp2 : p ≠ 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    pPrimeCore 2 ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)) = ⊥ := by
  have := finite_mulAut (Y := Y)
  have hs := isSimpleGroup_of_lieModel_psl2 hL
  have : IsSimpleGroup ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)) :=
    (layerMapEquiv hZ C).symm.isSimpleGroup
  have h2 : 2 ∣ Nat.card ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)) := by
    rw [← Nat.card_congr (layerMapEquiv hZ C).toEquiv]
    exact even_iff_two_dvd.mp (even_card_of_lieModel_psl2 hp2 hL)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (pPrimeCore 2 ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y))) with h | h
  · exact h
  · exfalso
    have hc := pPrimeCore_coprime_card (p := 2)
      (G := ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)))
    rw [h, card_top] at hc
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2 hc

theorem lieModel_pcore_layerMap [Finite Y] (hZ : center Y = ⊥) (hp2 : p ≠ 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) :
    Blueprint.LieModel (↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y)) ⧸
      pPrimeCore 2 ↥((GSThmB.layerIn C).map (MulAut.conj : Y →* MulAut Y))) .PSL 2 p m :=
  lieModel_psl2_of_mulEquiv (((QuotientGroup.quotientMulEquivOfEq
    (pPrimeCore_layerMap_eq_bot hZ hp2 hL)).trans QuotientGroup.quotientBot).trans
      (layerMapEquiv hZ C).symm) hL

end Image

end CFSG.ComponentClassification.HarrisLit.Hin
