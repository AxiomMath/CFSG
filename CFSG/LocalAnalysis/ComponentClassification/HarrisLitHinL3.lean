module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAut
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L3Main
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL3U3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LieType.HighestRoot.CentTrialityThree

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

variable {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]

theorem eq_of_l3u3 (hnab : ∃ a b : Y, a * b ≠ b * a) {ℓ f p m : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hY : Blueprint.LieModel Y .PSL 3 ℓ f ∨ Blueprint.LieModel Y .PSU 3 ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    p = ℓ ∧ m = f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun σ : MulAut Y => (σ : Y → Y)) fun a b h => MulEquiv.ext (congrFun h)
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have hF := CatLeaf.generalizedFitting_mulAut_eq_range hnab
  set W := (MulAut.conj : Y →* MulAut Y).range
  let eW : Y ≃* ↥(generalizedFitting (MulAut Y)) :=
    (MonoidHom.ofInjective (conj_injective_of_center hZ)).trans (MulEquiv.subgroupCongr hF.symm)
  have hWs : IsSimpleGroup ↥(generalizedFitting (MulAut Y)) := eW.symm.isSimpleGroup
  have hWC : centralizer (generalizedFitting (MulAut Y) : Set (MulAut Y)) = ⊥ := by
    rw [hF, eq_bot_iff]
    intro σ hσ
    rw [mem_bot]
    ext s
    have h := mem_centralizer_iff.mp hσ (MulAut.conj s) ⟨s, rfl⟩
    have h' : MulAut.conj (σ s) = MulAut.conj s := by
      rw [conj_apply_eq, ← h, mul_inv_cancel_right]
    exact conj_injective_of_center hZ h'
  have hWm : Blueprint.LieModel ↥(generalizedFitting (MulAut Y)) .PSL 3 ℓ f ∨
      Blueprint.LieModel ↥(generalizedFitting (MulAut Y)) .PSU 3 ℓ f :=
    hY.imp (LieType.CurtisTits.lieModel_of_mulEquiv eW) (LieType.CurtisTits.lieModel_of_mulEquiv eW)
  set L' := (GSThmB.layerIn (fixedPoints τ)).map (MulAut.conj : Y →* MulAut Y)
  have hcomp := isComponentOf_map_conj_layer hZ hL
  have hL'F : L' ≤ generalizedFitting (MulAut Y) := hF ▸ map_le_range _ _
  have hs := isSimpleGroup_pLayer hL
  let eL' : ↥(GSThmB.layerIn (fixedPoints τ)) ≃* ↥L' :=
    (GSThmB.layerIn (fixedPoints τ)).equivMapOfInjective _ (conj_injective_of_center hZ)
  have hL's : IsSimpleGroup ↥L' := ((layerInEquiv _).symm.trans eL').symm.isSimpleGroup
  have h2L' : 2 ∣ Nat.card ↥L' := by
    rw [← Nat.card_congr eL'.toEquiv]
    exact even_iff_two_dvd.mp (even_card_of_lieModel_psl2 hp2 hL)
  have hO : pPrimeCore 2 ↥L' = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥L') with h | h
    · exact h
    · exfalso
      have hc := pPrimeCore_coprime_card (p := 2) (G := ↥L')
      rw [h, card_top] at hc
      exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2L' hc
  have hLm : Blueprint.LieModel (↥L' ⧸ pPrimeCore 2 ↥L') .PSL 2 p m :=
    lieModel_psl2_of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans eL'.symm) hL
  have h5 : 5 ≤ p ^ m := by
    have := seven_le_of_sixteen_dvd hp hp2 hm h16
    omega
  exact GSThmB.Catalog7Std.l3EpsL2Input (MulAut Y) hWs hWC ℓ f hℓ hℓ2 hf hWm τ hτ L' hL'F hcomp.1
    (isPComponent_map_conj_layer hZ hp2 hL) p m hp hp2 hm h5 hLm

theorem not_mem_innAut_of_l3u3 (hnab : ∃ a b : Y, a * b ≠ b * a) {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h16 : 16 ∣ p ^ (2 * m) - 1)
    (hY : Blueprint.LieModel Y .PSL 3 p m ∨ Blueprint.LieModel Y .PSU 3 p m) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) : τ ∉ innAut Y := by
  intro hinn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, rfl, -, htL⟩ := exists_conj_of_mem_innAut hτ hinn hL
  have ht2 : orderOf t = 2 := by
    have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
    rw [← orderOf_injective _ (conj_injective_of_center hZ) t]
    exact hτ
  have hE : Blueprint.LieModel ↥(⊤ : Subgroup Y) .PSL 3 p m ∨
      Blueprint.LieModel ↥(⊤ : Subgroup Y) .PSU 3 p m :=
    hY.imp (LieType.CurtisTits.lieModel_of_mulEquiv Subgroup.topEquiv.symm)
      (LieType.CurtisTits.lieModel_of_mulEquiv Subgroup.topEquiv.symm)
  obtain ⟨S, hSle, hSsn, ⟨F, _, _, hFc, ⟨eS⟩⟩, htS⟩ :=
    EndB.l3u3InvolutionSL2Fact Y ⊤ p m hp hp2 hm hE t (mem_top t) ht2
  set C := fixedPoints (MulAut.conj t)
  have hTC : (⊤ : Subgroup Y) ⊓ centralizer ({t} : Set Y) = C := by
    rw [top_inf_eq, centralizer_eq_fixedPoints_conj]
  rw [hTC] at hSle hSsn
  have h4 : 4 ≤ Nat.card F := by
    have := seven_le_of_sixteen_dvd hp hp2 hm h16
    rw [Nat.card_eq_fintype_card, hFc]
    omega
  have hq : IsQuasisimple ↥(S.subgroupOf C) :=
    LocalCores.isQuasisimple_of_mulEquiv ((subgroupOfEquivOfLe hSle).trans eS).symm
      (LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4)
  have hSc : IsComponent (S.subgroupOf C) := ⟨hq, hSsn⟩
  have hSp : IsPComponent 2 (S.subgroupOf C) := by
    refine LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hSc
      fun hle => ?_
    have h2 : 2 ∣ Nat.card ↥(S.subgroupOf C) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hSle).toEquiv]
      have := orderOf_dvd_natCard (⟨t, htS⟩ : S)
      rwa [Subgroup.orderOf_mk, ht2] at this
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl
      (h2.trans (Subgroup.card_dvd_of_le hle)) (pPrimeCore_coprime_card (p := 2) (G := ↥C))
  have htC : t ∈ C := hSle htS
  have hle : S.subgroupOf C ≤ pLayer ↥C 2 := le_sSup hSp
  have hmem : (⟨t, htC⟩ : ↥C) ∈ pLayer ↥C 2 := hle (mem_subgroupOf.mpr htS)
  exact htL ⟨_, hmem, rfl⟩

theorem hinFor_l3u3_odd : HinFor fun Y _ => ∃ ℓ f : ℕ, ℓ ≠ 2 ∧
    (Assembly.LowTwoRank.StatedClassicalModel Y .PSL 3 ℓ f ∨
      Assembly.LowTwoRank.StatedClassicalModel Y .PSU 3 ℓ f) := by
  intro Y _ _ _ ⟨ℓ, f, hℓ2, hY⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  have hℓf : ℓ.Prime ∧ 1 ≤ f := by
    rcases hY with ⟨⟨h1, h2, -⟩, -⟩ | ⟨⟨h1, h2, -⟩, -⟩ <;> exact ⟨h1, h2⟩
  have hYm : Blueprint.LieModel Y .PSL 3 ℓ f ∨ Blueprint.LieModel Y .PSU 3 ℓ f :=
    hY.imp (fun h => Or.inl ⟨by simp [Blueprint.classicalTags], h⟩)
      (fun h => Or.inl ⟨by simp [Blueprint.classicalTags], h⟩)
  obtain ⟨rfl, rfl⟩ := eq_of_l3u3 hnab hℓf.1 hℓ2 hℓf.2 hYm hp hp2 hm h16 hτ hL
  have hout := not_mem_innAut_of_l3u3 hnab hp hp2 hm h16 hYm hτ hL
  rcases hYm with h | h
  · exact hinConcl_of_list hout (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact hinConcl_of_list hout (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

end CFSG.ComponentClassification.HarrisLit.Hin
