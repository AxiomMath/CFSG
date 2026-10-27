module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCLieMult
public import CFSG.LocalAnalysis.ComponentClassification.GS82PCLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.GS82PCLieOuter
public import CFSG.LocalAnalysis.ComponentClassification.GS82PCLieL34
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_typC_of_typLeafEven {Y : Type} [Group Y] (hO : pPrimeCore 2 Y = ⊥)
    (h : TypLeafEven Y) : ¬ TypC Y := by
  obtain ⟨-, hnodd, hnalt, hnL⟩ := h
  let e₁ : Y ⧸ pPrimeCore 2 Y ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  rintro (⟨t, n, p, f, hp, hp2, hadm, hm⟩ | ⟨n, -, -, -, ⟨g⟩⟩ | ⟨h1, h2⟩)
  · exact hnodd ⟨t, n, p, f, hp, hp2, hadm, Blueprint.LieModel.of_mulEquiv
      ((Sol78.coreQuotientCenterEquiv Y).symm.trans (Sol78.centerQuotCongr e₁)) hm⟩
  · exact (hnalt n).false ((Sol78.centerQuotCongr e₁).symm.trans g)
  · exact hnL ⟨Blueprint.LieModel.of_mulEquiv (Sol78.centerQuotCongr e₁) h1,
      fun hE => h2 (IsElementaryAbelian.of_mulEquiv (Subgroup.centerCongr e₁).symm hE)⟩

theorem false_of_inner_fixed_component_evenLie
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (heven : Blueprint.EvenLieType S) (hU : ¬ TBLit.UList S) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) {t : S} (ht : σ = MulAut.conj t) : False := by
  obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
  rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU'
  · have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
    exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
      ⟨hq, hPc.choose_spec.2.1⟩
  · exact hU hU'

theorem not_uList_of_lieModel (hO : LieOrderFormulasInput)
    {S : Type} [Group S] (hnodd : ¬ Blueprint.OddLieType S)
    (hnalt : ∀ n : ℕ, IsEmpty (S ≃* alternatingGroup (Fin n))) {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hm : Blueprint.LieModel S t n p f)
    (h20 : Nat.card S ≠ 20160) : ¬ TBLit.UList S := by
  rintro (h | ⟨k, -, -, he⟩ | h | he)
  · exact hnodd h
  · obtain ⟨e⟩ := he
    exact (hnalt k).false e
  · exact h20 (card_eq_of_lieModel_L34 hO h)
  · obtain ⟨e⟩ := he
    exact lieModel_card_ne_held hO hadm hm
      ((Nat.card_congr e.toEquiv).trans Sporadic.He.fam_he_order.1)

theorem typPumpLeaf_even_holds
    : TypPumpLeaf TypLeafEven := by
  intro Y _ _ hY hO hZ hleaf β hβ T hTF hT hTZ hTC
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO' : LieOrderFormulasInput := CatLeafProof.lieOrderFormulasInput
  obtain ⟨heven, hnodd, hnalt, hnL⟩ := hleaf
  have hTperf : Group.IsPerfect T := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hT
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTF).toMonoidHom)
      (subgroupOfEquivOfLe hTF).surjective
  have hidx : (pPrimeCore 2 T).index ≤ Nat.card T :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  have hTY : Nat.card T ≤ Nat.card Y := Subgroup.card_le_card_group T
  have hOY : (pPrimeCore 2 Y).index = Nat.card Y := by rw [hO, Subgroup.index_bot]
  rcases (hidx.trans hTY).lt_or_eq with hlt | heq
  swap
  · have hTtop : T = ⊤ := Subgroup.eq_top_of_card_eq T (le_antisymm hTY (heq ▸ hidx))
    exact not_typC_of_typLeafEven hO ⟨heven, hnodd, hnalt, hnL⟩
      (typC_of_coreEquiv (Sol78.coreQuotCongr ((MulEquiv.subgroupCongr hTtop).trans
        Subgroup.topEquiv)) hTC)
  let e₁ : Y ⧸ pPrimeCore 2 Y ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hYq' : IsQuasisimple (Y ⧸ pPrimeCore 2 Y) := LocalCores.isQuasisimple_of_mulEquiv e₁.symm hY
  obtain ⟨σ, -, hσ, hPF, hP, hPne, ⟨eP⟩⟩ :=
    GrSLit.exists_simple_fixed_component_image hYq' β hβ hTF hT (hOY ▸ hlt)
  set Yb := Y ⧸ pPrimeCore 2 Y with hYb
  set π₁ := QuotientGroup.mk' (pPrimeCore 2 Y) with hπ₁
  set Tb := T.map π₁ with hTb
  set P := Tb.map (QuotientGroup.mk' (center Yb)) with hPdef
  have hPC : ProperFixedComponent σ P := ⟨hσ, hPF, hP, hPne⟩
  have : IsSimpleGroup (Yb ⧸ center Yb) := hYq'.2.1
  have hna' : ∃ a b : Yb ⧸ center Yb, a * b ≠ b * a := hYq'.2.2
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => hσ y) hPC.ne_one
  let eS : Yb ⧸ center Yb ≃* Y ⧸ center Y := Sol78.centerQuotCongr e₁
  have hnodd' : ¬ Blueprint.OddLieType (Yb ⧸ center Yb) := fun ⟨t, n, p, f, hp, hp2, hadm, hm⟩ =>
    hnodd ⟨t, n, p, f, hp, hp2, hadm, Blueprint.LieModel.of_mulEquiv eS hm⟩
  have hnalt' : ∀ n : ℕ, IsEmpty (Yb ⧸ center Yb ≃* alternatingGroup (Fin n)) := fun n =>
    ⟨fun g => (hnalt n).false (eS.symm.trans g)⟩
  have hCT : CSimpleType (P ⧸ Open.fusionZStar P) := (cSimpleType_of_typC hTC).of_mulEquiv eP
  obtain ⟨ePF⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hPF)
  have hCT' : ¬ CSimpleType ((P.subgroupOf (fixedSubgroup σ)) ⧸
      Open.fusionZStar (P.subgroupOf (fixedSubgroup σ))) → False := fun h =>
    h (hCT.of_mulEquiv ePF.symm)
  obtain ⟨t, n, f, hadm, hm⟩ := heven
  have hm' : Blueprint.LieModel (Yb ⧸ center Yb) t n 2 f :=
    Blueprint.LieModel.of_mulEquiv eS.symm hm
  have heven' : Blueprint.EvenLieType (Yb ⧸ center Yb) := ⟨t, n, f, hadm, hm'⟩
  have inner : ¬ TBLit.UList (Yb ⧸ center Yb) → ∀ g : Yb ⧸ center Yb, σ = MulAut.conj g →
      False := fun hU g hg => false_of_inner_fixed_component_evenLie hna' heven' hU hPC hg
  have hcard : ∀ {N : ℕ}, lieOrderNumerator t n (2 ^ f) = N * lieOrderDivisor t n (2 ^ f) →
      0 < lieOrderDivisor t n (2 ^ f) → Nat.card (Yb ⧸ center Yb) = N := fun hN hd =>
    card_eq_of_lieModel hO' hadm hm' hN hd
  rcases even_center_lie_two_cases hY hO hZ hadm hm with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    obtain ⟨g⟩ := LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hm
    exact (hnalt 5).false g
  ·
    have h7 := LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _ hm
    exact hnodd ⟨.PSL, 2, 7, 1, by norm_num, by norm_num, h7.admissible, h7⟩
  ·
    obtain ⟨g⟩ := (SymmetricLocal.lie_model_linear_four_two_iff _).mp hm
    exact (hnalt 8).false g
  ·
    have h3 := GH74.Exceptional.lieModel_PSp_two_three_of_lieModel_PSU_four_two hm
    exact hnodd ⟨.PSp, 2, 3, 1, by norm_num, by norm_num, h3.admissible, h3⟩
  ·
    have hN : Nat.card (Yb ⧸ center Yb) = 1451520 := hcard (by decide) (by decide)
    have hU := not_uList_of_lieModel hO' hnodd' hnalt' hadm hm' (by rw [hN]; decide)
    obtain ⟨g, hg⟩ := psp_three_two_mem_range hm' σ
    exact inner hU g hg.symm
  ·
    have hN : Nat.card (Yb ⧸ center Yb) = 251596800 := hcard (by decide) (by decide)
    have hU := not_uList_of_lieModel hO' hnodd' hnalt' hadm hm' (by rw [hN]; decide)
    rcases exists_conj_or_not_mem_range σ with ⟨g, hg⟩ | hout
    · exact inner hU g hg
    have hL := lieModel_outer_fixed_G2_four hm' hσ2 hout hP
    have hLT : Blueprint.LieModel ((↥T ⧸ pPrimeCore 2 ↥T) ⧸ center (↥T ⧸ pPrimeCore 2 ↥T))
        .PSU 3 3 1 := Blueprint.LieModel.of_mulEquiv
      ((ePF.trans eP.symm).trans (Sol78.coreQuotientCenterEquiv T).symm) hL
    have : Group.IsPerfect (↥T ⧸ pPrimeCore 2 ↥T) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    exact hTZ (center_eq_bot_of_lieModel_PSU_three_three inferInstance hLT)
  ·
    have hN : Nat.card (Yb ⧸ center Yb) = 3311126603366400 := hcard (by decide) (by decide)
    have hU := not_uList_of_lieModel hO' hnodd' hnalt' hadm hm' (by rw [hN]; decide)
    rcases exists_conj_or_not_mem_range σ with ⟨g, hg⟩ | hout
    · exact inner hU g hg
    have hL := lieModel_outer_fixed_F4_two hm' hσ2 hout hP
    exact hCT' (not_cSimpleType_of_card_tits hO'
      (card_eq_of_lieModel hO' hL.admissible hL (by decide) (by decide)))
  ·
    have hN : Nat.card (Yb ⧸ center Yb) = 174182400 := hcard (by decide) (by decide)
    have hU := not_uList_of_lieModel hO' hnodd' hnalt' hadm hm' (by rw [hN]; decide)
    rcases exists_conj_or_not_mem_range σ with ⟨g, hg⟩ | hout
    · exact inner hU g hg
    exact hCT' (not_cSimpleType_of_card_sp62 hO' (card_outer_fixed_omegaPlus hm' hσ2 hout hP))
  ·
    have hN : Nat.card (Yb ⧸ center Yb) = 9196830720 := hcard (by decide) (by decide)
    have hU := not_uList_of_lieModel hO' hnodd' hnalt' hadm hm' (by rw [hN]; decide)
    rcases exists_conj_or_not_mem_range σ with ⟨g, hg⟩ | hout
    · exact inner hU g hg
    exact hCT' (not_cSimpleType_of_card_sp62 hO' (card_outer_fixed_psu hm' hσ2 hout hP))
  ·
    have hN : Nat.card (Yb ⧸ center Yb) = 29120 := hcard (by decide) (by decide)
    have hU := not_uList_of_lieModel hO' hnodd' hnalt' hadm hm' (by rw [hN]; decide)
    obtain ⟨g, hg⟩ := twistedB2_mem_range hm' hσ2
    exact inner hU g hg.symm
  ·
    have hN : Nat.card (Yb ⧸ center Yb) = 76532479683774853939200 := hcard (by decide) (by decide)
    have hU := not_uList_of_lieModel hO' hnodd' hnalt' hadm hm' (by rw [hN]; decide)
    rcases exists_conj_or_not_mem_range σ with ⟨g, hg⟩ | hout
    · exact inner hU g hg
    have hL := lieModel_outer_fixed_twistedE6 hadm hm' hσ2 hout hP
    exact hCT' (not_cSimpleType_of_card_f42 hO'
      (card_eq_of_lieModel hO' hL.admissible hL (by decide) (by decide)))
  ·
    have hE : IsElementaryAbelian 2 ↥(center Y) := by
      by_contra hE
      exact hnL ⟨hm, hE⟩
    have hEb : IsElementaryAbelian 2 ↥(center Yb) :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.centerCongr e₁).symm hE
    obtain ⟨-, -, -, -, ⟨eT⟩⟩ := exists_coreQuotient_fixed_component β hβ hTF hT
    have hTbperf : Group.IsPerfect ↥Tb := by
      let ρ : T →* Tb := (π₁.comp T.subtype).codRestrict Tb fun t => mem_map_of_mem π₁ t.2
      refine Group.IsPerfect.ofSurjective (f := ρ) ?_
      rintro ⟨y, hy⟩
      obtain ⟨t, ht, rfl⟩ := hy
      exact ⟨⟨t, ht⟩, rfl⟩
    exact false_of_l34_fixed_cover hYq' hm' hEb hTbperf (center_ne_bot_of_mulEquiv eT hTZ) hPC

end CFSG.ComponentClassification.GS82PumpInputs
