module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1Small
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTyped
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndSetting
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1Defs

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem lieModel_psl_two_seven_of_dvd_1008 (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {τ : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) (hY : Blueprint.LieModel Y τ n p f)
    (hdvd : Nat.card Y ∣ 1008) (hlt : Nat.card Y < 1008) :
    τ = .PSL ∧ n = 2 ∧ p = 7 ∧ f = 1 := by
  have h := allowed_of_oddLieDvdCheck hO (l := [(2, 4), (3, 2), (7, 1)])
    (ok := fun τ n p f => τ == .PSL && n == 2 && p == 7 && f == 1) (by norm_num)
    (by simp only [List.forall_mem_cons]; norm_num) (by decide) (by decide +kernel) hp2 hY hdvd
    hlt
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem card_quot_lt_of_properFixedComponent {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P) :
    Nat.card (P ⧸ Open.fusionZStar P) < Nat.card S := by
  have hP : Nat.card P < Nat.card S := by
    by_contra hc
    exact h.2.2.2 (Subgroup.eq_top_of_le_card _ (not_lt.mp hc))
  exact lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hP

theorem inChev2_of_isAltType_of_oddLie
    (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    (hA : IsAltType Y) {τ : StatedLieTag} {n r f : ℕ} (hr2 : r ≠ 2)
    (hY : Blueprint.LieModel Y τ n r f) : GH74.GLS.InChev2 Y := by
  obtain ⟨Ω, _, _, hΩ, ⟨e⟩⟩ := hA
  have hadm := Blueprint.LieModel.admissible hY
  set m := Fintype.card Ω with hm
  let e' : Y ≃* alternatingGroup (Fin m) := e.trans (Fintype.equivFin Ω).altCongrHom
  rcases (show m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ 9 ≤ m by omega) with h5 | h6 | h7 | h8 | h9
  · rw [h5] at e'
    exact Or.inl ⟨.PSL, 2, 2, ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩,
      StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five e'⟩
  · rw [h6] at e'
    exact Or.inr (Or.inl ⟨e'⟩)
  · rw [h7] at e'
    exact (CatFC.not_lieModel_of_alt7 hO hadm hY ⟨e'⟩).elim
  · rw [h8] at e'
    exact (lieModel_odd_card_ne_L34 hO hr2 hadm hY
      (by rw [OddStandard.AltStdSec.card_eq_of_equiv_alt (by norm_num) e']; decide)).elim
  · exact (OddStandard.AltStdSec.false_of_lieModel_alt hO h9 e' hadm hY).elim

theorem false_of_alt_six (hO : LieOrderFormulasInput) {S : Type}
    [Group S] [Finite S] (θ : S ≃* alternatingGroup (Fin 6)) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) {τ : StatedLieTag} {n r f : ℕ} (hr2 : r ≠ 2)
    (hY : Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hY2 : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  have hS : Nat.card S = 360 := by
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]; decide
  have hdvd := card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
  have hlt := card_quot_lt_of_properFixedComponent h
  rw [hS] at hdvd hlt
  obtain ⟨rfl, rfl, rfl, rfl⟩ := lieModel_psl_two_five_of_dvd_360 hO hr2 hY hdvd hlt
  exact hY2 (inChev2_of_lieModel_psl_two_five hY)

theorem false_of_psu_three_three (hO : LieOrderFormulasInput)
    {S : Type} [Group S] [Finite S] (hU : Blueprint.LieModel S .PSU 3 3 1) {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P) {τ : StatedLieTag} {n r f : ℕ} (hr2 : r ≠ 2)
    (hY : Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hY2 : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  have hS : Nat.card S = 6048 := by
    obtain ⟨-, hord, -⟩ := hO S .PSU 3 3 1 (Blueprint.LieModel.admissible hU) hU
    simp only [lieOrderNumerator, lieOrderDivisor] at hord
    norm_num [Finset.prod_Icc_succ_top] at hord
    omega
  have hdvd := card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
  have hlt := card_quot_lt_of_properFixedComponent h
  rw [hS] at hdvd hlt
  obtain ⟨rfl, rfl, rfl, rfl⟩ := lieModel_psl_two_seven_of_dvd_6048 hO hr2 hY hdvd hlt
  exact hY2 (inChev2_of_lieModel_psl_two_seven hY)

theorem false_of_alternating
    (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] {m : ℕ} (hm : 5 ≤ m)
    (θ : S ≃* alternatingGroup (Fin m)) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) {τ : StatedLieTag} {n r f : ℕ} (hr2 : r ≠ 2)
    (hY : Blueprint.LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hY2 : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  by_cases hm6 : m = 6
  · subst hm6
    exact false_of_alt_six hO θ h hr2 hY hY2
  obtain ⟨h', ⟨eP⟩⟩ := h.map θ
  have hA := (isAltType_of_properFixedComponent_alternating hm hm6 h').of_mulEquiv eP
  exact hY2 (inChev2_of_isAltType_of_oddLie hO hA hr2 hY)

theorem chev_of_oddLieType
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hT : CatFC.EvenOuterTypedInput) (hC : OddLieCharUnique) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (ho : OddLieType S) {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P) {r : ℕ} (hr2 : r ≠ 2)
    (hY : HarrisLit.IsSimpleChevalleyOver r (P ⧸ Open.fusionZStar P))
    (hY2 : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) :
    HarrisLit.IsSimpleChevalleyOver r S ∧ ¬ GH74.GLS.InChev2 S := by
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hq : IsQuasisimple (P.subgroupOf (fixedSubgroup σ)) :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna ho σ hσσ hσ1 _ h.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  obtain ⟨τ0, n0, f0, hY0⟩ := hY
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := ho
  have hpr : p = r := by
    rcases hGLS S t n p f hp hp2 hadm hm σ hσ2 _ hcomp with ⟨τ', n', f', -, hm'⟩ |
        ⟨-, -, -, h8⟩
    · exact hC _ τ' n' p f' τ0 n0 r f0 hp2 hr2 (Blueprint.LieModel.of_mulEquiv eZ.symm hm') hY0
    · exfalso
      have h504 : Nat.card (P.subgroupOf (fixedSubgroup σ)) = 504 := by
        obtain ⟨-, hord, -⟩ := hO _ .PSL 2 2 3 (Blueprint.LieModel.admissible h8) h8
        simp only [lieOrderNumerator, lieOrderDivisor] at hord
        norm_num [Finset.Icc_self] at hord
        omega
      have hle := Nat.card_le_card_of_surjective _
        (QuotientGroup.mk'_surjective (center (P.subgroupOf (fixedSubgroup σ))))
      have hdvd : Nat.card (P ⧸ Open.fusionZStar P) ∣ 1008 := by
        rw [Nat.card_congr eZ.toEquiv]
        exact (Subgroup.card_quotient_dvd_card _).trans (by rw [h504]; norm_num)
      have hlt : Nat.card (P ⧸ Open.fusionZStar P) < 1008 := by
        rw [Nat.card_congr eZ.toEquiv]
        omega
      obtain ⟨rfl, rfl, rfl, rfl⟩ := lieModel_psl_two_seven_of_dvd_1008 hO hr2 hY0 hdvd hlt
      exact hY2 (inChev2_of_lieModel_psl_two_seven hY0)
  subst hpr
  refine ⟨⟨t, n, f, hm⟩, ?_⟩
  rintro (heven | ⟨⟨eA⟩⟩ | hU)
  · rcases exists_conj_or_not_mem_range σ with ⟨t0, ht0⟩ | hout
    ·
      obtain ⟨ht2, hPt, hPc, -⟩ := h.inner hna ht0
      have hqP : IsQuasisimple P :=
        HarrisLit.HarrisEnd.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe h.2.1) hq
      have hqt : IsQuasisimple (P.subgroupOf (centralizer ({t0} : Set S))) :=
        HarrisLit.HarrisEnd.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hPt).symm hqP
      exact involutionCentralizersComponentFree_of_evenLieType heven t0 ht2 _
        ⟨hqt, hPc.choose_spec.2.1⟩
    ·
      obtain ⟨τ2, n2, f2, hadm2, hm2⟩ := heven
      obtain ⟨eL⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1)
      rcases hT S τ2 n2 f2 hadm2 hm2 σ hσ2 hout _ h.2.2.1 with ⟨τ', n', f', hadm', hm', -⟩ |
          ⟨⟨eA⟩⟩ | hU
      · exact hY2 (Or.inl ⟨τ', n', f', hadm', Blueprint.LieModel.of_mulEquiv eL hm'⟩)
      · exact hY2 (Or.inr (Or.inl ⟨eL.symm.trans eA⟩))
      · exact hY2 (Or.inr (Or.inr (Blueprint.LieModel.of_mulEquiv eL hU)))
  · exact false_of_alt_six hO eA h hr2 hY0 hY2
  · exact false_of_psu_three_three hO hU h hr2 hY0 hY2

theorem chevOddPumpLeaf_of_clauses
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hT : CatFC.EvenOuterTypedInput) (hC : OddLieCharUnique)
    (hspor : ChevOddSporadicClause) : ChevOddPumpLeaf := by
  intro S _ _ hs hna hcat σ P h r hr hr2 hY hY2
  have : IsSimpleGroup S := hs
  have hodd : OddLieType S → HarrisLit.IsSimpleChevalleyOver r S ∧ ¬ GH74.GLS.InChev2 S :=
    fun ho => chev_of_oddLieType hGLS hO hT hC hna ho h hr2 hY hY2
  obtain ⟨τ0, n0, f0, hY0⟩ := hY
  have halt : ∀ m : ℕ, 5 ≤ m → Nonempty (S ≃* alternatingGroup (Fin m)) → False :=
    fun m hm ⟨θ⟩ => false_of_alternating hO hm θ h hr2 hY0 hY2
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨m, hm, hθ⟩ | ho | heven | hsp
  · exact (halt m hm hθ).elim
  · exact Or.inl (hodd ho)
  ·
    have hσ1 := h.ne_one
    have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
      rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
    rcases exists_conj_or_not_mem_range σ with ⟨t0, ht0⟩ | hout
    · obtain ⟨ht2, hPt, hPc, -⟩ := h.inner hna ht0
      rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
      · exfalso
        have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
        exact involutionCentralizersComponentFree_of_evenLieType heven t0 ht2 _
          ⟨hq, hPc.choose_spec.2.1⟩
      rcases hU with ho | ⟨m, -, hm7, hθ⟩ | hL | hH
      · exact Or.inl (hodd ho)
      · exact (halt m (by omega) hθ).elim
      ·
        exfalso
        obtain ⟨-, h64, -⟩ :=
          PSL3Four.excludes_alternating_models_stated.{0} S
            (statedClassicalModel_of_lieModel_psl hL)
        have hdvd : Nat.card (P ⧸ Open.fusionZStar P) ∣ 2 ^ 6 :=
          (Subgroup.card_quotient_dvd_card _).trans
            ((Subgroup.card_dvd_of_le hPt).trans (by rw [h64 t0 ht2]; norm_num))
        have hadm0 := Blueprint.LieModel.admissible hY0
        obtain ⟨-, -, hfac⟩ := hO _ τ0 n0 r f0 hadm0 hY0
        have hrd : r ∣ Nat.card (P ⧸ Open.fusionZStar P) :=
          Nat.dvd_of_factorization_pos (by
            rw [hfac]
            exact Nat.mul_ne_zero (by have := lieSylowExponent_pos hadm0; omega)
              (by have := hadm0.2.1; omega))
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
          (hr.dvd_of_dvd_pow (hrd.trans hdvd)))
      · exact Or.inr (hspor S hs hna ⟨.He, hH⟩ σ P h r hr hr2 ⟨τ0, n0, f0, hY0⟩ hY2)
    · exfalso
      obtain ⟨τ2, n2, f2, hadm2, hm2⟩ := heven
      obtain ⟨eL⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1)
      rcases hT S τ2 n2 f2 hadm2 hm2 σ hσ2 hout _ h.2.2.1 with ⟨τ', n', f', hadm', hm', -⟩ |
          ⟨⟨eA⟩⟩ | hU
      · exact hY2 (Or.inl ⟨τ', n', f', hadm', Blueprint.LieModel.of_mulEquiv eL hm'⟩)
      · exact hY2 (Or.inr (Or.inl ⟨eL.symm.trans eA⟩))
      · exact hY2 (Or.inr (Or.inr (Blueprint.LieModel.of_mulEquiv eL hU)))
  · exact Or.inr (hspor S hs hna hsp σ P h r hr hr2 ⟨τ0, n0, f0, hY0⟩ hY2)

end CFSG.ComponentClassification.GS82PumpInputs
