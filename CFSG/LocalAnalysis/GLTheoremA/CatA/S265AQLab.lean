module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FIdent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge lieOrderBridge_holds)

private theorem card_tyA (hLO : LieOrderBridge) {R : Type} [Group R] [Finite R]
    (h : catalogIs R tyA) :
    Nat.card R = 174182400 ∨ Nat.card R = 25015379558400 ∨ Nat.card R = 1451520 ∨
      Nat.card R = 47377612800 ∨ Nat.card R = 360 := by
  obtain ⟨i, hi, he⟩ := h
  rcases hi with hi | hi | hi | hi | hi
  · obtain ⟨q, hv, hq, he'⟩ := CatB.lieIndex_isD4two (⟨i, hi, he⟩ : catalogIs R S9.isD4two)
    refine Or.inl ((hLO ⟨_, hv⟩ R he').trans ?_)
    show orderD 4 q.card = _
    rw [hq]
    decide +kernel
  · obtain ⟨d, hv, hP, he'⟩ := CatB.exists_lieIndex (⟨i, hi, he⟩ : catalogIs R tyOm10m)
    cases d <;> try exact hP.elim
    rename_i r q
    rcases r with _ | _ | _ | _ | _ | _ | r <;> try exact hP.elim
    have hq : q.card = 2 := hP
    refine Or.inr (Or.inl ((hLO ⟨_, hv⟩ R he').trans ?_))
    show orderTwistedD 5 q.card = _
    rw [hq]
    decide +kernel
  · obtain ⟨q, hv, hq, he'⟩ := CatB.lieIndex_isSp6two (⟨i, hi, he⟩ : catalogIs R S9.isSp6two)
    refine Or.inr (Or.inr (Or.inl ((hLO ⟨_, hv⟩ R he').trans ?_)))
    show orderBC 3 q.card = _
    rw [hq]
    decide +kernel
  · obtain ⟨d, hv, hP, he'⟩ := CatB.exists_lieIndex (⟨i, hi, he⟩ : catalogIs R tySp8)
    cases d <;> try exact hP.elim
    rename_i r q
    rcases r with _ | _ | _ | _ | _ | r <;> try exact hP.elim
    have hq : q.card = 2 := hP
    refine Or.inr (Or.inr (Or.inr (Or.inl ((hLO ⟨_, hv⟩ R he').trans ?_))))
    show orderBC 4 q.card = _
    rw [hq]
    decide +kernel
  · cases i <;> try exact hi.elim
    rename_i n hn
    rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> try exact hi.elim
    obtain ⟨e⟩ := he
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    rw [Nat.card_congr e.toEquiv]
    show Nat.card (alternatingGroup (Fin 6)) = 360
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl

private theorem lieModel_of_marked_div_three {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hpn : 3 ∣ lab.n) {X : Type} [Group X]
    (hM : MarkedModel ⟨lab.tag, lab.rank, lab.n / 3⟩ X) :
    CFSG.Blueprint.LieModel X (markTag ⟨lab.tag, lab.rank, lab.n / 3⟩)
      (markRank ⟨lab.tag, lab.rank, lab.n / 3⟩) 2 (markDeg ⟨lab.tag, lab.rank, lab.n / 3⟩) := by
  refine lieModel_of_markedModel ?_ hM
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  dsimp only at hl hpn ⊢
  cases t <;> first | rfl | exact absurd hpn (by rw [hl.2]; norm_num)

section Main


theorem QUCfg.fieldOn_of_tyA {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (cfg : QUCfg 3 S B T x b) (hA : catalogIs (PSimple 3 (Ipart 3 S b)) tyA) :
    FieldOn 3 b S := by
  rcases cfg.prop with hF | ⟨-, hT, -⟩
  · exact hF
  exfalso
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hbp : b ^ 3 = 1 := cfg.elem.2 b cfg.hb
  obtain ⟨hb, E, hEC, hE, hna, hperf, h2, -⟩ := FR.coreSub_of_r2 hp hp2 FR.Res.smallDatum_holds
    (FR.Res.twF4Core_holds hp hp2) FR.Res.td4Core_holds cfg.comp cfg.chev hbp cfg.prop cfg.ipart
  have hEC' := hEC
  have hperf' := hperf
  rw [FR.fixSub_indAut hb] at hEC' hperf'
  obtain ⟨J₀, hJ₀, hIeq, -⟩ := FR.ipart_single hp hb hbp hE hEC' hperf' cfg.ipart
  obtain ⟨e⟩ := I91T.pSimple_component_equiv hp hb hbp hE hEC hna hperf hJ₀
  rw [← hIeq] at e
  have hcent := FP.centCard2_eq_twoPart_fixNum hb (FP.odd_card_center_pQuot hp hp2 S)
  rw [FP.fixNum_eq_card_fixSub] at hcent
  have hle : twoPart (Nat.card E) ≤ centCard2 3 S b := by
    rw [hcent]
    exact lemma102_twoPart_le_of_dvd Nat.card_pos.ne' (Subgroup.card_dvd_of_le hEC)
  have hge : centCard2 3 S b ≤ 2 * twoPart (Nat.card E) := by
    rw [hcent]
    exact h2
  have hdvd : Nat.card E ∣ Nat.card (PSimple 3 S) := Subgroup.card_subgroup_dvd_card E
  obtain ⟨q, hv, ⟨eS⟩⟩ := FR.Res.td4_index' hT
  have hqp : q.p = 2 := by
    by_contra hne
    exact FR.Res.td4_odd_false' hv hne eS cfg.chev
  have hcardS : Nat.card (PSimple 3 S) = orderTrialityD4 q.card :=
    lieOrderBridge_holds ⟨.trialityD4 q, hv⟩ (PSimple 3 S) ⟨eS⟩
  rw [TauCeti.PrimePower.card_def, hqp] at hcardS
  obtain ⟨O, hO, -, hOrd⟩ := CatDistinct.orderTrialityD4_two_pow q.exponent_pos
  have hsqrt : centCard2 3 S b = 2 ^ (q.exponent * 6) := by
    rw [cfg.g2 rfl hT, FP.card2_eq_twoPart_card_pSimple hp hp2, hcardS, hOrd,
      FQ.twoPart_two_pow_mul_odd hO,
      show (2 : ℕ) ^ (q.exponent * 12) = (2 ^ (q.exponent * 6)) ^ 2 by rw [← pow_mul]; ring_nf,
      Nat.sqrt_eq']
  have hexp : ∀ a O' : ℕ, Odd O' → Nat.card E = 2 ^ a * O' →
      a ≤ q.exponent * 6 ∧ q.exponent * 6 ≤ a + 1 := by
    intro a O' hO' hEa
    rw [hEa, FQ.twoPart_two_pow_mul_odd hO', hsqrt] at hle hge
    exact ⟨(Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle,
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (by rw [pow_succ']; exact hge)⟩
  have hf := q.exponent_pos
  have hNE : Nat.card (PSimple 3 (Ipart 3 S b)) = Nat.card E := Nat.card_congr e.toEquiv
  rcases card_tyA lieOrderBridge_holds hA with h | h | h | h | h <;> rw [hNE] at h
  · obtain ⟨h1, h1'⟩ := hexp 12 42525 (by decide) (h.trans (by norm_num))
    have hf2 : q.exponent = 2 := by omega
    rw [hcardS, hf2, h] at hdvd
    exact absurd hdvd (by decide +kernel)
  · obtain ⟨h1, h1'⟩ := hexp 20 23856525 (by decide) (h.trans (by norm_num))
    omega
  · obtain ⟨h1, h1'⟩ := hexp 9 2835 (by decide) (h.trans (by norm_num))
    omega
  · obtain ⟨h1, h1'⟩ := hexp 16 722925 (by decide) (h.trans (by norm_num))
    omega
  · obtain ⟨h1, h1'⟩ := hexp 3 45 (by decide) (h.trans (by norm_num))
    omega

theorem QUCfg.ident_d4two {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (cfg : QUCfg 3 S B T x b) (hJ : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isD4two) :
    FieldOn 3 b S ∧ StatedClassicalModel (PSimple 3 S) .POmegaPlus 4 2 3 := by
  obtain ⟨i, hi, he⟩ := hJ
  have hF := cfg.fieldOn_of_tyA ⟨i, Or.inl hi, he⟩
  refine ⟨hF, ?_⟩
  obtain ⟨q, hv, hq, ⟨eJ⟩⟩ := CatB.lieIndex_isD4two ⟨i, hi, he⟩
  obtain ⟨hq2, hq1⟩ := primePower_eq_of_card_eq Nat.prime_two one_pos (hq.trans (pow_one 2).symm)
  have hLJ := CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_D 4 q hv eJ)
  rw [hq2, hq1] at hLJ
  have hcardJ : Nat.card (PSimple 3 (Ipart 3 S b)) = 174182400 := by
    rw [lieOrderBridge_holds ⟨_, hv⟩ _ ⟨eJ⟩]
    show orderD 4 q.card = _
    rw [hq]
    decide +kernel
  obtain ⟨lab, hlab, hM, hpn, -, hMD⟩ := s265f_ident Nat.prime_three (by norm_num) hF
    (cfg.elem.2 b cfg.hb) cfg.ipart (by rw [hcardJ]; unfold S265FSmallOrd; omega)
  obtain ⟨e1, e2, e3⟩ := CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique (Or.inl rfl)
    hLJ (lieModel_of_marked_div_three hlab hpn hMD)
  obtain ⟨htD, hr3⟩ := tag_eq_D_of_markTag_eq_POmegaPlus e1
  obtain ⟨t, r, n⟩ := lab
  dsimp only at htD hr3 e2 e3 hpn
  subst htD
  simp only [markRank, markDeg, if_neg hr3] at e2 e3
  subst e2
  obtain rfl : n = 3 := by omega
  have h : CFSG.Blueprint.LieModel (PSimple 3 S) .POmegaPlus 4 2 3 := by
    simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
  exact h.statedClassicalModel (by decide)

theorem QUCfg.ident_sp6two {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (cfg : QUCfg 3 S B T x b) (hJ : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isSp6two) :
    FieldOn 3 b S ∧ StatedClassicalModel (PSimple 3 S) .PSp 3 2 3 := by
  obtain ⟨i, hi, he⟩ := hJ
  have hF := cfg.fieldOn_of_tyA ⟨i, Or.inr (Or.inr (Or.inl hi)), he⟩
  refine ⟨hF, ?_⟩
  obtain ⟨q, hv, hq, ⟨eJ⟩⟩ := CatB.lieIndex_isSp6two ⟨i, hi, he⟩
  obtain ⟨hq2, hq1⟩ := primePower_eq_of_card_eq Nat.prime_two one_pos (hq.trans (pow_one 2).symm)
  have hLJ : CFSG.Blueprint.LieModel (PSimple 3 (Ipart 3 S b)) .PSp 3 2 1 := by
    rcases CFSG.Models.lieModel_B 3 q hv eJ with h | h
    · have h' := CFSG.Models.LieModel.toBlueprint (by decide) h
      rwa [hq2, hq1] at h'
    · exact absurd hq2 h.1.2.2.2
  have hcardJ : Nat.card (PSimple 3 (Ipart 3 S b)) = 1451520 := by
    rw [lieOrderBridge_holds ⟨_, hv⟩ _ ⟨eJ⟩]
    show orderBC 3 q.card = _
    rw [hq]
    decide +kernel
  obtain ⟨lab, hlab, hM, hpn, -, hMD⟩ := s265f_ident Nat.prime_three (by norm_num) hF
    (cfg.elem.2 b cfg.hb) cfg.ipart (by rw [hcardJ]; unfold S265FSmallOrd; omega)
  obtain ⟨e1, e2, e3⟩ := CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hLJ
    (lieModel_of_marked_div_three hlab hpn hMD)
  have htBC := ClNonsplit.tag_of_markTag_PSp e1
  obtain ⟨t, r, n⟩ := lab
  dsimp only at htBC e2 e3 hpn
  rcases htBC with rfl | rfl
  all_goals
    simp only [markRank, markDeg] at e2 e3
    subst e2
    obtain rfl : n = 3 := by omega
    have h : CFSG.Blueprint.LieModel (PSimple 3 S) .PSp 3 2 3 := by
      simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
    exact h.statedClassicalModel (by decide)

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end
