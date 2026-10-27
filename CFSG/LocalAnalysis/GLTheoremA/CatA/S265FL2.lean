module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FIdent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOrd
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
public import CFSG.RankThree.PartOne.K133.KillL2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.Index
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019A
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.S11.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint TauCeti
open scoped commutatorElement

@[expose] def tyL28 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A 1 q => q.card = 8 | _ => False

@[expose] def tyU38 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 2 q => q.card = 8 | _ => False

theorem tyD_split {S : Type} [Group S] (h : catalogIs S tyD) :
    catalogIs S tyL28 ∨ catalogIs S tyU38 := by
  obtain ⟨i, hi, he⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A r q =>
      left
      rcases r with _ | _ | r
      · exact hi.elim
      · exact ⟨.lie ⟨.A 1 q, hv⟩, hi, he⟩
      · exact hi.elim
    | twistedA r q =>
      right
      rcases r with _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      · exact ⟨.lie ⟨.twistedA 2 q, hv⟩, hi, he⟩
      · exact hi.elim
    | _ => exact hi.elim

private theorem s265f_primePower_eq {q : TauCeti.PrimePower} {r s : ℕ} (hr : r.Prime) (hs : 0 < s)
    (h : q.card = r ^ s) : q.p = r ∧ q.exponent = s := by
  rw [TauCeti.PrimePower.card_def] at h
  obtain ⟨m, hm⟩ : ∃ m, q.exponent = m + 1 := ⟨q.exponent - 1, by have := q.exponent_pos; omega⟩
  obtain ⟨k, hk⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [hm, hk] at h
  obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj q.prime_p hr h
  exact ⟨h1, by omega⟩

private theorem s265f_l28_model {R : Type} [Group R] (h : catalogIs R tyL28) :
    CFSG.Blueprint.LieModel R .PSL 2 2 3 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A r q =>
      rcases r with _ | _ | r
      · exact hi.elim
      · have hq : q.card = 8 := hi
        have hmodel := CFSG.HardMathSupport.Malle.E27Lie.statedClassicalModel_typeA' hv e
        obtain ⟨h1, h2⟩ := s265f_primePower_eq Nat.prime_two (s := 3) (by norm_num)
          (hq.trans (by norm_num))
        rw [h1, h2] at hmodel
        exact Or.inl ⟨by decide, hmodel⟩
      · exact hi.elim
    | _ => exact hi.elim

private theorem s265f_card_l28 {R : Type} [Group R] (h : catalogIs R tyL28) : Nat.card R = 504 := by
  have hL := s265f_l28_model h
  rw [CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hL,
    CFSG.RankThree.PartOne.S12K.ordA_one_eq (by norm_num : 1 ≤ 3)]
  norm_num

private theorem s265f_psl2_aut_card_le {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [NeZero (p : K)] {A : Subgroup (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))}
    (hA : IsElemAbelian p A) : Nat.card A ≤ p ^ 2 := by
  have hA' : CFSG.IsElementaryAbelian p A := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA
  obtain ⟨E₀, hE₀E, hE₀in, hE₀card⟩ :=
    CFSG.RankThree.PartOne.K133.exists_inner_core_psl2 hp hp2 A hA'
  have hE₀el : CFSG.IsElementaryAbelian p E₀ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₀).2 (isElemAbelian_mono hA hE₀E)
  obtain ⟨A', hA'el, hA'c⟩ := CFSG.RankThree.PartOne.K133.exists_elemAb_card_eq_of_le_inner
    (CFSG.GorensteinWalter.psl2_center_eq_bot K) hE₀el hE₀in
  have hle := CFSG.RankThree.PartOne.K133.psl2_elemAb_card_le hp hp2 A' hA'el
  rw [hA'c] at hle
  calc Nat.card A ≤ p * Nat.card E₀ := hE₀card
    _ ≤ p * p := Nat.mul_le_mul_left _ hle
    _ = p ^ 2 := (sq p).symm

section Main


variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem s265f_td4_false_l28 {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg 3 S B T x b)
    (hT : IsTD4 3 S) (hJ : catalogIs (PSimple 3 (Ipart 3 S b)) tyL28) : False := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hbp : b ^ 3 = 1 := cfg.elem.2 b cfg.hb
  have hcent : centCard2 3 S b ≤ 2 * card2 3 (Ipart 3 S b) :=
    FR.i91CentIAt_of_residuals (G := Ω) hp hp2 FR.Res.smallDatum_holds (FR.Res.twF4Core_holds hp hp2)
      FR.Res.td4Core_holds ⊤ S b cfg.comp cfg.chev hbp cfg.prop cfg.ipart
  have h504 : Nat.card (PSimple 3 (Ipart 3 S b)) = 504 := s265f_card_l28 hJ
  have hcard2J : card2 3 (Ipart 3 S b) = 8 := by
    rw [FP.card2_eq_twoPart_card_pSimple hp hp2, h504]
    have : (504 : ℕ) = 2 ^ 3 * 63 := by norm_num
    rw [this, FQ.twoPart_two_pow_mul_odd (by decide : Odd 63)]
    norm_num
  have hg2 := cfg.g2 rfl hT
  obtain ⟨q, hv, ⟨e⟩⟩ := FR.Res.td4_index' hT
  have hqp : q.p = 2 := by
    by_contra hne
    exact FR.Res.td4_odd_false' hv hne e cfg.chev
  have hcardS : Nat.card (PSimple 3 S) = orderTrialityD4 q.card :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.trialityD4 q, hv⟩ (PSimple 3 S) ⟨e⟩
  have hqcard : q.card = 2 ^ q.exponent := by
    rw [TauCeti.PrimePower.card_def, hqp]
  obtain ⟨O, hO, -, hOrd⟩ := CatDistinct.orderTrialityD4_two_pow q.exponent_pos
  have hcard2S : card2 3 S = 2 ^ (q.exponent * 12) := by
    rw [FP.card2_eq_twoPart_card_pSimple hp hp2, hcardS, hqcard, hOrd,
      FQ.twoPart_two_pow_mul_odd hO]
  have hsqrt : Nat.sqrt (card2 3 S) = 2 ^ (q.exponent * 6) := by
    rw [hcard2S]
    have : (2 : ℕ) ^ (q.exponent * 12) = (2 ^ (q.exponent * 6)) ^ 2 := by
      rw [← pow_mul]
      ring_nf
    rw [this, Nat.sqrt_eq']
  have h64 : (2 : ℕ) ^ 6 ≤ 2 ^ (q.exponent * 6) :=
    Nat.pow_le_pow_right (by norm_num) (by have := q.exponent_pos; nlinarith)
  rw [hg2, hsqrt, hcard2J] at hcent
  norm_num at h64
  omega

private theorem s265f_not_der_aux {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hpn : p ∣ lab.n) : lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der := by
  obtain ⟨tg, r, nn⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at hl hpn
  have key : ∀ (hnn : nn = 1), False := fun hnn => by
    rw [hnn] at hpn
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpn)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> dsimp only at h <;> subst h <;> exact key hl.2

private theorem s265f_tag_A1 {lab : LargeEvenLabel} {R : Type} [Group R] (hL : CFSG.Blueprint.LieModel R .PSL 2 2 3)
    (hM : MarkedModel lab R) (hder : lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der) :
    lab.tag = .A ∧ lab.rank = 1 := by
  obtain ⟨tg, r, nn⟩ := lab
  dsimp only at hder ⊢
  have hchar : markChar ⟨tg, r, nn⟩ = 2 := by
    cases tg <;> simp_all [markChar]
  have hM' : CFSG.Blueprint.LieModel R (markTag ⟨tg, r, nn⟩) (markRank ⟨tg, r, nn⟩) 2
      (markDeg ⟨tg, r, nn⟩) := by
    unfold MarkedModel at hM
    rwa [hchar] at hM
  obtain ⟨e1, e2, e3⟩ := CFSG.SeitzReduction.RankOne.sl2EvenTypeDet R 3 _ _ _ hL hM'.admissible hM'
  cases tg
  · simp only [markTag, markRank, markDeg] at e1 e2 e3
    exact ⟨rfl, by omega⟩
  all_goals first
    | exact absurd rfl hder.1
    | exact absurd rfl hder.2.1
    | exact absurd rfl hder.2.2
    | (exfalso; simp only [markTag, markRank, markDeg] at e1 e2 e3; first | (cases e1) | omega)
    | (exfalso; simp only [markTag, markRank, markDeg] at e1 e2 e3; split_ifs at e1 e2 e3 <;> first | omega | (cases e1))

theorem s265f_false_of_l28 {p : ℕ} {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg p S B T x b)
    (hp3 : p = 3) (hJ : catalogIs (PSimple p (Ipart p S b)) tyL28) : False := by
  subst hp3
  have hp := cfg.prime
  have hp2 := cfg.odd
  have hbp : b ^ 3 = 1 := cfg.elem.2 b cfg.hb
  have hL28 := s265f_l28_model hJ
  have hcardJ : Nat.card (PSimple 3 (Ipart 3 S b)) = 504 := s265f_card_l28 hJ
  rcases cfg.prop with hF | ⟨-, hT, -⟩
  · have hN : ¬ S265FSmallOrd (Nat.card (PSimple 3 (Ipart 3 S b))) := by
      rw [hcardJ]
      unfold S265FSmallOrd
      omega
    obtain ⟨lab, hlab, hM, hpn, hΛ', hMD⟩ := s265f_ident hp hp2 hF hbp cfg.ipart hN
    have hder := s265f_not_der_aux hp hlab hpn
    obtain ⟨htag, hrank⟩ := s265f_tag_A1 (lab := ⟨lab.tag, lab.rank, lab.n / 3⟩) hL28 hMD hder
    have hSM : StatedClassicalModel (PSimple 3 S) .PSL 2 2 lab.n := by
      obtain ⟨tg, r, nn⟩ := lab
      dsimp only at htag hrank
      subst htag
      subst hrank
      have hM' : CFSG.Blueprint.LieModel (PSimple 3 S) .PSL (1 + 1) 2 nn := by
        simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
      exact hM'.statedClassicalModel (by decide)
    obtain ⟨-, K, _, _, hKcard, ⟨eK⟩⟩ := hSM
    let ePSL : PSimple 3 S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
      eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := Finite.of_equiv _ ePSL.toEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := lab.n)
      (by rw [← Nat.card_eq_fintype_card]; simpa using hKcard)
    haveI : NeZero ((3 : ℕ) : K) :=
      ⟨fun h => by have := (CharP.cast_eq_zero_iff K 2 3).1 h; omega⟩
    obtain ⟨A, hA, hA3⟩ := qu_aut_rank' cfg
    let e : MulAut (PSimple 3 S) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
      MulAut.congr ePSL
    have hA' : IsElemAbelian 3 (A.map e.toMonoidHom) :=
      CFSG.SectionRank.isElemAbelian_map hA e.toMonoidHom
    have hle := s265f_psl2_aut_card_le (K := K) hp hp2 hA'
    rw [Subgroup.card_map_of_injective e.injective] at hle
    have : (3 : ℕ) ^ 2 < 3 ^ 3 := by norm_num
    omega
  · exact s265f_td4_false_l28 cfg hT hJ

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end
