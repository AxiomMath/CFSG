module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Set
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Statement
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSec59
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3f
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.LocalAnalysis.ComponentClassification.AlternatingUnbalancedDegree
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubQData
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubQComp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFa
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58ReChoice
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubData
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecX0
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTableReduced
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3e
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SecL
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.Walter.JRFacts
public import CFSG.Walter.W67.Statements
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Eight2

variable {X : Type} [Group X] [Finite X]

theorem oddLieType_of_lieModel {G : Type} [Group G] {t : Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ}
    (h : Blueprint.LieModel G t n p f) (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ≠ .twistedB2) :
    Blueprint.OddLieType G := by
  refine ⟨t, n, p, f, hp, hp2, ?_, h⟩
  rcases h with ⟨-, hm⟩ | ⟨hn, -, hm⟩ | ⟨hn, -, hm⟩ | ⟨-, rfl, -⟩
  · exact hm.1
  · subst hn
    exact hm.1
  · subst hn
    exact hm.1
  · exact absurd rfl ht

theorem genFitting_eq_top_of_simple [IsSimpleGroup X] : GeneralizedFitting.subgroup X = ⊤ :=
  (CFSG.generalizedFitting_eq_componentClassification X).symm.trans
    (CFSG.Adapters.generalizedFitting_eq_top_of_isSimpleGroup X)

theorem uOutcome_of_oddLieType [IsSimpleGroup X] (h : Blueprint.OddLieType X) :
    OutcomeLocal.UOutcome X :=
  Or.inl ((ClassicalInvolution.oddLieType_congr
    ((MulEquiv.subgroupCongr genFitting_eq_top_of_simple).trans Subgroup.topEquiv)).2 h)

theorem mod_four_eq_three_of_alternating [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    {n : ℕ} (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n))
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) : n % 4 = 3 := by
  let eF : GeneralizedFitting.subgroup X ≃* X :=
    (MulEquiv.subgroupCongr genFitting_eq_top_of_simple).trans Subgroup.topEquiv
  have : IsSimpleGroup (GeneralizedFitting.subgroup X) := eF.isSimpleGroup
  have hFnonab : ∃ u v : GeneralizedFitting.subgroup X, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnonab
    exact ⟨eF.symm u, eF.symm v, fun h => huv (by simpa using congrArg eF h)⟩
  obtain ⟨z, hz2, hzc⟩ := hz
  obtain ⟨hodd, h1, -⟩ := AlternatingUnbalanced.alternating_generalized_fitting_unbalanced_degree
    hFnonab hn ⟨eF.trans e⟩ hz2 hzc
  have hn1 : n % 4 ≠ 1 := fun h => (h1 h).ne genFitting_eq_top_of_simple
  obtain ⟨k, rfl⟩ := hodd
  omega

omit [Finite X] in
theorem eq_top_of_isPComponent [IsSimpleGroup X] {C M : Subgroup X} (hC : C = ⊤)
    (hM : IsPComponent 2 (M.subgroupOf C)) : M = ⊤ := by
  subst hC
  obtain ⟨K, hK, hsn, hmap, -⟩ := hM
  have : IsSimpleGroup ↥(⊤ : Subgroup X) := Subgroup.topEquiv.isSimpleGroup
  rcases hsn.eq_bot_or_top_of_isSimpleGroup this with h | h
  · exfalso
    rw [h, Subgroup.map_bot] at hmap
    subst hmap
    obtain ⟨⟨-, -, u, v, huv⟩, -⟩ := hK
    apply huv
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    rw [Subsingleton.elim u v]
  · exact eq_top_iff.mpr (subgroupOf_eq_top.mp h)

theorem fusionZStar_eq_bot_of_simple {Y : Type*} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hZ : center Y = ⊥) (h2 : 2 ∣ Nat.card Y) : Open.fusionZStar Y = ⊥ := by
  have hO : pPrimeCore 2 Y = ⊥ := by
    rcases (inferInstance : (pPrimeCore 2 Y).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hc := pPrimeCore_coprime_card (p := 2) (G := Y)
      rw [h, Subgroup.card_top] at hc
      exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2 hc
  have hZ' : center (Y ⧸ pPrimeCore 2 Y) = ⊥ := by
    have e : Y ⧸ pPrimeCore 2 Y ≃* Y :=
      (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
    exact center_eq_bot_of_mulEquiv e.symm hZ
  rw [fusionZStar_eq_of_center_eq_bot hZ', hO]

structure Setting1 (X : Type) [Group X] [Finite X] extends Setting0 X where
  sec : Hyp59 (h.subQuot y)
  sec_a : ∀ ha : h.a ∈ h.secSub y, sec.a = h.subQ y ⟨h.a, ha⟩
  sec_J : sec.J = ((h.secJ0 y).subgroupOf (h.secSub y)).map (h.subQ y)
  sec_S : sec.S = ((hr.S ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y)
  sec_B : sec.B = (h.B.subgroupOf (h.secSub y)).map (h.subQ y)
  sec_K : sec.K = (h.K.subgroupOf (h.secSub y)).map (h.subQ y)
  sec_P : sec.toHyp52.P =
    (((h.reChooseSX hr hr_a hr_J hr_B).P ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y)
  sec_J_equiv : Nonempty (↥sec.J ⧸ pPrimeCore 2 ↥sec.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J)
  lemma81 : Nonempty (generalizedFitting (h.subQuot y) ≃* alternatingGroup (Fin 10)) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (Blueprint.LieModel (sec.J ⧸ pPrimeCore 2 sec.J) .PSL 2 p (2 * f) ∨
        (p = 3 ∧ f = 1 ∧ Nonempty (sec.J ⧸ pPrimeCore 2 sec.J ≃* alternatingGroup (Fin 6)))) ∧
      (Blueprint.LieModel (generalizedFitting (h.subQuot y)) .PSL 4 p f ∨
        Blueprint.LieModel (generalizedFitting (h.subQuot y)) .PSU 4 p f)
  L_pc : IsPComponent 2 ((Seven.Lay h y).subgroupOf (centralizer (h.secB0 y : Set X)))
  L_equiv : Nonempty (↥(Seven.Lay h y) ⧸ Open.fusionZStar ↥(Seven.Lay h y) ≃*
    generalizedFitting (h.subQuot y))

namespace Setting0

variable (s : Setting0 X)

theorem eight_mul_card_B0_le : 8 * Nat.card (s.h.secB0 s.y) ≤
    Nat.card ↥(s.h.P ⊓ s.h.secG0 s.y) := by
  have hTle : s.h.T ≤ s.h.P ⊓ s.h.secG0 s.y :=
    le_inf inf_le_right (inf_le_left.trans s.secCond.Q_le)
  have hyG : s.y ∈ s.h.secG0 s.y := s.secCond.y_mem_G0
  have hyY : s.y ∈ s.h.P ⊓ s.h.secG0 s.y := mem_inf.mpr ⟨s.secCond.mem_P, hyG⟩
  have hlt : s.h.T < s.h.P ⊓ s.h.secG0 s.y :=
    lt_of_le_of_ne hTle fun he => s.secCond.not_mem_T (he ▸ hyY)
  have hdvd : Nat.card s.h.T ∣ Nat.card ↥(s.h.P ⊓ s.h.secG0 s.y) := card_dvd_of_le hTle
  have hne : Nat.card s.h.T ≠ Nat.card ↥(s.h.P ⊓ s.h.secG0 s.y) := fun he =>
    hlt.ne (Subgroup.eq_of_le_of_card_ge hTle he.symm.le)
  have hpos : 0 < Nat.card ↥(s.h.P ⊓ s.h.secG0 s.y) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · rw [hk, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact absurd (show Nat.card s.h.T = Nat.card ↥(s.h.P ⊓ s.h.secG0 s.y) by rw [hk]; ring)
        hne
    · omega
  have hT := s.h.card_T s.NP_eq
  have hB := relIndex_mul_card (H := s.h.secB0 s.y) (K := s.h.B)
  rw [s.relIndex_B0, inf_eq_left.mpr (s.h.secB0_le_B s.y)] at hB
  rw [hk, hT, ← hB]
  nlinarith [Nat.card_pos (α := s.h.secB0 s.y)]

theorem eight_le_card_of_le {Y : Subgroup (s.h.subQuot s.y)}
    (hY : ((s.h.P ⊓ s.h.secG0 s.y).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ≤ Y) :
    8 ≤ Nat.card Y := by
  have hBY : s.h.secB0 s.y ≤ s.h.P ⊓ s.h.secG0 s.y :=
    le_inf ((s.h.secB0_le_B s.y).trans s.h.B_le_P) (le_normalizer : s.h.secB0 s.y ≤ s.h.secG0 s.y)
  have h1 : Nat.card ↥(((s.h.P ⊓ s.h.secG0 s.y).subgroupOf (s.h.secSub s.y)).map
      (s.h.subQ s.y)) * Nat.card (s.h.secB0 s.y) = Nat.card ↥(s.h.P ⊓ s.h.secG0 s.y) :=
    Hyp52.card_map_subQ_mul ((B5a.isPGroup_S s.h).to_le (inf_le_left.trans inf_le_left)) hBY
      (s.h.P_inf_le_secSub s.y)
  have h2 := s.eight_mul_card_B0_le
  have hpos : 0 < Nat.card (s.h.secB0 s.y) := Nat.card_pos
  have h4 : 8 ≤ Nat.card ↥(((s.h.P ⊓ s.h.secG0 s.y).subgroupOf (s.h.secSub s.y)).map
      (s.h.subQ s.y)) := by
    by_contra hlt
    push Not at hlt
    have h5 := Nat.mul_lt_mul_of_pos_right hlt hpos
    rw [h1] at h5
    omega
  exact h4.trans (card_le_of_le hY)

theorem isKGroupCat_or_simple (sec : Hyp59 (s.h.subQuot s.y)) :
    SectionRank.IsKGroupCat (s.h.subQuot s.y) ∨ IsSimpleGroup (s.h.subQuot s.y) := by
  have := s.isSimpleGroup
  by_cases hB0 : s.h.secB0 s.y = ⊥
  · right
    have hC : centralizer (s.h.secB0 s.y : Set X) = ⊤ := by
      rw [hB0, coe_bot, centralizer_eq_top_iff_subset]
      rintro _ rfl
      exact one_mem _
    obtain ⟨M, hMC, hM⟩ := Hyp52.exists_isPComponent_centralizer_secB0 (h := s.h) (y := s.y)
    have hMtop : M = ⊤ := eq_top_of_isPComponent hC hM
    have hH : s.h.secSub s.y = ⊤ := by
      rw [eq_top_iff, ← hMtop]
      exact Hyp52.SubQAux.le_secSub_of_isPComponent hMC hM
    have : IsSimpleGroup ↥(s.h.secSub s.y) :=
      ((MulEquiv.subgroupCongr hH).trans Subgroup.topEquiv).isSimpleGroup
    have : Nontrivial (s.h.subQuot s.y) := by
      refine ⟨⟨sec.a, 1, fun he => ?_⟩⟩
      have h1 := sec.orderOf_a
      rw [he, orderOf_one] at h1
      exact absurd h1 (by norm_num)
    exact IsSimpleGroup.isSimpleGroup_of_surjective (s.h.subQ s.y) (Hyp52.subQ_surjective s.h s.y)
  · exact Or.inl (Hyp52.isKGroupCat_subQuot s.nonab s.kProper hB0)

theorem sec8Case_of {H : Type} [Group H] [Finite H] (sec : Hyp59 H)
    (eJ : center (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J) = ⊥ →
      Nonempty (↥sec.J ⧸ pPrimeCore 2 ↥sec.J ≃* ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J))
    (eK : center (↥s.h.K ⧸ pPrimeCore 2 ↥s.h.K) = ⊥ →
      Nonempty (↥sec.K ⧸ pPrimeCore 2 ↥sec.K ≃* ↥s.h.K ⧸ pPrimeCore 2 ↥s.h.K))
    (hconj : conjugate sec.K sec.a = sec.K ↔ conjugate s.h.K s.h.a = s.h.K) :
    sec.toHyp52.Sec8Case := by
  have hZK : center (↥s.h.K ⧸ pPrimeCore 2 ↥s.h.K) = ⊥ := by
    have hq := s.h.isQuasisimple_K
    rcases s.case8 with ⟨-, -, ⟨e⟩⟩ | ⟨p, f, -, -, -, -, -, hKL⟩
    · exact center_eq_bot_of_mulEquiv e.symm (center_eq_bot_of_mulEquiv_alternating (by norm_num)
        (MulEquiv.refl _))
    · have := Seven.isSimpleGroup_of_lieModel_psp hKL
      exact center_eq_bot_of_isSimpleGroup_of_isQuasisimple hq
  obtain ⟨eK'⟩ := eK hZK
  obtain ⟨eJ'⟩ := eJ s.center_J
  rcases s.case8 with ⟨⟨e6⟩, hKa, ⟨e8⟩⟩ | ⟨p, f, hp, hp2, hf, hJL, hKa, hKL⟩
  · exact Or.inl ⟨⟨eJ'.trans e6⟩, hconj.mpr hKa, ⟨eK'.trans e8⟩⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, LieType.CurtisTits.lieModel_of_mulEquiv eJ'.symm hJL,
      hconj.mpr hKa, LieType.CurtisTits.lieModel_of_mulEquiv eK'.symm hKL⟩

theorem exists_hyp59_section (hκ : s.KappaAt) : ∃ sec : Hyp59 (s.h.subQuot s.y),
    sec.a = s.h.subQ s.y ⟨s.h.a, s.secCond.a_mem_secSub⟩ ∧
    sec.J = ((s.h.secJ0 s.y).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ∧
    sec.S = ((s.hr.S ⊓ s.h.secG0 s.y).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ∧
    sec.B = (s.h.B.subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ∧
    sec.K = (s.h.K.subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ∧
    sec.toHyp52.P = ((s.hsec.P ⊓ s.h.secG0 s.y).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ∧
    (center (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J) = ⊥ →
      Nonempty (↥sec.J ⧸ pPrimeCore 2 ↥sec.J ≃* ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J)) ∧
    (center (↥s.h.K ⧸ pPrimeCore 2 ↥s.h.K) = ⊥ →
      Nonempty (↥sec.K ⧸ pPrimeCore 2 ↥sec.K ≃* ↥s.h.K ⧸ pPrimeCore 2 ↥s.h.K)) ∧
    (conjugate sec.K sec.a = sec.K ↔ conjugate s.h.K s.h.a = s.h.K) := by
  obtain ⟨sec, ha, hJ, hB, hK, -, hS, hP, -, -, -, -, eJ, eK, hconj, -, -, -⟩ :=
    s.secCondR.exists_hyp59_subQuot_of_kappa s.sylowR s.J_normal hκ
  exact ⟨sec, ha, hJ, hS, hB, hK, hP, eJ, eK, hconj⟩

theorem exists_setting1 (h81 : Lemma81StatementK) (hκ : s.KappaAt) :
    ∃ s1 : Setting1 X, s1.toSetting0 = s := by
  obtain ⟨sec, ha, hJ, hS, hB, hK, hP, eJ, eK, hconj⟩ := s.exists_hyp59_section hκ
  obtain ⟨eJ'⟩ := eJ s.center_J
  have hP8 : 8 ≤ Nat.card sec.toHyp52.P := by
    refine s.eight_le_card_of_le ?_
    rw [hP]
    exact map_mono fun w hw => mem_subgroupOf.mpr (mem_inf.mpr
      ⟨s.mem_hsec_P (mem_inf.mp (mem_subgroupOf.mp hw)).1 (mem_inf.mp (mem_subgroupOf.mp hw)).2,
        (mem_inf.mp (mem_subgroupOf.mp hw)).2⟩)
  have hL := h81 (s.h.subQuot s.y) sec (s.isKGroupCat_or_simple sec) (s.sec8Case_of sec eJ eK hconj)
    hP8
  obtain ⟨M, hMC, hM, ⟨eM⟩⟩ := s.secCond.exists_isPComponent_centralizer_of_sub sec
    (MulEquiv.refl _)
  have hLM : Seven.Lay s.h s.y = M := Hyp52.layerIn_centralizer_eq_sub sec hMC hM
  refine ⟨
    { toSetting0 := s
      sec := sec
      sec_a := fun _ => ha
      sec_J := hJ
      sec_S := hS
      sec_B := hB
      sec_K := hK
      sec_P := hP
      sec_J_equiv := ⟨eJ'⟩
      lemma81 := hL
      L_pc := hLM ▸ hM
      L_equiv := hLM ▸ ⟨eM⟩ }, rfl⟩

theorem exists_params {H : Type} [Group H] [Finite H] (sec : Hyp59 H)
    (eJ : Nonempty (↥sec.J ⧸ pPrimeCore 2 ↥sec.J ≃* ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J))
    (hL : Nonempty (generalizedFitting H ≃* alternatingGroup (Fin 10)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        (Blueprint.LieModel (sec.J ⧸ pPrimeCore 2 sec.J) .PSL 2 p (2 * f) ∨
          (p = 3 ∧ f = 1 ∧ Nonempty (sec.J ⧸ pPrimeCore 2 sec.J ≃* alternatingGroup (Fin 6)))) ∧
        (Blueprint.LieModel (generalizedFitting H) .PSL 4 p f ∨
          Blueprint.LieModel (generalizedFitting H) .PSU 4 p f)) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ IsSec82LType ↥(generalizedFitting H) p f ∧
      IsSec8JType (↥sec.J ⧸ pPrimeCore 2 ↥sec.J) p f := by
  rcases hL with h10 | ⟨p, f, hp, hp2, hf, hJ, hLie⟩
  · obtain ⟨-, p, f, hp, hp2, hf, -, hJG⟩ := Hyp52.Sec8Case.exists_params s.h s.case8
    obtain ⟨eJ⟩ := eJ
    refine ⟨p, f, hp, hp2, hf, Or.inr (Or.inr h10), ?_⟩
    rcases hJG with hJL | ⟨rfl, rfl, ⟨e6⟩⟩
    · exact Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv eJ.symm hJL)
    · exact Or.inr ⟨rfl, rfl, ⟨eJ.trans e6⟩⟩
  · refine ⟨p, f, hp, hp2, hf, ?_, hJ⟩
    rcases hLie with hL4 | hU4
    · exact Or.inl hL4
    · exact Or.inr (Or.inl hU4)

theorem inner_of_sec (hInn : CF82Inner) (sec : Hyp59 (s.h.subQuot s.y))
    (ha : sec.a = s.h.subQ s.y ⟨s.h.a, s.secCond.a_mem_secSub⟩)
    (hP : ((s.h.P ⊓ s.h.secG0 s.y).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ≤
      sec.toHyp52.P)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (htype : IsSec82LType ↥(generalizedFitting (s.h.subQuot s.y)) p f)
    (hJt : IsSec8JType (↥sec.J ⧸ pPrimeCore 2 ↥sec.J) p f) :
    sec.a ∈ generalizedFitting (s.h.subQuot s.y) ∧
      (Blueprint.LieModel ↥(generalizedFitting (s.h.subQuot s.y)) .PSL 4 p f → p ^ f % 4 = 3) ∧
      (Blueprint.LieModel ↥(generalizedFitting (s.h.subQuot s.y)) .PSU 4 p f →
        p ^ f % 4 = 1) := by
  obtain ⟨hFeq, hsimple, hcent, -, -⟩ := Hyp59.generalizedFitting_simple sec
  have hcent' : centralizer (generalizedFitting (s.h.subQuot s.y) : Set (s.h.subQuot s.y)) =
      ⊥ := by rw [hFeq]; exact hcent
  obtain ⟨b', hb', b₀, hb₀, hcomm⟩ := s.exists_commutator_eq
  have hBH := s.secCond.B_le_secSub
  have hyH := s.secCond.y_mem_secSub
  have hb₀H : b₀ ∈ s.h.secSub s.y := s.h.secB0_le_secSub s.y hb₀
  set β := s.h.subQ s.y ⟨b', hBH hb'⟩ with hβ
  set ξ := s.h.subQ s.y ⟨s.y, hyH⟩ with hξ
  have hαβξ : sec.a = ⁅β, ξ⁆ := by
    rw [ha, hβ, hξ, ← map_commutatorElement]
    have h1 : (⁅(⟨b', hBH hb'⟩ : ↥(s.h.secSub s.y)), ⟨s.y, hyH⟩⁆ : ↥(s.h.secSub s.y)) =
        ⟨s.h.a, s.secCond.a_mem_secSub⟩ * ⟨b₀, hb₀H⟩ := Subtype.ext hcomm
    rw [h1, map_mul, Hyp52.subQ_eq_one_of_mem_secB0 (w := ⟨b₀, hb₀H⟩) hb₀, mul_one]
  have hker : ∀ w (hw : w ∈ s.h.secSub s.y), w ∈ s.h.P → w ∈ s.h.secG0 s.y →
      s.h.subQ s.y ⟨w, hw⟩ ∈ coreActionKernel sec.J := fun w hw hwP hwG =>
    (mem_inf.mp (hP (mem_map_of_mem _ (show (⟨w, hw⟩ : ↥(s.h.secSub s.y)) ∈
      (s.h.P ⊓ s.h.secG0 s.y).subgroupOf (s.h.secSub s.y) from
        mem_subgroupOf.mpr (mem_inf.mpr ⟨hwP, hwG⟩))))).2
  have hβK := hker b' (hBH hb') (s.h.B_le_P hb') (s.secCond.B_le_G0 hb')
  have hξK := hker s.y hyH s.secCond.mem_P s.secCond.y_mem_G0
  have haa : sec.a * sec.a = 1 := by
    have h1 := pow_orderOf_eq_one sec.a
    rw [sec.orderOf_a, pow_two] at h1
    exact h1
  exact hInn (s.h.subQuot s.y) p f hp hp2 hf hsimple hcent' htype sec.a β ξ haa hαβξ sec.J
    sec.J_le sec.isPComponent_J hJt hβK hξK

end Setting0

namespace Setting1

variable (s : Setting1 X)

theorem subQ_mem_secS {w : X} (hwS : w ∈ s.h.S) (hwG : w ∈ s.h.secG0 s.y)
    (hwH : w ∈ s.h.secSub s.y) : s.h.subQ s.y ⟨w, hwH⟩ ∈ s.sec.S := by
  rw [s.sec_S]
  exact mem_map_of_mem _ (mem_subgroupOf.mpr
    (mem_inf.mpr ⟨s.S0_le_hr (mem_inf.mpr ⟨hwS, hwG⟩), hwG⟩))

theorem subQ_mem_secP {w : X} (hwP : w ∈ s.h.P) (hwG : w ∈ s.h.secG0 s.y)
    (hwH : w ∈ s.h.secSub s.y) : s.h.subQ s.y ⟨w, hwH⟩ ∈ s.sec.toHyp52.P := by
  rw [s.sec_P]
  exact mem_map_of_mem _ (mem_subgroupOf.mpr (mem_inf.mpr ⟨s.mem_hsec_P hwP hwG, hwG⟩))

theorem map_P_le_secP :
    ((s.h.P ⊓ s.h.secG0 s.y).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ≤
      s.sec.toHyp52.P := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hwP, hwG⟩ := mem_inf.mp (mem_subgroupOf.mp hw)
  exact s.subQ_mem_secP hwP hwG w.2

theorem B0_ne_bot : s.h.secB0 s.y ≠ ⊥ := by
  intro hB0
  have := s.isSimpleGroup
  have hC : centralizer (s.h.secB0 s.y : Set X) = ⊤ := by
    rw [hB0, coe_bot, centralizer_eq_top_iff_subset]
    rintro _ rfl
    exact one_mem _
  have hLtop : Seven.Lay s.h s.y = ⊤ := eq_top_of_isPComponent hC s.L_pc
  obtain ⟨eL⟩ := s.L_equiv
  have h2 : 2 ∣ Nat.card X := by
    obtain ⟨z, hz, -⟩ := s.unbal
    rw [← hz]
    exact orderOf_dvd_natCard z
  have hZX : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := s.nonab
      exact huv (mem_center_iff.mp (h ▸ mem_top u) v).symm
  let eT : ↥(Seven.Lay s.h s.y) ≃* X := (MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv
  have : IsSimpleGroup ↥(Seven.Lay s.h s.y) := eT.isSimpleGroup
  have hZL : center ↥(Seven.Lay s.h s.y) = ⊥ := center_eq_bot_of_mulEquiv eT.symm hZX
  have h2L : 2 ∣ Nat.card ↥(Seven.Lay s.h s.y) := by rw [Nat.card_congr eT.toEquiv]; exact h2
  have hZs := fusionZStar_eq_bot_of_simple hZL h2L
  let eX : X ≃* generalizedFitting (s.h.subQuot s.y) :=
    eT.symm.trans ((QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZs.symm)).trans eL)
  rcases s.lemma81 with ⟨⟨e10⟩⟩ | ⟨p, f, hp, hp2, -, -, hLie⟩
  · have h3 := mod_four_eq_three_of_alternating s.nonab (by norm_num : 7 ≤ 10)
      (eX.trans e10) s.unbal
    norm_num at h3
  · apply s.notU
    apply uOutcome_of_oddLieType
    rcases hLie with hL4 | hU4
    · exact oddLieType_of_lieModel (LieType.CurtisTits.lieModel_of_mulEquiv eX.symm hL4) hp hp2
        (by decide)
    · exact oddLieType_of_lieModel (LieType.CurtisTits.lieModel_of_mulEquiv eX.symm hU4) hp hp2
        (by decide)

end Setting1

end Eight2

end CFSG.ComponentClassification.GSThmB
