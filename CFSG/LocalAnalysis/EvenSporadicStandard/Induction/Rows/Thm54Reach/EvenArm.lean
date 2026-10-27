module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Fixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.TypeFacts
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatEvenOuter
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatEvenBenderOuter

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.SymplecticPilot (CatSp2mEvenOuterExact)
open CFSG.SeitzReduction.UnitaryPilot (CatSUmEvenOuterAt)
open CFSG.SeitzReduction.LinearPilot (CatSLmEvenOuterAt)
open CFSG.LocalAnalysis.EvenBN.GMSK.CatEvenBender (EvenOuterListOf)

theorem exists_orderOf_eq_two_of_isPGroup {G : Type} [Group G] [Finite G] {U : Subgroup G}
    (hU : IsPGroup 2 U) (hne : U ≠ ⊥) : ∃ z ∈ U, orderOf z = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).2 hne
  obtain ⟨n, hn, hcard⟩ := hU.nontrivial_iff_card.1 inferInstance
  have hdvd : 2 ∣ Nat.card U := by
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 hdvd
  exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩

theorem false_of_involution_centralizes
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} (hev : EvenLieType ↥N)
    {P : Subgroup Y} (hsol : SolStd P) (hq : CFSG.IsQuasisimple ↥P) (hPN : P ≤ N)
    {z : ↥N} (hz : orderOf z = 2) (hzC : (z : Y) ∈ centralizer (P : Set Y)) : False := by
  have hz2 : orderOf (z : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hLC : P ≤ centralizer ({(z : Y)} : Set Y) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hzC l hl)
  have hcomp : IsCompIn P (centralizer ({(z : Y)} : Set Y)) :=
    isCompIn_of_normal hLC hq
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLC).2
        (hsol.centralizer_le_normalizer hzC hz2))
  exact hEI ↥N hev z hz _ (isComponent_centralizer_of_normal hcomp hPN)

theorem odd_card_center_of_evenLie
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} (hev : EvenLieType ↥N)
    {P : Subgroup Y} (hsol : SolStd P) (hq : CFSG.IsQuasisimple ↥P) (hPN : P ≤ N) :
    Odd (Nat.card ↥(center ↥P)) := by
  by_contra hodd
  have hev2 : Even (Nat.card ↥(center ↥P)) := Nat.not_odd_iff_even.1 hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥P)) 2
    (even_iff_two_dvd.1 hev2)
  have hr2 : orderOf ((r : ↥P) : Y) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hr
  have hrC : ((r : ↥P) : Y) ∈ centralizer (P : Set Y) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 r.2 ⟨y, hy⟩)
  refine false_of_involution_centralizes hEI hev hsol hq hPN
    (z := ⟨((r : ↥P) : Y), hPN (r : ↥P).2⟩) ?_ hrC
  rw [Subgroup.orderOf_mk]
  exact hr2

theorem fixedCentralizerTwoFree_of_component
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} (hev : EvenLieType ↥N)
    {P : Subgroup Y} (hsol : SolStd P) (hq : CFSG.IsQuasisimple ↥P) (hPN : P ≤ N)
    {σ : MulAut ↥N} {D : Subgroup ↥(fixedSubgroup σ)}
    (hDP : D.map (fixedSubgroup σ).subtype = P.subgroupOf N) : FixedCentralizerTwoFree σ D := by
  intro U hU hUC _
  by_contra hne
  obtain ⟨z, hzU, hz2⟩ := exists_orderOf_eq_two_of_isPGroup hU hne
  have hzP : (z : Y) ∈ centralizer (P : Set Y) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hz' := hUC hzU
    rw [hDP] at hz'
    have h' := mem_centralizer_iff.1 hz' ⟨x, hPN hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx)
    exact congrArg Subtype.val h'
  exact false_of_involution_centralizes hEI hev hsol hq hPN hz2 hzP

noncomputable def centerQuotientEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

structure EvenArmInputs : Prop where
  sz : ∀ f : ℕ, EvenOuterListOf (fun X _ => LieModel X .twistedB2 0 2 f)
    (fun S _ => LieModel S .PSp 2 2 f)
  sp : CatSp2mEvenOuterExact 2
  su4 : CatSUmEvenOuterAt 4
  su5 : CatSUmEvenOuterAt 5
  sl4 : CatSLmEvenOuterAt 4
  sl5 : CatSLmEvenOuterAt 5
  spCover : ∀ {L : Type} [Group L] [Finite L], CFSG.IsQuasisimple L →
    Odd (Nat.card (center L)) → ∀ {n f : ℕ},
      CFSG.Open.StatedClassicalModel (L ⧸ center L) .PSp n 2 f → center L = ⊥

theorem evenArm_result (E : EvenArmInputs) (hO : LieOrderFormulasInput)
    {N : Type} [Group N] [Finite N] (hS : IsSimpleGroup N) (hna : ∃ a b : N, a * b ≠ b * a)
    (hev : EvenLieType N) {σ : MulAut N} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : N →* MulAut N).range)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) (hfree : FixedCentralizerTwoFree σ D)
    {P : Type} [Group P] [Finite P] (e : ↥D ≃* P) (hq : CFSG.IsQuasisimple P)
    (hodd : Odd (Nat.card (center P)))
    (hT : Sol78Thm54Types (P ⧸ center P)) (h29 : ¬ 29 ∣ Nat.card (P ⧸ center P)) :
    Sol78Thm54Types N ∧ ¬ 29 ∣ Nat.card N := by
  have eQ : ↥D ⧸ center ↥D ≃* P ⧸ center P := centerQuotientEquiv e
  rcases hT with ⟨n, hn, hSz⟩ | ⟨m, hm, hP | hP | hP | hP | hP⟩
  ·
    have hSzD : SuzukiModel (↥D ⧸ center ↥D) 2 (2 * n + 1) :=
      suzukiModel_of_mulEquiv' eQ.symm hSz
    have hLie : LieModel (↥D ⧸ center ↥D) .twistedB2 0 2 (2 * n + 1) :=
      Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hSzD⟩))
    have hN := E.sz (2 * n + 1) N hS hna hev σ hσ hout D hD hLie
    have h7 : ¬ 7 ∣ (2 * n + 1) := fun h => h29 ((dvd29_card_suzuki' hO hSz).2 h)
    exact thm54_of_lieFam (by omega) h7 (Or.inl hN)
  ·
    have hZ : center P = ⊥ := E.spCover hq hodd (hP.statedClassicalModel (by decide))
    have hDsp : LieModel ↥D .PSp 2 2 m :=
      LieModel.of_mulEquiv e.symm (LieModel.of_quotient_center hZ hP)
    obtain ⟨hov, -⟩ := E.sp N hS hna hev σ hσ hout m D hD hDsp
    have h7 : ¬ 7 ∣ m := fun h => h29 ((dvd29_card_psp hP).2 h)
    rcases hov with h | h | h | h | h | h | h
    · exact thm54_of_lieFam (m := 2 * m) (by omega) (by omega) (Or.inl h)
    · exact thm54_of_lieFam hm h7 (Or.inr (Or.inr (Or.inl h)))
    · exact thm54_of_lieFam hm h7 (Or.inr (Or.inl h))
    · exact thm54_of_lieFam hm h7 (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact thm54_of_lieFam hm h7 (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact absurd h.admissible.2.2 (by norm_num)
    · exact absurd h.admissible.2.2 (by norm_num)
  ·
    have hU : LieModel (↥D ⧸ center ↥D) .PSU 4 2 m := LieModel.of_mulEquiv eQ.symm hP
    have hN := E.su4 N hS hna hev σ hσ hout m D hD hU hfree
    have h7 : ¬ 7 ∣ m := fun h => h29 ((dvd29_card_psu_four hP).2 h)
    exact thm54_of_lieFam (m := 2 * m) (by omega) (by omega) (Or.inr (Or.inr (Or.inl hN)))
  ·
    have hL : LieModel (↥D ⧸ center ↥D) .PSL 4 2 m := LieModel.of_mulEquiv eQ.symm hP
    have hN := E.sl4 N hS hna hev σ hσ hout m D hD hL hfree
    have h7 : ¬ 7 ∣ m := fun h => h29 ((dvd29_card_psl_four hP).2 h)
    exact thm54_of_lieFam (m := 2 * m) (by omega) (by omega) (Or.inr (Or.inr (Or.inl hN)))
  ·
    have hU : LieModel (↥D ⧸ center ↥D) .PSU 5 2 m := LieModel.of_mulEquiv eQ.symm hP
    have hN := E.su5 N hS hna hev σ hσ hout m D hD hU hfree
    have h7 : ¬ 7 ∣ m := fun h => h29 ((dvd29_card_psu_five hP).2 h)
    exact thm54_of_lieFam (m := 2 * m) (by omega) (by omega)
      (Or.inr (Or.inr (Or.inr (Or.inr hN))))
  ·
    have hL : LieModel (↥D ⧸ center ↥D) .PSL 5 2 m := LieModel.of_mulEquiv eQ.symm hP
    have hN := E.sl5 N hS hna hev σ hσ hout m D hD hL hfree
    have h7 : ¬ 7 ∣ m := fun h => h29 ((dvd29_card_psl_five hP).2 h)
    exact thm54_of_lieFam (m := 2 * m) (by omega) (by omega)
      (Or.inr (Or.inr (Or.inr (Or.inr hN))))

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
