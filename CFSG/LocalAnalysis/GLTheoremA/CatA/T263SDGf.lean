module

public import CFSG.GroupTheory.QuasisimpleCenterDivisibility
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDAut
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263 CFSG.LocalAnalysis.GLTheoremA.T263.DX
open scoped commutatorElement

theorem sd_rawDatum_twD_two_iff (n : ℕ) (Q : CFSG.Assembly.LargeEvenRawCont) :
    CFSG.Assembly.LargeEvenRawDatum ⟨.twD, 2, n⟩ Q ↔
      CFSG.Assembly.LargeEvenRawDatum ⟨.A, 1, 2 * n⟩ Q := by
  have h : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  simp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeLinear, h]
  rfl

theorem sd_inLambda2_A_two_mul (n : ℕ) (hn : 1 ≤ n) :
    CFSG.Assembly.LargeEvenInLambda2 ⟨.A, 1, 2 * n⟩ := by
  refine ⟨by simp only; omega, ?_⟩
  simp only
  exact ⟨le_rfl, fun _ => by omega⟩

theorem sd_two_le_rank_of_twD {lab : CFSG.Assembly.LargeEvenLabel}
    (hlam : CFSG.Assembly.LargeEvenInLambda2 lab) (htag : lab.tag = .twD) : 2 ≤ lab.rank := by
  have := hlam.2
  rw [htag] at this
  exact this

theorem sd_rawDatum_twD_two_one_iff (Q : CFSG.Assembly.LargeEvenRawCont) :
    CFSG.Assembly.LargeEvenRawDatum ⟨.twD, 2, 1⟩ Q ↔ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 4 ∧ Q (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) K))
        (CFSG.Assembly.LargeEvenMatConjImage (CFSG.Assembly.LargeEvenProjMk _) Set.univ)
        (CFSG.Assembly.LargeEvenMatFieldImage (CFSG.Assembly.LargeEvenProjMk _)) := Iff.rfl

theorem sd_card_proj_sl_two_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin 2) K)) = 60 := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2)
    (by norm_num)
  rw [hK] at h
  have hEq : CFSG.Assembly.LargeEvenSLGroup (Fin 2) K = CFSG.Open.StatedSL 2 K :=
    (CFSG.Open.StatedAPI.statedSL_eq_ker_det 2 K).symm
  rw [hEq]
  refine h.trans ?_
  decide

theorem sd_card_centerQuot_of_label_twD {J : Type} [Group J]
    {lab : CFSG.Assembly.LargeEvenLabel} (hlab : lab = ⟨.twD, 2, 1⟩)
    (hraw : CFSG.Assembly.LargeEvenRawDatum lab fun R _ _ _ =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ ∃ _ : J ⧸ Subgroup.center J ≃* R, lab.n = 1) :
    Nat.card (J ⧸ Subgroup.center J) = 60 := by
  subst hlab
  obtain ⟨K, _, _, hK, -, -, θ, -⟩ := (sd_rawDatum_twD_two_one_iff _).1 hraw
  rw [Nat.card_congr θ.toEquiv]
  exact sd_card_proj_sl_two_four hK

section Marking

variable {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}

theorem sd_exists_markedInnDiag {S : Subgroup Ω} {x : Ω} (hp : p.Prime)
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hdvd : p ∣ Nat.card (↥S ⧸ Subgroup.center ↥S))
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) : ∃ lab : GLALabel, MarkedInnDiag S x lab := by
  have hPC : GLAPComponent p S S :=
    glaPComponent_of_isComponentOf_of_dvd hp ⟨le_rfl, IsSubnormal.refl S, hSq⟩ hdvd
  obtain ⟨hperf, lab, hlab, hraw⟩ := (S10.innDiagOn_iff hPC hSq).2 hInn
  refine ⟨lab, hperf, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R' _ I' F' ⟨hs', hna', θ', -, hind'⟩
  exact ⟨hs', hna', θ', rfl, hind' x (Subgroup.mem_zpowers x)⟩

theorem sd_labS_dvd_of_labelOf (hSub : CFSG.LocalAnalysis.GLTheoremA.SubcompField) (hp : p.Prime)
    (hp2 : p ≠ 2) {S J : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hxp : x ^ p = 1)
    (hxC : x ∉ Subgroup.centralizer (S : Set Ω)) {labS lab : GLALabel} (hM : MarkedInnDiag S x labS)
    (hJ : IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω)))
    (hlam : CFSG.Assembly.LargeEvenInLambda2 lab) (hlab : LabelOf J lab) :
    labS.n ∣ lab.n ∨ (lab.tag = .twD ∧ lab.rank = 2 ∧ labS.n ∣ 2 * lab.n) := by
  have hN : x ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  by_cases htw : lab.tag = .twD ∧ lab.rank = 2
  · right
    refine ⟨htw.1, htw.2, ?_⟩
    obtain ⟨t, r, n⟩ := lab
    obtain ⟨rfl, rfl⟩ := htw
    have hlabA : LabelOf J ⟨.A, 1, 2 * n⟩ := by
      obtain ⟨hperf, lab', hlam', hraw⟩ := hlab
      obtain ⟨R, _, I, F, hs, hna, θ, hlabeq⟩ :=
        CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
      subst hlabeq
      refine ⟨hperf, ⟨.A, 1, 2 * n⟩, sd_inLambda2_A_two_mul n hlam.1, ?_⟩
      refine (sd_rawDatum_twD_two_iff n _).1 ?_
      exact CFSG.StandardType.Canonical.largeEvenRawDatum_mono
        (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw
    exact hSub Ω S J x labS ⟨.A, 1, 2 * n⟩ p hp hp2 hxp hN hxC hM hJ hlabA (fun h => by cases h)
  · left
    have h3 : lab.tag = .twD → 3 ≤ lab.rank := by
      intro htag
      have h2 := sd_two_le_rank_of_twD hlam htag
      have : lab.rank ≠ 2 := fun hr => htw ⟨htag, hr⟩
      omega
    exact hSub Ω S J x labS lab p hp hp2 hxp hN hxC hM hJ hlab h3

end Marking


section Main

variable {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}

theorem sd_dvd_card_centerQuot {S J : Subgroup Ω} (hp : p.Prime) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hJS : J ≤ S) (hJp : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)) :
    p ∣ Nat.card (↥S ⧸ Subgroup.center ↥S) := by
  have h1 : p ∣ Nat.card ↥J := hJp.trans (Subgroup.card_quotient_dvd_card _)
  have h2 : p ∣ Nat.card ↥S := h1.trans (Subgroup.card_dvd_of_le hJS)
  exact CFSG.dvd_card_quotient_center_of_quasisimple
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hSq) hp h2

theorem sd_selComp_or_a5 (hSub : CFSG.LocalAnalysis.GLTheoremA.SubcompField) (hp : p.Prime)
    (hp2 : p ≠ 2) {S B₀ T' : Subgroup Ω} {x : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hF2 : p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1))
    (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) {J : Subgroup Ω} (hJ : SDCore p S B₀ T' x J) :
    SelComp p S B₀ T' x J ∨ (p = 3 ∧ Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) := by
  by_cases h3 : p = 3
  · subst h3
    by_cases hm : GLAMarking (↥J) (fun lab _ _ _ _ _ => lab.n = 1)
    · right
      refine ⟨rfl, ?_⟩
      obtain ⟨labS, hMS⟩ := sd_exists_markedInnDiag hp hSq
        (sd_dvd_card_centerQuot hp hSq (hJ.comp.1.trans inf_le_left) hJ.pdvd) hInn
      obtain ⟨hperf, lab, hlam, hraw⟩ := hm
      obtain ⟨R, _, I, F, hs, hna, θ, hn1⟩ :=
        CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
      have hlabJ : LabelOf J lab := by
        refine ⟨hperf, lab, hlam, ?_⟩
        exact CFSG.StandardType.Canonical.largeEvenRawDatum_mono
          (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw
      rcases sd_labS_dvd_of_labelOf hSub hp hp2 hSn hxp hxC hMS hJ.comp hlam hlabJ with
        h | ⟨htag, hrank, -⟩
      · exfalso
        rw [hn1] at h
        have hS1 : labS.n = 1 := Nat.dvd_one.1 h
        refine hF2 rfl (CFSG.StandardType.Canonical.largeEvenMarking_mono
          (fun lab' R _ I F θ h => ?_) hMS)
        rw [h.1]
        exact hS1
      · refine sd_card_centerQuot_of_label_twD ?_ hraw
        obtain ⟨t, r, n⟩ := lab
        simp only at htag hrank hn1
        subst htag hrank hn1
        rfl
    · exact Or.inl (hJ.toSelComp fun _ => hm)
  · exact Or.inl (hJ.toSelComp fun h => absurd h h3)

end Main

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
