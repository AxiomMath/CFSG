module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQLab

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremB

section Main


theorem QUCfg.ident_alt6 {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (cfg : QUCfg 3 S B T x b) (hJ : catalogIs (PSimple 3 (Ipart 3 S b)) tyAlt6) :
    FieldOn 3 b S ∧ StatedClassicalModel (PSimple 3 S) .PSp 2 2 3 := by
  obtain ⟨i, hi, he⟩ := hJ
  have hF := cfg.fieldOn_of_tyA ⟨i, Or.inr (Or.inr (Or.inr (Or.inr hi))), he⟩
  refine ⟨hF, ?_⟩
  have hcardJ : Nat.card (PSimple 3 (Ipart 3 S b)) = 360 := by
    cases i <;> try exact hi.elim
    rename_i n hn
    rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> try exact hi.elim
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    show Nat.card (alternatingGroup (Fin 6)) = 360
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hbp : b ^ 3 = 1 := cfg.elem.2 b cfg.hb
  have hb : b ∈ Subgroup.normalizer (S : Set Ω) := hF.1
  obtain ⟨lab, hlab, -, hM, hpn, D, hD, hdat⟩ := FR.fieldOn_subfield hp hp2 hF
  obtain ⟨E, hEC, hEs, hEna, hEperf, h2E, -⟩ := FR.coreSub_of_fieldOn hp hp2
    FR.Res.smallDatum_holds (FR.Res.twF4Core_holds hp hp2) hF
    (FR.exists_perfect_of_ipart hp hb hbp cfg.ipart)
  have hEC' := hEC
  have hEperf' := hEperf
  rw [FR.fixSub_indAut hb] at hEC' hEperf'
  obtain ⟨J₀, hJ₀, hIeq, -⟩ := FR.ipart_single hp hb hbp hEs hEC' hEperf' cfg.ipart
  obtain ⟨e⟩ := I91T.pSimple_component_equiv hp hb hbp hEs hEC hEna hEperf hJ₀
  rw [← hIeq] at e
  have hE : Nat.card E = 360 := (Nat.card_congr e.toEquiv).symm.trans hcardJ
  have hEperfect : ⁅E, E⁆ = E := s265f_perfect_of_simple_sub hEs hEna
  have hED : E ≤ D := hEperfect ▸ (Subgroup.commutator_mono hEC hEC).trans hD.2.1
  have hne : E ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot E).1 hEs.toNontrivial
  rw [hE, show (360 : ℕ) = 2 ^ 3 * 45 by norm_num, FQ.twoPart_two_pow_mul_odd (by decide)] at h2E
  have hdvd : 360 ∣ Nat.card (PSimple 3 S) := by
    rw [← hE]
    exact Subgroup.card_subgroup_dvd_card E
  have htw : ¬ (lab.tag = .twF4 ∧ lab.n = 3) := by
    rintro ⟨ht, hn⟩
    rw [I91T.twF4CentOrder_holds Ω S b hF lab ht hn hM, show (35942400 : ℕ) = 2 ^ 12 * 8775 by
      norm_num, FQ.twoPart_two_pow_mul_odd (by decide)] at h2E
    norm_num at h2E
  rcases hdat with hdat | hexc
  · by_cases hΛ : LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / 3⟩
    ·
      exfalso
      have hder : lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der := by
        obtain ⟨t, r, n⟩ := lab
        obtain ⟨-, hl⟩ := hlab
        dsimp only at hl hpn ⊢
        constructor <;> rintro rfl <;> exact absurd hpn (by rw [hl.2]; norm_num)
      have hna' : ∃ x y : ↥D, x * y ≠ y * x := by
        obtain ⟨x, y, hxy⟩ := hEna
        exact ⟨⟨x, hED x.2⟩, ⟨y, hED y.2⟩, fun h =>
          hxy (Subtype.ext (congrArg (fun z : ↥D => (z : PSimple 3 S)) h))⟩
      obtain ⟨hDs, hMD⟩ := I91T.simple_of_datum hΛ hder.2 hna' hdat
      have hDE : D = E := le_antisymm (hEperf D hD.1 (s265f_perfect_of_simple_sub hDs hna')) hED
      exact ggMarkedModel_card_ne_three_sixty (lab := ⟨lab.tag, lab.rank, lab.n / 3⟩) hder.1 hMD
        (hDE ▸ hE)
    ·
      obtain ⟨t, r, n⟩ := lab
      obtain ⟨hn, hl⟩ := hlab
      dsimp only at hn hl hpn hΛ hdat hM htw
      obtain ⟨m, rfl⟩ := hpn
      have hm : 1 ≤ m := by omega
      rw [show 3 * m / 3 = m by omega] at hΛ hdat
      cases t <;> simp only [LargeEvenInLambda2] at hΛ
      case A =>
        have h1 : r = 1 ∧ m = 1 := by
          by_contra hcon
          apply hΛ
          refine ⟨hm, hl.1, fun hr => ?_⟩
          by_cases hm1 : m = 1
          · exact absurd ⟨hr, hm1⟩ hcon
          · omega
        obtain ⟨rfl, rfl⟩ := h1
        exact (FR.false_of_perfect_solvable hED hEperfect hne (FR.Res.solvable_A11 _ hdat)).elim
      case twA =>
        have h1 : r = 2 ∧ m = 1 := by
          by_contra hcon
          apply hΛ
          refine ⟨hm, hl.1, fun hr => ?_⟩
          by_cases hm1 : m = 1
          · exact absurd ⟨hr, hm1⟩ hcon
          · omega
        obtain ⟨rfl, rfl⟩ := h1
        exact (FR.false_of_perfect_solvable hED hEperfect hne
          (FR.Res.solvable_twA21 _ hdat)).elim
      case B =>
        have h1 : r = 2 ∧ m = 1 := by
          by_contra hcon
          apply hΛ
          refine ⟨hm, hl.1, fun hr => ?_⟩
          by_cases hm1 : m = 1
          · exact absurd ⟨hr, hm1⟩ hcon
          · omega
        obtain ⟨rfl, rfl⟩ := h1
        have h : CFSG.Blueprint.LieModel (PSimple 3 S) .PSp 2 2 3 := by
          simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
        exact h.statedClassicalModel (by decide)
      case C =>
        have h1 : r = 2 ∧ m = 1 := by
          by_contra hcon
          apply hΛ
          refine ⟨hm, hl.1, fun hr => ?_⟩
          by_cases hm1 : m = 1
          · exact absurd ⟨hr, hm1⟩ hcon
          · omega
        obtain ⟨rfl, rfl⟩ := h1
        have h : CFSG.Blueprint.LieModel (PSimple 3 S) .PSp 2 2 3 := by
          simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
        exact h.statedClassicalModel (by decide)
      case D => exact absurd ⟨hm, hl⟩ hΛ
      case twD => exact absurd ⟨hm, hl⟩ hΛ
      case E6 => exact absurd ⟨hm, hl⟩ hΛ
      case E7 => exact absurd ⟨hm, hl⟩ hΛ
      case E8 => exact absurd ⟨hm, hl⟩ hΛ
      case F4 => exact absurd ⟨hm, hl⟩ hΛ
      case twE6 => exact absurd ⟨hm, hl⟩ hΛ
      case triD4 => exact absurd ⟨hm, hl⟩ hΛ
      case G2 =>
        have h1 : m = 1 := by
          by_contra hcon
          apply hΛ
          exact ⟨hm, hl.1, by omega⟩
        obtain rfl := h1
        obtain rfl := hl.1
        rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder (lieModel_of_markedModel rfl hM)]
          at hdvd
        exact absurd hdvd (by decide +kernel)
      case twB2 =>
        obtain ⟨hr, hodd, -⟩ := hl
        have hmodd : Odd m := (Nat.odd_mul.1 hodd).2
        have h1 : m = 1 := by
          by_contra hcon
          apply hΛ
          refine ⟨hm, hr, hmodd, ?_⟩
          obtain ⟨k, hk⟩ := hmodd
          omega
        obtain rfl := h1
        obtain rfl := hr
        exact (FR.false_of_perfect_solvable hED hEperfect hne
          (FR.Res.solvable_twB2 _ hdat)).elim
      case twF4 =>
        obtain ⟨hr, hodd, -⟩ := hl
        have hmodd : Odd m := (Nat.odd_mul.1 hodd).2
        have h1 : m = 1 := by
          by_contra hcon
          apply hΛ
          refine ⟨hm, hr, hmodd, ?_⟩
          obtain ⟨k, hk⟩ := hmodd
          omega
        exact (htw ⟨rfl, by omega⟩).elim
      case B2der => exact absurd hl.2 (by omega)
      case G2der => exact absurd hl.2 (by omega)
      case twF4der => exact absurd hl.2 (by omega)
  · rcases hexc with ⟨-, -, hsol⟩ | hexc
    · exact (FR.false_of_perfect_solvable hED hEperfect hne hsol).elim
    · exact (htw hexc).elim

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end
