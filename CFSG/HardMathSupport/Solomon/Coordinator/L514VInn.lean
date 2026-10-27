module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514V
public import CFSG.HardMathSupport.Solomon.Coordinator.L514VInnL2
public import CFSG.HardMathSupport.Solomon.Coordinator.L514T
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

section Core

@[deprecated (since := "2026-10-15")]
alias l514vinn_innerAut_le_commutator := innerAut_le_commutator_of_perfect

variable {π : Bool} {p f : ℕ} {K : Type} [Field K] {Y : Type} [Group Y] [Finite Y]

theorem l514vinn_inn_core (hY : CFSG.Open.IsQuasisimple Y) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (e : Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    {α : MulAut Y} (hα3 : α ^ 3 = 1) (hcomm : α ∈ commutator (MulAut Y)) (hα1 : α ≠ 1) :
    ¬ IsFieldAutThree α ∧
      ((∀ J : Subgroup Y, ¬ CFSG.Open.GLAPComponent 3 (fixSub α) J) ∨
        ∃ S : Subgroup Y, CFSG.Open.GLAPComponent 3 (fixSub α) S ∧
          (∀ J : Subgroup Y, CFSG.Open.GLAPComponent 3 (fixSub α) J → J = S) ∧
          IsTypeL2 (p ^ f) (barOf 3 S)) := by
  have hnf : ¬ IsFieldAutThree α := by
    intro hf
    obtain ⟨pkg⟩ := exists_etaPkg hK hq2
    have hGq : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ f) K) :=
      isQuasisimple_slPi hK (fun _ h => by omega)
    have hGp : Group.IsPerfect ↥(slPi π 3 (p ^ f) K) := (Group.isPerfect_def).2 hGq.1
    have hcQ : Subgroup.center
        (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot _
    have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_mulEquiv_of_center_eq_bot e hcQ
    apply hα1
    refine eq_one_of_inndiag_model hY pkg.good ((barEquivBot hZ).trans (e.trans pkg.η)) ?_ hf
    rw [congr_trans', congr_barEquivBot, congr_trans']
    exact pkg.good.down ((mem_commutator_congr (MulAut.congr pkg.η)).2
      ((mem_commutator_congr (MulAut.congr e)).2 hcomm))
  refine ⟨hnf, ?_⟩
  rcases dichot_proj hK hq hq2 e hα3 with hf | hin
  · exact absurd hf hnf
  rcases inner_lay hK hq hq2 hin with hnone | ⟨S0, -, hS0⟩
  · exact Or.inl hnone
  by_cases hex : ∃ J : Subgroup Y, CFSG.Open.GLAPComponent 3 (fixSub α) J
  · obtain ⟨J, hJ⟩ := hex
    refine Or.inr ⟨J, hJ, fun J' hJ' => (hS0 J' hJ').trans (hS0 J hJ).symm, ?_⟩
    obtain ⟨Φ, hΦ⟩ := inner_comp hK hq hq2 hin J hJ
    exact l514vinn_isTypeL2_of_range_slPiTwo hK hq hq2 Φ hΦ
      (isQuasisimple_quotient_of_glaPComponent hJ)
  · push Not at hex
    exact Or.inl hex

end Core

section Model

theorem l514vinn_exists_projModel_of_isL3Eps {Y : Type} [Group Y]
    (hY : CFSG.Open.IsQuasisimple Y) {r : ℕ} (hr : IsL3Eps r Y) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
      2 < p ^ f ∧ p ^ f = r ∧
      Nonempty (Y ≃* (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K))) := by
  rcases hr with ⟨hr3, F, _, hfin, hc, ⟨e⟩⟩ | ⟨hr3, F, _, hfin, hc, ⟨e⟩⟩
  · obtain ⟨p, f, hK, hmod, h2⟩ := exists_true_data F (by rw [hc]; exact hr3)
    refine ⟨true, p, f, F, inferInstance, hK, hmod, h2, ?_,
      ⟨e.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm⟩⟩
    have := hK.card
    rw [hc, piCard, Bool.cond_true] at this
    exact this.symm
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hc
    have hK : PiField false p f F :=
      ⟨hF.prime, hF.one_le, by rw [piCard, Bool.cond_false]; exact hc⟩
    have hmod : ModThree false (p ^ f) := hr3
    have h2 : 2 < p ^ f := two_lt_pow_of_quasisimple_statedSU hY hF e
    exact ⟨false, p, f, F, inferInstance, hK, hmod, h2, rfl,
      ⟨e.trans (QuotientGroup.quotientMulEquivOfEq (center_slPi_eq hK hmod)).symm⟩⟩

end Model

section Main

theorem inputL3inn_holds : InputL3inn innAutDerivedVocab := by
  intro G _ _ K g r hY hr hg3 hInn hnot
  obtain ⟨hgN, hin⟩ := hInn
  have hα3 := barAut_pow_three hgN hg3
  have hα1 : barAut 3 K ⟨g, hgN⟩ ≠ 1 := fun h => hnot ⟨hgN, h⟩
  have hcomm : barAut 3 K ⟨g, hgN⟩ ∈ commutator (MulAut (barOf 3 K)) :=
    innAutDerivedVocab_le_commutator hY hin
  obtain ⟨π, p, f, K', _, hK, hq, hq2, rfl, ⟨e⟩⟩ := l514vinn_exists_projModel_of_isL3Eps hY hr
  obtain ⟨hnf, hcases⟩ := l514vinn_inn_core hY hK hq hq2 e hα3 hcomm hα1
  refine ⟨fun ⟨h, hf⟩ => hnf hf, ?_⟩
  have hfix : fixSub (barAut 3 K ⟨g, hgN⟩) = barX 3 K (K ⊓ Cs g) :=
    Lemma512Ns.fixedSub_barAut_eq hg3 hgN
  rw [hfix] at hcases
  rcases hcases with hnone | ⟨S, hS, hu, hL2⟩
  · left
    have h0 := l514t_noComp_transfer (inf_le_left : K ⊓ Cs g ≤ K) hnone
    show sSup {J | CFSG.Open.GLAPComponent 3 (K ⊓ Cs g) J} = ⊥
    have : {J | CFSG.Open.GLAPComponent 3 (K ⊓ Cs g) J} = ∅ :=
      Set.eq_empty_of_forall_notMem h0
    rw [this, sSup_empty]
  · right
    obtain ⟨J₀, hJ₀, hJu, ⟨e'⟩⟩ := l514t_comp_unique_transfer (inf_le_left : K ⊓ Cs g ≤ K) hS hu
    have hlay : CLay K g = J₀ := by
      apply le_antisymm
      · exact sSup_le fun A hA => (hJu A hA).le
      · exact le_sSup hJ₀
    subst hlay
    exact ⟨hJ₀, l514vinn_isTypeL2_congr e'.symm hL2⟩

end Main

end CFSG.HardMathSupport.Solomon.Coordinator
