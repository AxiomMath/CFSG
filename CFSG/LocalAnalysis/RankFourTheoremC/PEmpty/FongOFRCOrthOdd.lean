module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieOrth
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCArith
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSigma

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedOmega StatedQuadOdd StatedSp)

theorem two_ne_zero_of_odd_card_fintype {F : Type} [Field F] [Fintype F]
    (hF : Odd (Fintype.card F)) : (2 : F) ≠ 0 := by
  refine Ring.two_ne_zero fun h => ?_
  have h2 := (FiniteField.even_card_iff_char_two (F := F)).mp h
  rw [Nat.odd_iff] at hF
  omega

theorem odd_card_of_two_ne_zero_fintype {F : Type} [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) :
    Odd (Fintype.card F) := by
  rw [Nat.odd_iff]
  refine FiniteField.odd_card_of_char_ne_two fun hc => h2 ?_
  have h := ringChar.Nat.cast_ringChar (R := F)
  rw [hc] at h
  exact_mod_cast h

theorem exists_witt_three_quadOdd {F : Type} [Field F] {n : ℕ} (hn : 3 ≤ n) :
    ∃ T : Submodule F (Fin n ⊕ Fin n ⊕ Unit → F), Module.finrank F T = 3 ∧
      ∀ x ∈ T, (CFSG.LieType.Universal.Spin.quadOdd n F) x = 0 := by
  have h₁₂ : (CFSG.ClassicalGroups.Orthogonal.oddPair F (⟨0, by omega⟩ : Fin n)).Orth
      (CFSG.ClassicalGroups.Orthogonal.oddPair F ⟨1, by omega⟩) :=
    CFSG.ClassicalGroups.Orthogonal.oddPair_orth (by simp [Fin.ext_iff])
  have h₁₃ : (CFSG.ClassicalGroups.Orthogonal.oddPair F (⟨0, by omega⟩ : Fin n)).Orth
      (CFSG.ClassicalGroups.Orthogonal.oddPair F ⟨2, by omega⟩) :=
    CFSG.ClassicalGroups.Orthogonal.oddPair_orth (by simp [Fin.ext_iff])
  have h₂₃ : (CFSG.ClassicalGroups.Orthogonal.oddPair F (⟨1, by omega⟩ : Fin n)).Orth
      (CFSG.ClassicalGroups.Orthogonal.oddPair F ⟨2, by omega⟩) :=
    CFSG.ClassicalGroups.Orthogonal.oddPair_orth (by simp [Fin.ext_iff])
  exact CFSG.ClassicalGroups.Orthogonal.exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃

theorem pRank_orthogonal_quadOdd {F : Type} [Field F] [Fintype F] {p n : ℕ} [Fact p.Prime]
    (hp : Odd p) (hF : Odd (Fintype.card F)) (hpF : ¬ p ∣ Fintype.card F) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadOdd n F))) =
      (if Even (orderOf (Fintype.card F : ZMod p)) then 2 * n else n) /
        orderOf (Fintype.card F : ZMod p) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card_fintype hF
  have hdim : Module.finrank F (Fin n ⊕ Fin n ⊕ Unit → F) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    omega
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n F h2
  refine CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_eq_of_sylow_sigmaModel p
    (CFSG.GroupTheory.WeirSylow.one_le_weirA hpF) fun P => ?_
  obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp n F)) := inferInstance
  obtain ⟨e₁⟩ := CFSG.GroupTheory.WeirSylow.sylow_orthogonal_odd hp hF hpF hdim
    (CFSG.LieType.Universal.Spin.quadOdd n F) hQ P P'
  obtain ⟨e₂⟩ := CFSG.GroupTheory.WeirSylow.sylow_Sp hp F hpF n P'
  exact ⟨e₁.trans e₂⟩

theorem pRank_statedProj_OmegaOdd_formula {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (hF2 : (2 : F) ≠ 0) (hpF : ¬ p ∣ Nat.card F) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n F)))) =
      (if Even (orderOf (Nat.card F : ZMod p)) then 2 * n else n) /
        orderOf (Nat.card F : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  have hodd : Odd (Fintype.card F) := odd_card_of_two_ne_zero_fintype hF2
  have hpF' : ¬ p ∣ Fintype.card F := by rwa [hc]
  rw [pRank_statedProj_statedOmega_eq_orthogonal_of_witt
      (CFSG.LieType.Universal.Spin.coe_quadOdd n F)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n F hF2)
      (exists_witt_three_quadOdd hn) hp2,
    pRank_orthogonal_quadOdd (n := n) (hp.odd_of_ne_two hp2) hodd hpF', hc]

theorem pRank_statedProj_OmegaOdd_eq_of_pow {F F₀ : Type} [Field F] [Field F₀] [Finite F]
    [Finite F₀] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) (hF2 : (2 : F) ≠ 0)
    (hF₀2 : (2 : F₀) ≠ 0) (hcard : Nat.card F = Nat.card F₀ ^ p) (hpF : ¬ p ∣ Nat.card F) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n F)))) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n F₀)))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF₀ : ¬ p ∣ Nat.card F₀ := fun h => hpF (hcard ▸ h.trans (dvd_pow_self _ hp.ne_zero))
  rw [pRank_statedProj_OmegaOdd_formula hp hp2 hn hF2 hpF,
    pRank_statedProj_OmegaOdd_formula hp hp2 hn hF₀2 hF₀, hcard, OFRC.orderOf_natCast_pow_prime]

theorem outerFixedRankCrossAt_POmegaOdd : OuterFixedRankCrossAt .POmegaOdd := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ hdivL α hαp hαin hrk
  have hcl : StatedClassicalModel K .POmegaOdd n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hpf, F₀, hF₀, hF₀fin, hcard, hrank⟩ := pomegaOdd_pRank_fixed hcl hp hp2 α hαp hαin
  obtain ⟨⟨hℓp, hf, hn, hℓ2⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hFcard' : Nat.card F = Nat.card F₀ ^ p := by
    rw [hFcard, hcard, ← pow_mul, Nat.div_mul_cancel hpf]
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hFcard]
    exact OFRC.not_dvd_pow_of_ne hp hℓp hℓ
  have hF2 : (2 : F) ≠ 0 := by
    have h := OFRC.natCast_ne_zero_of_not_dvd_card (F := F) (p := 2) Nat.prime_two
      (by rw [hFcard]; exact OFRC.not_dvd_pow_of_ne Nat.prime_two hℓp hℓ2)
    exact_mod_cast h
  have hF₀2 : (2 : F₀) ≠ 0 := by
    have h := OFRC.natCast_ne_zero_of_not_dvd_card (F := F₀) (p := 2) Nat.prime_two
      (by rw [hcard]; exact OFRC.not_dvd_pow_of_ne Nat.prime_two hℓp hℓ2)
    exact_mod_cast h
  have hK : CFSG.Open.pRank p (⊤ : Subgroup K) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n F)))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have heq := pRank_statedProj_OmegaOdd_eq_of_pow hp hp2 hn hF2 hF₀2 hFcard' hpF
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
