module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCArith
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieOrth
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossOmega

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedOmega StatedQuadMinus)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.GroupTheory.WeirSylow (weirE)

theorem exists_witt_three_quadMinus {F : Type} [Field F] {n : ℕ} (hn : 4 ≤ n) (b c : F) :
    ∃ T : Submodule F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F), Module.finrank F T = 3 ∧
      ∀ x ∈ T, (CFSG.LieType.Universal.Spin.quadMinus n F b c) x = 0 := by
  have h01 : (CFSG.ClassicalGroups.Orthogonal.minusPair F b c (⟨0, by omega⟩ : Fin (n - 1))).Orth
      (CFSG.ClassicalGroups.Orthogonal.minusPair F b c (⟨1, by omega⟩ : Fin (n - 1))) :=
    CFSG.ClassicalGroups.Orthogonal.minusPair_orth (by simp [Fin.ext_iff])
  have h02 : (CFSG.ClassicalGroups.Orthogonal.minusPair F b c (⟨0, by omega⟩ : Fin (n - 1))).Orth
      (CFSG.ClassicalGroups.Orthogonal.minusPair F b c (⟨2, by omega⟩ : Fin (n - 1))) :=
    CFSG.ClassicalGroups.Orthogonal.minusPair_orth (by simp [Fin.ext_iff])
  have h12 : (CFSG.ClassicalGroups.Orthogonal.minusPair F b c (⟨1, by omega⟩ : Fin (n - 1))).Orth
      (CFSG.ClassicalGroups.Orthogonal.minusPair F b c (⟨2, by omega⟩ : Fin (n - 1))) :=
    CFSG.ClassicalGroups.Orthogonal.minusPair_orth (by simp [Fin.ext_iff])
  exact CFSG.ClassicalGroups.Orthogonal.exists_totallySingular_of_hypPairs h01 h02 h12

theorem int_dvd_card_pow_add_iff {p : ℕ} {q q₀ : ℕ} (h : (q : ZMod p) = (q₀ : ZMod p))
    (n : ℕ) (ε : ℤ) : (p : ℤ) ∣ (q : ℤ) ^ n + ε ↔ (p : ℤ) ∣ (q₀ : ℤ) ^ n + ε := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [h]

theorem pRank_statedProj_OmegaMinus_formula {F : Type} [Field F] [Finite F] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hpF : ¬ p ∣ Nat.card F) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F b c)))) =
      if (p : ℤ) ∣ (Nat.card F : ℤ) ^ n + (-1) then
        (if Even (orderOf (Nat.card F : ZMod p)) then 2 * (n - 1) else n - 1) /
          orderOf (Nat.card F : ZMod p)
      else (if Even (orderOf (Nat.card F : ZMod p)) then 2 * n else n) /
        orderOf (Nat.card F : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  have hpF' : ¬ p ∣ Fintype.card F := by rw [hc]; exact hpF
  have hn1 : 1 ≤ n := by omega
  have hdim : Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) = 2 * n := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n F hirr
  have hMinus : CFSG.GroupTheory.WeirSylow.IsMinusType
      (CFSG.LieType.Universal.Spin.quadMinus n F b c) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega.isMinusType_quadMinus hn1 hirr
  have hW := CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_orthogonal_even (p := p)
    (hp.odd_of_ne_two hp2) hpF' hn1 hdim (CFSG.LieType.Universal.Spin.quadMinus n F b c) hnd
    (ε := -1) (Or.inr ⟨rfl, hMinus⟩)
  have hΩ := pRank_statedProj_statedOmega_eq_orthogonal_of_witt (p := p)
    (CFSG.LieType.Universal.Spin.coe_quadMinus n F b c) hnd (exists_witt_three_quadMinus hn b c) hp2
  rw [hΩ, hW]
  simp only [weirE, hc]

theorem pRank_statedProj_OmegaMinus_eq_of_pow {F F₀ : Type} [Field F] [Field F₀] [Finite F]
    [Finite F₀] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {b₀ c₀ : F₀}
    (hirr₀ : ∀ s : F₀, s ^ 2 + b₀ * s + c₀ ≠ 0) (hcard : Nat.card F = Nat.card F₀ ^ p)
    (hpF : ¬ p ∣ Nat.card F) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F b c)))) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F₀ b₀ c₀)))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF₀ : ¬ p ∣ Nat.card F₀ := fun h => hpF (hcard ▸ h.trans (dvd_pow_self _ hp.ne_zero))
  have hz : ((Nat.card F : ℕ) : ZMod p) = ((Nat.card F₀ : ℕ) : ZMod p) := by
    rw [hcard]
    exact OFRC.natCast_pow_prime (p := p) (Nat.card F₀)
  have hiff := int_dvd_card_pow_add_iff hz n (-1)
  rw [pRank_statedProj_OmegaMinus_formula hp hp2 hn hirr hpF,
    pRank_statedProj_OmegaMinus_formula hp hp2 hn hirr₀ hF₀, hz]
  by_cases h1 : (p : ℤ) ∣ (Nat.card F₀ : ℤ) ^ n + (-1)
  · rw [if_pos (hiff.2 h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hiff.1 h)), if_neg h1]

theorem outerFixedRankCrossAt_POmegaMinus : OuterFixedRankCrossAt .POmegaMinus := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ hdivL α hαp hαin hrk
  have hcl : StatedClassicalModel K .POmegaMinus n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨hpf, F₀, hF₀, hF₀fin, hcard, b₀, c₀, hirr₀, hrank⟩ :=
    pomegaMinus_pRank_fixed hcl hp (by omega) α hαp hαin
  obtain ⟨⟨hℓp, hf, hn4⟩, F, hF, hFin, hFcard, b, c, hirr, ⟨e⟩⟩ := hcl
  have hFcard' : Nat.card F = Nat.card F₀ ^ p := by
    rw [hFcard, hcard, ← pow_mul, Nat.div_mul_cancel hpf]
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hFcard]
    exact OFRC.not_dvd_pow_of_ne hp hℓp hℓ
  have hK : CFSG.Open.pRank p (⊤ : Subgroup K) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F b c)))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have heq := pRank_statedProj_OmegaMinus_eq_of_pow hp (by omega) hn4 hirr hirr₀ hFcard' hpF
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
