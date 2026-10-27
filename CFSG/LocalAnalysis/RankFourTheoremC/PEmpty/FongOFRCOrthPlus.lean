module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCOrthCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieOrth
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCArith

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadPlus StatedClassicalModel)

theorem exists_witt_three_quadPlus {F : Type} [Field F] {n : ℕ} (hn : 3 ≤ n) :
    ∃ T : Submodule F (Fin n ⊕ Fin n → F), Module.finrank F T = 3 ∧
      ∀ x ∈ T, (CFSG.LieType.Universal.Spin.quadPlus n F) x = 0 :=
  (CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := n) hn).2

theorem dvd_natCast_pow_prime_add_one_iff {p : ℕ} (hp : p.Prime) (q n : ℕ) :
    (p : ℤ) ∣ ((q ^ p : ℕ) : ℤ) ^ n + 1 ↔ (p : ℤ) ∣ (q : ℤ) ^ n + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card]

theorem pRank_statedProj_OmegaPlus_formula {F : Type} [Field F] [Finite F] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n) (hpF : ¬ p ∣ Nat.card F) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n F)))) =
      if (p : ℤ) ∣ (Nat.card F : ℤ) ^ n + 1 then
        (if Even (orderOf (Nat.card F : ZMod p)) then 2 * (n - 1) else n - 1) /
          orderOf (Nat.card F : ZMod p)
      else (if Even (orderOf (Nat.card F : ZMod p)) then 2 * n else n) /
        orderOf (Nat.card F : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  have hpK : ¬ p ∣ Fintype.card F := by
    rw [hc]
    exact hpF
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n F
  have hT := exists_witt_three_quadPlus (F := F) (n := n) (by omega)
  have hW := pRank_statedProj_statedOmega_eq_orthogonal_of_witt (K := F)
    (Q := CFSG.LieType.Universal.Spin.quadPlus n F) (CFSG.LieType.Universal.Spin.coe_quadPlus n F)
    hnd hT hp2
  have hdim : Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
    rw [Fintype.card_sum, Fintype.card_fin]
    omega
  have hO := CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_orthogonal_even
    (p := p) (hp.odd_of_ne_two hp2) (K := F) hpK (ι := Fin n ⊕ Fin n) (n := n) (by omega) hdim
    (CFSG.LieType.Universal.Spin.quadPlus n F) hnd (ε := 1)
    (Or.inl ⟨rfl, CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus F n⟩)
  rw [hW, hO]
  simp only [CFSG.GroupTheory.WeirSylow.weirE, hc]

theorem pRank_statedProj_OmegaPlus_eq_of_pow {F F₀ : Type} [Field F] [Field F₀] [Finite F]
    [Finite F₀] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hcard : Nat.card F = Nat.card F₀ ^ p) (hpF : ¬ p ∣ Nat.card F) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n F)))) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n F₀)))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF₀ : ¬ p ∣ Nat.card F₀ := fun h => hpF (hcard ▸ h.trans (dvd_pow_self _ hp.ne_zero))
  have hcond : (p : ℤ) ∣ (Nat.card F : ℤ) ^ n + 1 ↔ (p : ℤ) ∣ (Nat.card F₀ : ℤ) ^ n + 1 := by
    rw [hcard]
    exact dvd_natCast_pow_prime_add_one_iff hp _ _
  have hord : orderOf (Nat.card F : ZMod p) = orderOf (Nat.card F₀ : ZMod p) := by
    rw [hcard]
    exact OFRC.orderOf_natCast_pow_prime _
  rw [pRank_statedProj_OmegaPlus_formula hp hp2 hn hpF,
    pRank_statedProj_OmegaPlus_formula hp hp2 hn hF₀]
  simp only [hcond, hord]

theorem outerFixedRankCrossAt_POmegaPlus : OuterFixedRankCrossAt .POmegaPlus := by
  intro K _ _ n ℓ f _ hmodel _ p hp hp5 hℓ _ α hαp hαin hrk
  have hcl : StatedClassicalModel K .POmegaPlus n ℓ f :=
    hmodel.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨hpf, F₀, hF₀, hF₀fin, hcard, hrank⟩ :=
    pomegaPlus_pRank_fixed hcl hp (by omega) (fun h => by omega) α hαp hαin
  obtain ⟨⟨hℓp, -, hn⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hFcard]
    exact OFRC.not_dvd_pow_of_ne hp hℓp hℓ
  have hFcard' : Nat.card F = Nat.card F₀ ^ p := by
    rw [hFcard, hcard, ← pow_mul, Nat.div_mul_cancel hpf]
  have hK : CFSG.Open.pRank p (⊤ : Subgroup K) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n F)))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  have heq := pRank_statedProj_OmegaPlus_eq_of_pow hp (by omega) hn hFcard' hpF
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
