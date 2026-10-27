module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviBound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperTwE6
public import CFSG.GroupTheory.WeirSylow.CrossRankLinear
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
public import CFSG.LargeExtraspecial.DWFldLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LieType.Chevalley.E6GraphLevi

section Su6Rank

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree


theorem pRank_su6Levi_eq_five {f : ℕ} (hf : 1 ≤ f) {k K : Type} [Field k] [Field K]
    [Algebra k K] [Finite K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(su6Levi σ)) = 5 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcl := (su6Levi_facts (k := k) (K := K) hf hk hK hσ).2.2.2.2.2.1
  rw [StatedClassicalModel] at hcl
  obtain ⟨-, K', hFieldK', hFinK', hcardK', ⟨e⟩⟩ := hcl
  letI : Field K' := hFieldK'
  letI : Finite K' := hFinK'
  have hfn : Nat.card K' = 2 ^ (2 * f) := by rw [hcardK', ← pow_mul, Nat.mul_comm]
  have hchar : CharP K' 2 := CFSG.LargeExtraspecial.DW.charP_two_of_card_eq hfn
  have hpK' : (p : K') ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K' 2 p).1 h
    exact (by omega : p ≠ 2) ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  have hprSU : CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSU 6 (2 ^ f) K')) = 5 := by
    have h := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_top_statedSU_eq_pred
      (F := K') (q := 2 ^ f) (r := p) (m := 6) (by norm_num) hpK' hcardK' hpq
    simpa using h
  have hprPSU : CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K'))) = 5 := by
    rw [CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_eq (d := 6)
      (H := StatedSU 6 (2 ^ f) K') (by
        intro h
        have h23 : 6 = 2 * 3 := by norm_num
        rw [h23] at h
        rcases hp.dvd_mul.1 h with h2 | h3
        · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
          omega
        · have : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
          omega) (by
        intro c hc
        have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU (q := 2 ^ f) hc
        rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
        exact Units.ext (by simpa using hdet))]
    exact hprSU
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact hprPSU

theorem exists_elemAbelian_five_le_su6Levi {f : ℕ} (hf : 1 ≤ f) {k K : Type} [Field k]
    [Field K] [Algebra k K] [Finite K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1) :
    ∃ E : Subgroup (ModGL TwistTag.E6.tag K), E ≤ su6Levi σ ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 5 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ (by norm_num))
  have hpr : CFSG.Open.pRank p (⊤ : Subgroup ↥(su6Levi σ)) = 5 :=
    pRank_su6Levi_eq_five hf hk hK hσ hp hp5 hpq
  obtain ⟨E, -, hEel, hEcard⟩ :=
    exists_isElemAbelian_card_pRank hp (⊤ : Subgroup ↥(su6Levi σ))
  refine ⟨E.map (su6Levi σ).subtype, Subgroup.map_subtype_le E, hEel.map _, ?_⟩
  rw [Subgroup.card_map_of_injective (su6Levi σ).subtype_injective, hEcard, hpr]

theorem five_le_twoLocalPrimeRank_twistedE6RootGroup {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (σ : F ≃+* F) (hF : Nat.card F = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) :
    5 ≤ CFSG.Open.twoLocalPrimeRank p ↥(twistedE6RootGroup F σ) := by
  haveI : Finite (ModGL TwistTag.E6.tag F) := CFSG.LieType.Chevalley.finite_modGL
  let k := CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.fixedSubfield σ.toRingHom
  have hk : Nat.card k = 2 ^ n :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_fixedSubfield_of_card
      (k := F) σ.toRingHom hF hσ
  have h2 : (2 : F) = 0 := E6GraphLevi.two_eq_zero_of_card_sq hn hF
  have hσk : ∀ c, σ.toRingHom c = c ^ Nat.card k := sigma_eq_pow_card hk hσ
  have hXC : thetaRootGroup (algebraMap k F) ≤ twistedE6RootGroup F σ :=
    le_sup_left.trans (E6GraphLevi.thetaRankOneGroup_le_graphFixedRootGroup h2 hσk)
  obtain ⟨E, hEsu6, hEel, hEcard⟩ :=
    exists_elemAbelian_five_le_su6Levi (f := n) hn (k := k) (K := F) hk hF
      (σ := σ.toRingHom) hσ hp hp5 hpq
  have hEX : E ≤ Subgroup.normalizer (thetaRootGroup (algebraMap k F) :
      Set (ModGL TwistTag.E6.tag F)) :=
    (hEsu6.trans ((su6Levi_facts (k := k) (K := F) (σ := σ.toRingHom) hn hk hF hσ).1.trans
      (Subgroup.centralizer_le (le_sup_left : thetaRootGroup (algebraMap k F) ≤
        thetaRankOneGroup (algebraMap k F))))).trans (Subgroup.centralizer_le_normalizer _)
  let H := ↥(twistedE6RootGroup F σ)
  let X' : Subgroup H := (thetaRootGroup (algebraMap k F)).subgroupOf (twistedE6RootGroup F σ)
  let E' : Subgroup H := E.subgroupOf (twistedE6RootGroup F σ)
  have hX'2 : IsPGroup 2 ↥X' :=
    (E6GraphRootPair.isPGroup_thetaRootGroup h2 (algebraMap k F)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hXC).symm
  have hX'ne : X' ≠ ⊥ := by
    have hcard : Nat.card X' = 2 ^ n := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv,
        E6GraphRootSL2.card_thetaRootGroup (algebraMap k F), hk]
    intro hbot
    have h1 : 1 < Nat.card X' := by
      rw [hcard]
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [hbot, Subgroup.card_bot] at h1
    exact lt_irrefl 1 h1
  have hE'el : IsElemAbelian p E' := hEel.comap (twistedE6RootGroup F σ).subtype_injective
  have hE'card : Nat.card E' = p ^ 5 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (hEsu6.trans (su6Levi_le_graphFixedRootGroup σ.toRingHom))).toEquiv
  have hE'N : E' ≤ Subgroup.normalizer (X' : Set H) := by
    have h1 : E.subgroupOf (twistedE6RootGroup F σ) ≤
        (Subgroup.normalizer (thetaRootGroup (algebraMap k F) :
          Set (ModGL TwistTag.E6.tag F))).subgroupOf (twistedE6RootGroup F σ) :=
      Subgroup.subgroupOf_mono _ hEX
    rwa [Subgroup.subgroupOf_normalizer_eq hXC] at h1
  exact le_twoLocalPrimeRank_of_normalizer hp hX'ne hX'2 hE'el hE'card hE'N

end Su6Rank

section Maximal


theorem glaTwoLocalRank_twistedE6RootGroup_eq_five {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (σ : F ≃+* F) (hF : Nat.card F = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) :
    GLATwoLocalRank p ↥(twistedE6RootGroup F σ) = 5 := by
  have hp2 : p ≠ 2 := by omega
  haveI : Finite (ModGL TwistTag.E6.tag F) := CFSG.LieType.Chevalley.finite_modGL
  have hhigh : CFSG.Open.twoLocalPrimeRank p ↥(twistedE6RootGroup F σ) ≤ 5 :=
    twoLocalPrimeRank_twistedE6RootGroup_le_five hn σ hF hσ
      rk2TwE6LeviRankInputMaximal_holds hp hp2 hpq
  have hlow := five_le_twoLocalPrimeRank_twistedE6RootGroup hn σ hF hσ hp hp5 hpq
  unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank
  exact le_antisymm hhigh hlow

end Maximal

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
