module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinHighCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5LowExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (genericOrders_fst_pos)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (factorization_card_table)
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.RankThree.PartTwo.Sec4.Census (tableOrder)

theorem dvd_generic_of_dvd_center {K X : Type} [Group K] [Finite K] [Group X]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hK : CFSG.Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* X) {t : StatedLieTag} {n p' f : ℕ}
    (hm : CFSG.Models.LieModel X t n p' f)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .E6 ∨ t = .twistedE6)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hne : p ≠ p')
    (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    p ∣ (genericOrders t n p' f).1 := by
  have hK' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hK
  have hdvd : Nat.card (Subgroup.center K) ∣ tableOrder t n p' f :=
    CFSG.RankThree.PartTwo.Sec4.Census.card_center_dvd_tableOrder hGA hK' e hm
  have hp' : p ∣ tableOrder t n p' f := hpZ.trans hdvd
  unfold tableOrder at hp'
  rw [genericOrders_snd_eq_one ht n p' f, mul_one] at hp'
  rcases (Nat.Prime.dvd_mul hp).1 hp' with h | h
  · exact h
  · exfalso
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact (not_dvd_exceptional hp hp2 ht hne).1 h1
    · exact (not_dvd_exceptional hp hp2 ht hne).2 h1

theorem pRank_ge_PSL (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {F : Type} [Field F] [Finite F] {N r f : ℕ}
    (hadm : StatedLieAdmissible .PSL N r f) (hF : Nat.card F = r ^ f)
    (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSL N F)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hN : 4 ≤ N) (hpq : p ∣ r ^ f - 1) (hne : p ≠ r)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    N - 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  have hr : r.Prime := hadm.1
  have hq0 : 1 ≤ r ^ f := hF ▸ Nat.card_pos
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSL N F)) .PSL N r f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  have ha : p ∣ (genericOrders .PSL N r f).1 :=
    dvd_generic_of_dvd_center hGA hK e hmm (Or.inl rfl) hp hp2 hne hpZ
  have hga : (genericOrders .PSL N r f).1 = Nat.gcd N (r ^ f - 1) := rfl
  obtain ⟨hfin, hcard⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf
    hGA hmm
  haveI := hfin
  have hdv : (genericOrders .PSL N r f).1 ∣
      Nat.card ((StatedScalars (Fin N) F).subgroupOf (StatedSL N F)) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.dvd_card_scalars (q := r ^ f) (by omega)
      hq0 (Or.inl ⟨hF, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSL N F)))).factorization p ≤
      (Nat.card ((StatedScalars (Fin N) F).subgroupOf (StatedSL N F))).factorization p := by
    rw [hcard]
    refine (factorization_card_table hp hp2 hadm (Or.inl rfl) ha).trans ?_
    exact (Nat.factorization_le_iff_dvd (genericOrders_fst_pos hadm).ne' Nat.card_pos.ne').2
      hdv p
  have : Fact p.Prime := ⟨hp⟩
  exact CFSG.HardMathSupport.Timmesfeld.LinearRank.rank_ge_cover (K := F) ⟨hK.1⟩ hr hp hp2 hN
    (H := StatedSL N F) (Or.inl ⟨hF, rfl, hpq⟩) e hpZ hM

theorem pRank_ge_PSU (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {F : Type} [Field F] [Finite F] {N r f : ℕ}
    (hadm : StatedLieAdmissible .PSU N r f) (hF : Nat.card F = (r ^ f) ^ 2)
    (e : K ⧸ Subgroup.center K ≃* StatedProj (StatedSU N (r ^ f) F)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hN : 4 ≤ N) (hpq : p ∣ r ^ f + 1) (hne : p ≠ r)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) :
    N - 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  have hr : r.Prime := hadm.1
  have hq0 : 1 ≤ r ^ f := by
    have h1 : 1 ≤ (r ^ f) ^ 2 := hF ▸ Nat.card_pos
    exact Nat.one_le_iff_ne_zero.2 (fun h0 => by simp [h0] at h1)
  have hmm : CFSG.Models.LieModel (StatedProj (StatedSU N (r ^ f) F)) .PSU N r f :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  have ha : p ∣ (genericOrders .PSU N r f).1 :=
    dvd_generic_of_dvd_center hGA hK e hmm (Or.inr (Or.inl rfl)) hp hp2 hne hpZ
  have hga : (genericOrders .PSU N r f).1 = Nat.gcd N (r ^ f + 1) := rfl
  obtain ⟨hfin, hcard⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf
    hGA hmm
  haveI := hfin
  have hdv : (genericOrders .PSU N r f).1 ∣
      Nat.card ((StatedScalars (Fin N) F).subgroupOf (StatedSU N (r ^ f) F)) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.dvd_card_scalars (q := r ^ f) (by omega)
      hq0 (Or.inr ⟨hF, rfl, hga ▸ Nat.gcd_dvd_left _ _, hga ▸ Nat.gcd_dvd_right _ _⟩)
  have hM : (Nat.card (hopfMultiplier (StatedProj (StatedSU N (r ^ f) F)))).factorization p ≤
      (Nat.card ((StatedScalars (Fin N) F).subgroupOf (StatedSU N (r ^ f) F))).factorization p := by
    rw [hcard]
    refine (factorization_card_table hp hp2 hadm (Or.inr rfl) ha).trans ?_
    exact (Nat.factorization_le_iff_dvd (genericOrders_fst_pos hadm).ne' Nat.card_pos.ne').2
      hdv p
  have : Fact p.Prime := ⟨hp⟩
  exact CFSG.HardMathSupport.Timmesfeld.LinearRank.rank_ge_cover (K := F) ⟨hK.1⟩ hr hp hp2 hN
    (H := StatedSU N (r ^ f) F) (Or.inr ⟨hF, rfl, hpq⟩) e hpZ hM

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
