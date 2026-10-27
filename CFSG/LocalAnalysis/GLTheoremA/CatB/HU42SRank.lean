module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SRankSU
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42CatDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS11U62Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bU52

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.RankThree.PerfectCover
open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S

theorem card_mult_zmod (a : ℕ) : Nat.card (Multiplicative (ZMod a)) = a := by
  rw [← Nat.card_congr (Multiplicative.ofAdd : ZMod a ≃ Multiplicative (ZMod a))]
  exact Nat.card_zmod a

theorem card_generic_exceptional (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  rw [Nat.card_prod]
  simp only [generic, exceptional, Nat.card_prod, card_mult_zmod]

theorem hopf_card_of_model (hGA : CFSG.Open.GriessAllModelsStatement) {S : Type} [Group S]
    {t : StatedLieTag} {n p f : ℕ} (hm : CFSG.Models.LieModel S t n p f) :
    commutator S = ⊤ ∧ Nat.card (hopfMultiplier S) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨hc, ⟨e⟩⟩ := hGA S t n p f hm
  refine ⟨hc, ?_⟩
  rw [← Nat.card_congr (hopfMultiplierEquivGriess S).toEquiv, Nat.card_congr e.toEquiv,
    card_generic_exceptional]

theorem card_hopf_omegaPlus_two (hGA : CFSG.Open.GriessAllModelsStatement) {S : Type} [Group S]
    (hm : CFSG.Models.LieModel S .POmegaPlus 4 2 1) :
    commutator S = ⊤ ∧ Nat.card (hopfMultiplier S) = 4 := by
  obtain ⟨hc, h⟩ := hopf_card_of_model hGA hm
  refine ⟨hc, ?_⟩
  rw [h]
  have h1 : genericOrders .POmegaPlus 4 2 1 = (1, 1) := by decide
  have h2 : exceptionalOrders .POmegaPlus 4 2 1 = (2, 2) := by decide
  rw [h1, h2]
  norm_num

theorem card_hopf_u5two (hGA : CFSG.Open.GriessAllModelsStatement) {S : Type} [Group S]
    (hm : CFSG.Models.LieModel S .PSU 5 2 1) :
    commutator S = ⊤ ∧ Nat.card (hopfMultiplier S) = 1 := by
  obtain ⟨hc, h⟩ := hopf_card_of_model hGA hm
  refine ⟨hc, ?_⟩
  rw [h]
  have h1 : genericOrders .PSU 5 2 1 = (1, 1) := by
    unfold genericOrders
    norm_num
  have h2 : exceptionalOrders .PSU 5 2 1 = (1, 1) := by decide
  rw [h1, h2]
  norm_num

theorem card_hopf_u6two (hGA : CFSG.Open.GriessAllModelsStatement) {S : Type} [Group S]
    (hm : CFSG.Models.LieModel S .PSU 6 2 1) :
    commutator S = ⊤ ∧ Nat.card (hopfMultiplier S) = 12 := by
  obtain ⟨hc, h⟩ := hopf_card_of_model hGA hm
  refine ⟨hc, ?_⟩
  rw [h]
  have h1 : genericOrders .PSU 6 2 1 = (3, 1) := by
    unfold genericOrders
    norm_num
  have h2 : exceptionalOrders .PSU 6 2 1 = (2, 2) := by decide
  rw [h1, h2]
  norm_num

theorem classical_u6 {S : Type} [Group S] (hm : CFSG.Models.LieModel S .PSU 6 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (S ≃* StatedProj (StatedSU 6 (2 ^ 1) K)) := by
  have hC : StatedClassicalModel S .PSU 6 2 1 :=
    hm.2.resolve_right (fun h => by
      obtain ⟨h0, -⟩ := h
      omega)
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hC
  exact ⟨K, hKf, hKfin, by rw [hKcard]; norm_num, ⟨e⟩⟩

theorem u42RankAt_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : U42RankAt := by
  intro Q _ _ hQ hcat
  obtain ⟨i, hi, ⟨eS⟩⟩ := hcat
  let p : Q →* (Q ⧸ Subgroup.center Q) := QuotientGroup.mk' (Subgroup.center Q)
  have hp : Function.Surjective p := QuotientGroup.mk'_surjective _
  have hpc : p.ker ≤ Subgroup.center Q := by
    rw [QuotientGroup.ker_mk']
  have hker_card : Nat.card p.ker = Nat.card (Subgroup.center Q) := by
    rw [QuotientGroup.ker_mk']
  rcases hi with hD | hU5 | hU6
  ·
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isD4two
      (⟨i, hD, ⟨eS⟩⟩ : catalogIs (Q ⧸ Subgroup.center Q) S9.isD4two)
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq2.trans (by norm_num))
    have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .POmegaPlus 4 2 1 := by
      have := CFSG.Models.lieModel_D 4 q hv e
      rw [h1, h2] at this
      exact this
    obtain ⟨hc, hM⟩ := card_hopf_omegaPlus_two hGA hm
    haveI : Group.IsPerfect (Q ⧸ Subgroup.center Q) := Group.isPerfect_def.mpr hc
    have hdiv : Nat.card p.ker ∣ 4 := by
      rw [← hM]
      exact card_ker_dvd_hopfMultiplier p hp hpc
    obtain ⟨E, hE, hE4⟩ := CFSG.LocalAnalysis.GLTheoremA.D4XF.d4two_rank4
      (⟨i, hD, ⟨eS⟩⟩ : catalogIs (Q ⧸ Subgroup.center Q) S9.isD4two)
    refine ⟨fun h3 => ?_, fun hn => ?_⟩
    · rw [← hker_card] at h3
      have h34 : 3 ∣ 4 := h3.trans hdiv
      norm_num at h34
    · rw [← hker_card] at hn
      obtain ⟨W, hW, hWc⟩ := exists_elemAbelian_lift p hp hn hE
      exact ⟨W, hW, hWc.trans hE4⟩
  ·
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU5two
      (⟨i, hU5, ⟨eS⟩⟩ : catalogIs (Q ⧸ Subgroup.center Q) S9.isU5two)
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq2.trans (by norm_num))
    have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .PSU 5 2 1 := by
      have := CFSG.LocalAnalysis.GLTheoremA.lieModel_twistedA' 4 q hv e
      rw [h1, h2] at this
      exact this
    obtain ⟨hc, hM⟩ := card_hopf_u5two hGA hm
    haveI : Group.IsPerfect (Q ⧸ Subgroup.center Q) := Group.isPerfect_def.mpr hc
    have hdiv : Nat.card p.ker ∣ 1 := by
      rw [← hM]
      exact card_ker_dvd_hopfMultiplier p hp hpc
    obtain ⟨E, hE, hE4⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_e81_of_catalog_u52
      (⟨i, hU5, ⟨eS⟩⟩ : catalogIs (Q ⧸ Subgroup.center Q) S9.isU5two)
    refine ⟨fun h3 => ?_, fun hn => ?_⟩
    · rw [← hker_card] at h3
      have h1' : Nat.card p.ker = 1 := Nat.dvd_one.1 hdiv
      rw [h1'] at h3
      norm_num at h3
    · rw [← hker_card] at hn
      obtain ⟨W, hW, hWc⟩ := exists_elemAbelian_lift p hp hn hE
      exact ⟨W, hW, hWc.trans hE4⟩
  ·
    obtain ⟨q, hv, hq2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.U62RankSound.lieIndex_isU6two
      (⟨i, hU6, ⟨eS⟩⟩ : catalogIs (Q ⧸ Subgroup.center Q) S9.isU6two)
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq2.trans (by norm_num))
    have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .PSU 6 2 1 := by
      have := CFSG.LocalAnalysis.GLTheoremA.lieModel_twistedA' 5 q hv e
      rw [h1, h2] at this
      exact this
    obtain ⟨hc, hM⟩ := card_hopf_u6two hGA hm
    haveI : Group.IsPerfect (Q ⧸ Subgroup.center Q) := Group.isPerfect_def.mpr hc
    obtain ⟨K, hKF, hKfin, hK4, ⟨f⟩⟩ := classical_u6 hm
    refine ⟨fun h3 => ?_, fun hn => ?_⟩
    · rw [← hker_card] at h3
      exact rank5_of_u6 hK4 f hM p hp hpc h3
    · rw [← hker_card] at hn
      exact rank4_of_u6 hK4 f p hp hn

section Holds


theorem u42RankAt_holds : U42RankAt :=
  u42RankAt_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat
