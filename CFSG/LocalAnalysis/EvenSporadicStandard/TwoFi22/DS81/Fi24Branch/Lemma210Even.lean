module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCLieMult
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (lieSylowExponent)

theorem even_ker_lie_two_cases
    {Y Yh : Type} [Group Y] [Group Yh] [Finite Yh] (hperf : Group.IsPerfect Yh) (π : Yh →* Y)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Yh) (hk2 : Nat.card π.ker = 2)
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hm : Blueprint.LieModel Y t n 2 f) :
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) ∨
      (t = .PSU ∧ n = 4 ∧ f = 1) ∨ (t = .PSp ∧ n = 3 ∧ f = 1) ∨ (t = .G2 ∧ n = 0 ∧ f = 2) ∨
      (t = .F4 ∧ n = 0 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨
      (t = .PSU ∧ n = 6 ∧ f = 1) ∨ (t = .twistedB2 ∧ n = 0 ∧ f = 3) ∨
      (t = .twistedE6 ∧ n = 0 ∧ f = 1) ∨ (t = .PSL ∧ n = 3 ∧ f = 2) := by
  obtain ⟨-, ⟨e⟩⟩ := Milestones.cl_lit_griess_schur_multipliers_all_native_models Y t n 2 f hm
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hperf π hπ hker
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess Y).toEquiv,
    Nat.card_congr e.toEquiv, SectionRank.QTK.CoverB.card_generic_exceptional, hk2] at hdvd
  apply CFSG.ComponentClassification.GS82PumpInputs.even_exceptionalOrders_two
  rw [even_iff_two_dvd]
  exact Nat.Coprime.dvd_of_dvd_mul_left
    (Nat.coprime_two_left.mpr (CFSG.ComponentClassification.GS82PumpInputs.odd_genericOrders_two
      hadm)) hdvd

theorem ds81Lemma210_even
    {Y : Type} [Group Y] (heven : EvenLieType Y)
    (hext : ∃ (Yh : Type) (_ : Group Yh) (π : Yh →* Y), Function.Surjective π ∧
      commutator Yh = ⊤ ∧ π.ker ≤ Subgroup.center Yh ∧ Nat.card π.ker = 2)
    (h19 : 2 ^ 19 ∣ Nat.card Y) (h21 : ¬ 2 ^ 21 ∣ Nat.card Y) : False := by
  obtain ⟨t, n, f, hadm, hm⟩ := heven
  obtain ⟨hfin, -, hexp⟩ :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput Y t n 2 f hadm hm
  obtain ⟨Yh, _, π, hπ, hcomm, hker, hk2⟩ := hext
  have hYne : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  haveI : Finite Yh := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [CFSG.GH74.Generic.card_eq_card_mul_card_ker π hπ, hk2]
    omega
  have hcases := even_ker_lie_two_cases (Group.isPerfect_def.mpr hcomm) π hπ hker hk2 hadm hm
  have h19' : 19 ≤ lieSylowExponent t n * f := by
    rw [← hexp]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hYne).1 h19
  have h21' : lieSylowExponent t n * f < 21 := by
    rw [← hexp]
    by_contra hc
    exact h21 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hYne).2 (not_lt.1 hc))
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [lieSylowExponent] at h19' h21' <;> omega

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
