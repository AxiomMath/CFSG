module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevOrth
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevLin
import CFSG.RankThree.CentralLift.ClassicalScalarCover

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedScalars)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv statedOmega_eq_comap)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LocalAnalysis.RankThreeUC.S15

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

theorem exists_quadForm_ne_zero_of_witt (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ v, Q v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT3, -⟩ := hT
  have hall : ∀ x : ι → K, x = 0 := fun x =>
    hQ.1 x fun y => by
      simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hcon]
  have hT0 : T = ⊥ := by
    ext x
    simp [hall x]
  rw [hT0, finrank_bot] at hT3
  omega

theorem pRank_statedOmega_eq_orthogonal_of_witt (hQ₀ : ⇑Q = Q₀)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedOmega Q₀)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set Ω₀ : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) := ⁅O, O⁆ with hΩ₀
  have hΩO : Ω₀ ≤ O := by
    rw [hΩ₀, Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem h₁ h₂) (O.inv_mem h₁)) (O.inv_mem h₂)
  have hMeq : StatedOmega Q₀ = Ω₀.comap (toLinEquiv ι K).toMonoidHom := statedOmega_eq_comap hQ₀
  have e2 : ↥(StatedOmega Q₀) ≃* ↥Ω₀ :=
    (MulEquiv.subgroupCongr hMeq).trans
      ((((toLinEquiv ι K).subgroupMap (Ω₀.comap (toLinEquiv ι K).toMonoidHom))).trans
        (MulEquiv.subgroupCongr
          (Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective Ω₀)))
  let N : Subgroup ↥O := Ω₀.subgroupOf O
  have e3 : ↥(StatedOmega Q₀) ≃* ↥N := e2.trans (Subgroup.subgroupOfEquivOfLe hΩO).symm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e3]
  refine RankChevLinProof.pRank_top_eq_of_pow_mem N fun x hx => ?_
  have hodd : Odd (orderOf (x : (ι → K) ≃ₗ[K] (ι → K))) := by
    rw [Subgroup.orderOf_coe]
    rcases (Nat.dvd_prime hp.out).1 (orderOf_dvd_of_pow_eq_one hx) with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact hp.out.odd_of_ne_two hp2
  obtain ⟨-, -, -, -, -, -, hlift, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  exact hlift x.1 x.2 hodd

theorem pRank_statedProj_statedOmega_eq_orthogonal_of_witt (hQ₀ : ⇑Q = Q₀)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega Q₀))) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have hv := exists_quadForm_ne_zero_of_witt hQ hT
  have hZ : ¬ p ∣ Nat.card ((StatedScalars ι K).subgroupOf (StatedOmega Q₀)) := by
    intro h
    have h1 := CFSG.RankThree.CentralLift.card_statedScalars_subgroupOf_statedOmega_le_two hQ₀ hv
    have h2 := Nat.le_of_dvd Nat.card_pos h
    have h3 := hp.out.two_le
    omega
  refine (CFSG.SectionRank.pRank_quotient_eq _ hZ).trans ?_
  exact pRank_statedOmega_eq_orthogonal_of_witt hQ₀ hQ hT hp2

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
