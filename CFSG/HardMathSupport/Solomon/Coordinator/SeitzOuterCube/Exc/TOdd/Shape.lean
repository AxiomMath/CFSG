module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.Par
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF1

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.Open
open CFSG.RankThree.PartTwo.Sec19

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd


variable {ℓ f : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem conj_injective_odd (P : D4ParOdd ℓ f X σ) :
    Function.Injective (MulAut.conj : C0 σ →* MulAut (C0 σ)) :=
  mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.D4 X σ)

theorem sigma_ne_one_odd (P : D4ParOdd ℓ f X σ) : σ ≠ 1 := by
  intro h1
  have key : ∀ c : X, c ^ (ℓ ^ f) = c := fun c => by
    have h := P.frob c
    rw [h1] at h
    exact h.symm
  have h2 : 2 ≤ ℓ ^ f := le_trans (by norm_num) P.five_le
  have hle : Nat.card X ≤ ℓ ^ f := card_le_of_forall_pow_eq_self X (ℓ ^ f) h2 key
  rw [P.card] at hle
  exact absurd hle (not_le.2 (nf1_lt_pow_three h2))

theorem exists_theta_odd (P : D4ParOdd ℓ f X σ) :
    ∃ Θ : MulAut (C0 σ) →* (X ≃+* X),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Θ.ker = (MulAut.conj : C0 σ →* MulAut (C0 σ)).range ∧
      (∀ α : MulAut (C0 σ), ∃ g δ, α = MulAut.conj g * fieldActor σ δ) := by
  obtain ⟨-, hdec, ⟨Θ, hΘ, -, hker, -⟩, -, -, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form P.prime P.ne_two P.one_le X P.card σ P.frob
  refine ⟨Θ, hΘ, hker, fun α => ?_⟩
  obtain ⟨⟨g, δ⟩, hgδ⟩ := (hdec α).exists
  exact ⟨g, δ, hgδ⟩

theorem gal_cube_cases_odd (P : D4ParOdd ℓ f X σ) (ψ : X ≃+* X) (hψ : ψ ^ 3 = 1) :
    ψ = 1 ∨ ψ = σ ∨ ψ = σ ^ 2 := by
  obtain ⟨-, -, -, hcyc, hcard3, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form P.prime P.ne_two P.one_le X P.card σ P.frob
  haveI : Finite (X ≃+* X) :=
    Nat.finite_of_card_ne_zero (by rw [hcard3]; have := P.one_le; omega)
  haveI := hcyc
  have hσ1 : σ ≠ 1 := sigma_ne_one_odd P
  exact mem_of_cube_eq_one_cyclic σ P.sigma_pow_three hσ1 (nf1_sq_ne_one σ P.sigma_pow_three hσ1)
    ψ hψ

theorem shape_of_mem_E_odd (P : D4ParOdd ℓ f X σ) {E : Subgroup (MulAut (C0 σ))}
    (hE : CFSG.Open.IsElemAbelian 3 E) :
    ∀ y ∈ E, ∃ (g : C0 σ) (j : ℕ), y = MulAut.conj g * tauAut σ ^ j := by
  intro y hy
  obtain ⟨Θ, hΘ, -, hdec⟩ := exists_theta_odd P
  obtain ⟨g, δ, hgδ⟩ := hdec y
  have hy3 : y ^ 3 = 1 := hE.2 y hy
  have hδ : δ = Θ y := (hΘ y g δ hgδ).symm
  have hΘ3 : Θ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  obtain ⟨e, he⟩ : ∃ e : ℕ, δ = σ ^ e := by
    rcases gal_cube_cases_odd P (Θ y) hΘ3 with h | h | h
    · exact ⟨0, by rw [hδ, h, pow_zero]⟩
    · exact ⟨1, by rw [hδ, h, pow_one]⟩
    · exact ⟨2, by rw [hδ, h]⟩
  refine ⟨g, e, ?_⟩
  have hpow : fieldActor (t := TwistTag.D4) σ (σ ^ e) = tauAut σ ^ e :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ e
  rw [hgδ, he, hpow]

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
