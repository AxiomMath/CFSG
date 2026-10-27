module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExc2Classes
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6GraphMain

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

set_option linter.unusedSectionVars false


theorem a6_E6_graph_coset_false {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) {α : MulAut (adjointGroup TwistTag.E6.tag K)}
    {g : adjointGroup TwistTag.E6.tag K} {a : Fin TwistTag.E6.tag.rank → Kˣ}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag K, (α h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
        diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹ *
          (rootDiagUnit TwistTag.E6.tag a)⁻¹ * (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hα : α ^ 2 = 1)
    (S : Subgroup ↥(fixedSubgroup α))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (eS : S ≃* alternatingGroup (Fin 6)) : False := by
  classical
  have hf := (one_le_and_three_le_of_card hp hp2 hK).1
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K (AlgebraicClosure K)
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨x, hxR, hx2, ⟨Φ⟩⟩ := exists_mulEquiv_E6_graph_coset_fixed hK hKodd hαg hα
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS'⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_normal_simple_of_mulEquiv Φ S hSn hSs hSnab
  exact a6_E6_graph_coset_core_false p hp2 hf (AlgebraicClosure K) hk 0 (Or.inl rfl) hxR hx2 S'
    hS'n hS's hS'nab (eS'.symm.trans eS)

theorem a6_E6_false {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (β : MulAut (adjointGroup Tag.E6 F)) (hβ2 : β ^ 2 = 1)
    (S : Subgroup (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup Tag.E6 F))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (eS : S ≃* alternatingGroup (Fin 6)) : False := by
  classical
  have hf : 1 ≤ f := (one_le_and_three_le_of_card hp hp2 hF).1
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, hexist⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) F
  obtain ⟨g, a, σ, ε, hexpr⟩ := hexist β
  obtain ⟨-, -, -, -, hsq, hfacts⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) F
  have hσ2 : σ ^ 2 = 1 := hsq β g a σ ε hexpr hβ2
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h := ε.2
    change (ε : ℕ) < 2 at h
    omega
  have hQ : exactQ Tag.E6 F ε = (diagramMap TwistTag.E6 F : ModGL Tag.E6 F) ^ (ε : ℕ) := rfl
  have hQ0 : (ε : ℕ) = 0 → exactQ Tag.E6 F ε = 1 := fun h0 => by
    rw [hQ, h0, pow_zero]
    rfl
  have hQ1 : (ε : ℕ) = 1 → exactQ Tag.E6 F ε = (diagramMap TwistTag.E6 F : ModGL Tag.E6 F) :=
    fun h0 => by rw [hQ, h0, pow_one]
  by_cases hσ : σ = 1
  · subst hσ
    have h1 : ∀ h : adjointGroup Tag.E6 F, Units.map (entrywiseHom (1 : F ≃+* F).toRingHom)
        (h : ModGL Tag.E6 F) = h := fun h => Units.ext (entrywise_id _)
    rcases hε with h0 | h0
    · refine a6_inner_diagonal_false (Or.inr (Or.inr (Or.inl rfl))) hodd (g := g) (a := a)
        (fun h => ?_) hβ2 S hSn hSs hSnab eS
      rw [hexpr h, hQ0 h0, h1 h, inv_one, mul_one, mul_one]
    · refine a6_E6_graph_coset_false hp hp2 hF (g := g) (a := a) (fun h => ?_) hβ2 S hSn hSs
        hSnab eS
      have h2 := hexpr h
      rw [hQ1 h0, h1 h] at h2
      exact h2
  · obtain ⟨hfe, hσc, -⟩ := hfacts p f hp hf hF σ hσ2 hσ
    obtain ⟨e₀, rfl⟩ : ∃ e₀, f = 2 * e₀ := ⟨f / 2, (Nat.two_mul_div_two_of_even hfe).symm⟩
    have he₀ : 1 ≤ e₀ := by omega
    have hF' : Nat.card F = (p ^ e₀) ^ 2 := by rw [hF, ← pow_mul, mul_comm]
    have hσe : ∀ c, σ c = c ^ (p ^ e₀) := fun c => by
      rw [hσc, Nat.mul_div_cancel_left e₀ two_pos]
    rcases hε with h0 | h0
    · refine a6_quadratic_field_coset_false hp hp2 he₀ hF' σ hσe (g := g) (a := a) (fun h => ?_)
        hβ2 S hSn hSs hSnab eS
      rw [hexpr h, hQ0 h0, inv_one, mul_one, mul_one]
    · refine a6_E6_graph_field_coset_false hp hp2 he₀ hF' σ hσe (g := g) (a := a) (fun h => ?_)
        hβ2 S hSn hSs hSnab eS
      have h2 := hexpr h
      rw [hQ1 h0] at h2
      exact h2

end CFSG.ComponentClassification.CatFC
