module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPair
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Commute
import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section Vacuous

theorem layerGenerationPairAt_of_shared_involution {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p e : ℕ} (hp : p.Prime)
    (hperf : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, ⁅R, R⁆ = R)
    (hnc : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, ∀ r ∈ R,
      (∀ y : (modelUniv t n p e hp).K,
        r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center (modelUniv t n p e hp).K) → r = 1)
    (hshare : ∀ R₁ ∈ fundamentalSubgroups t (modelUniv t n p e hp).D,
      ∀ R₂ ∈ fundamentalSubgroups t (modelUniv t n p e hp).D,
      ∀ c₁ ∈ R₁, ∀ c₂ ∈ R₂, (∀ r ∈ R₁, c₁ * r = r * c₁) → (∀ r ∈ R₂, c₂ * r = r * c₂) →
        (∀ r ∈ R₁, c₂ * r = r * c₂) → (∀ r ∈ R₂, c₁ * r = r * c₁) → c₁ * c₁ = 1 →
        c₂ * c₂ = 1 → c₁ ≠ 1 → c₂ ≠ 1 → c₁ = c₂) :
    LayerGenerationPairAt t n p e hp := by
  intro X _ _ ψ hker _ R₁ hR₁ R₂ hR₂ z₁ hz₁ z₂ hz₂ hc₁ hc₂ hc₁₂ hc₂₁ F hF4 hF2 hFN hfaith f₁ hf₁
    f₂ hf₂ hf₁1 hf₂1 hf₁₂ hact₁ hact₂
  exfalso
  have cent : ∀ {R : Subgroup (modelUniv t n p e hp).K} {c : (modelUniv t n p e hp).K},
      ⁅R, R⁆ = R → (∀ y ∈ R.map ψ, ψ c * y = y * ψ c) → ∀ r ∈ R, c * r = r * c := by
    intro R c hR hc r hr
    have h := Models.Transfer.mem_centralizer_of_map (θ := ψ) hker hR (g := c)
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm)
    exact (Subgroup.mem_centralizer_iff.mp h r hr).symm
  have hsq : ∀ (R : Subgroup (modelUniv t n p e hp).K), R ∈ fundamentalSubgroups t
      (modelUniv t n p e hp).D → ∀ (f : X) (c : (modelUniv t n p e hp).K), c ∈ R → f ∈ F →
      (∀ y ∈ ψ.range, f * y * f⁻¹ = ψ c * y * (ψ c)⁻¹) → c * c = 1 := by
    intro R hR f c hcR hf hact
    have hff : f * f = 1 := hF2 f hf
    refine hnc R hR (c * c) (R.mul_mem hcR hcR) fun y => ?_
    apply hker
    rw [MonoidHom.mem_ker]
    have h1 : f * ψ y * f⁻¹ = ψ c * ψ y * (ψ c)⁻¹ := hact (ψ y) ⟨y, rfl⟩
    have h2 : f * (ψ c * ψ y * (ψ c)⁻¹) * f⁻¹ = ψ c * (ψ c * ψ y * (ψ c)⁻¹) * (ψ c)⁻¹ := by
      have := hact (ψ (c * y * c⁻¹)) ⟨_, rfl⟩
      simpa only [map_mul, map_inv] using this
    have h3 : ψ y = ψ c * (ψ c * ψ y * (ψ c)⁻¹) * (ψ c)⁻¹ := by
      rw [← h2, ← h1]
      have e1 : f * (f * ψ y * f⁻¹) * f⁻¹ = (f * f) * ψ y * (f * f)⁻¹ := by group
      rw [e1, hff]
      simp
    simp only [map_mul, map_inv]
    calc ψ c * ψ c * ψ y * (ψ c * ψ c)⁻¹ * (ψ y)⁻¹
        = (ψ c * (ψ c * ψ y * (ψ c)⁻¹) * (ψ c)⁻¹) * (ψ y)⁻¹ := by group
      _ = 1 := by rw [← h3]; group
  obtain ⟨c₁, hc₁R, rfl⟩ := hz₁
  obtain ⟨c₂, hc₂R, rfl⟩ := hz₂
  by_cases h1 : c₁ = 1
  · refine hfaith f₁ hf₁ hf₁1 fun x hx => ?_
    have := hact₁ x hx
    rw [h1, map_one, one_mul, inv_one, mul_one] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  by_cases h2 : c₂ = 1
  · refine hfaith f₂ hf₂ hf₂1 fun x hx => ?_
    have := hact₂ x hx
    rw [h2, map_one, one_mul, inv_one, mul_one] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  have hc : c₁ = c₂ := hshare R₁ hR₁ R₂ hR₂ c₁ hc₁R c₂ hc₂R (cent (hperf R₁ hR₁) hc₁)
    (cent (hperf R₂ hR₂) hc₂) (cent (hperf R₁ hR₁) hc₁₂) (cent (hperf R₂ hR₂) hc₂₁)
    (hsq R₁ hR₁ f₁ c₁ hc₁R hf₁ hact₁) (hsq R₂ hR₂ f₂ c₂ hc₂R hf₂ hact₂) h1 h2
  refine hfaith (f₂⁻¹ * f₁) (F.mul_mem (F.inv_mem hf₂) hf₁) ?_ fun x hx => ?_
  · intro h
    exact hf₁₂ (inv_mul_eq_one.1 h).symm
  · have e1 := hact₁ x hx
    have e2 := hact₂ x hx
    rw [hc] at e1
    have e3 : f₁ * x * f₁⁻¹ = f₂ * x * f₂⁻¹ := e1.trans e2.symm
    have e4 : f₁ * x = f₂ * x * f₂⁻¹ * f₁ := by
      rw [← e3]
      group
    calc f₂⁻¹ * f₁ * x = f₂⁻¹ * (f₁ * x) := by group
      _ = x * (f₂⁻¹ * f₁) := by
        rw [e4]
        group

end Vacuous

section D4

theorem fundamentalSubgroups_commutator_eq {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p e : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, ⁅R, R⁆ = R := fun R hR =>
  le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
    R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy))
    (ModelFacts.fundPerfect_core t n p e hp2 hfund hadm h4 R hR)

theorem fundamentalSubgroups_eq_one_of_central {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p e : ℕ} [Fact p.Prime] (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hne : ¬(t = .PSL ∧ n = 2)) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, ∀ r ∈ R,
      (∀ y : (modelUniv t n p e Fact.out).K,
        r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center (modelUniv t n p e Fact.out).K) → r = 1 :=
  ModelFacts.fundNoncentral_core t n p e hfund hadm hne

theorem layerGenerationPairAt_trialityD4 {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ e) (hadm : StatedLieAdmissible .trialityD4 n p e) :
    LayerGenerationPairAt .trialityD4 n p e hp := by
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  have hperf := fundamentalSubgroups_commutator_eq (t := .trialityD4) (n := n) hp2 trivial hadm
    (by omega)
  have hnc := fundamentalSubgroups_eq_one_of_central (t := .trialityD4) (n := n) (p := p) (e := e)
    trivial hadm (by simp)
  refine layerGenerationPairAt_of_shared_involution hp hperf hnc ?_
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁R c₂ hc₂R hc₁c hc₂c hc₁₂ hc₂₁ hc₁sq hc₂sq hc₁1 hc₂1
  exact (ModelFacts.trialityD4_eq_of_central_in_perfect p e hp2 he (hperf R₂ hR₂) hc₁sq hc₁1 hc₂1
    hc₂R hc₂c hc₂₁).symm

end D4

end CFSG.ClassicalInvolution.Balance.Bootstrap
