module

public import CFSG.ClassicalInvolution.Balance.BootstrapExoticD4
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedD4

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.TwistedD4
open scoped MatrixGroups

section Hom

variable {K : Type} [Field K] (σ : K →+* K)

theorem exists_hom_range_long_trialityD4 (hσ : ∀ c, σ (σ (σ c)) = c)
    {n : Fin (twistedDatum σ).rank → ↥(twistedGroup σ)}
    {H : Fin (twistedDatum σ).rank → Subgroup ↥(twistedGroup σ)}
    (hct : IsCTGroupDatum (coxeterMatrix (twistedDatum σ).isFiniteType).toCoxeterSystem
      (weylAction (twistedDatum σ).isFiniteType) (twistedDatum σ).roots
      (twistedDatum σ).rootGroup n H)
    (g : ↥(twistedGroup σ)) (w : WeylGroup .G2) :
    ∃ ι : SL(2, fixedField σ) →* ↥(twistedGroup σ),
      ι.range = conjSub g ((twistedDatum σ).rootGroup (w • Pi.single (ng 0) 1) ⊔
        (twistedDatum σ).rootGroup (-(w • Pi.single (ng 0) 1))) := by
  obtain ⟨h, hh⟩ := ModelFacts.exists_map_conj_rankOne hct w
  have hb : (Pi.single (ng 0) 1 : Fin Tag.G2.rank → ℤ) ∈ (twistedDatum σ).roots := by
    rw [twistedDatum_roots]
    exact isRoot_single .G2 (ng 0)
  have h2 : (twistedDatum σ).rootGroup (w • Pi.single (ng 0) 1) ⊔
      (twistedDatum σ).rootGroup (-(w • Pi.single (ng 0) 1)) =
      (rankOne (twistedRootGroup σ) (ng 0)).map (MulAut.conj h).toMonoidHom := (hh _ hb).symm
  refine ⟨((MulAut.conj (g * h)).toMonoidHom).comp (slLong σ hσ), ?_⟩
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (g * h)).toMonoidHom := MonoidHom.ext fun y => by simp [mul_assoc]
  rw [MonoidHom.range_comp, ← ModelFacts.rankOne_long_eq_range hσ]
  unfold conjSub
  rw [h2, Subgroup.map_map _ (MulAut.conj g).toMonoidHom (MulAut.conj h).toMonoidHom, hcomp]

end Hom

section Model

variable {p : ℕ} [hp : Fact p.Prime]

theorem fundamental_trialityD4_sl2_range {n e : ℕ} (hadm : StatedLieAdmissible .trialityD4 n p e) :
    ∀ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e hp.out).D,
      (∃ ι : SL(2, fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) →*
          (modelUniv .trialityD4 n p e hp.out).K, ι.range = R) ∨
        ∃ ι : SL(2, GaloisField p (3 * e)) →* (modelUniv .trialityD4 n p e hp.out).K,
          ι.range = R := by
  intro R hR
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    hK (fun c => iterateFrobenius_def p e c)
  obtain ⟨_, _, hct, -⟩ := ModelFacts.hasBruhatDatum .trialityD4 n p e hp.out trivial hadm
  have hroot : IsRoot .G2 γ := by
    have h : γ ∈ (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)).roots := by
      rcases hγ with h | ⟨h', -⟩ | ⟨-, h⟩
      · exact h.1
      · exact absurd h' (by decide)
      · exact h
    rwa [twistedDatum_roots] at h
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hroot
  by_cases hj : j = ng 0
  · subst hj
    subst hw
    left
    exact exists_hom_range_long_trialityD4 _ hσ hct g w
  · have hj' : j = ng 1 := by
      fin_cases j
      · exact absurd rfl hj
      · rfl
    subst hj'
    subst hw
    right
    exact exists_hom_range_short_trialityD4 _ hσ hct g w

theorem fundamental_trialityD4_perfect_or_long {n e : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 n p e) :
    ∀ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e hp.out).D,
      R ≤ ⁅R, R⁆ ∨
        ∃ ι : SL(2, fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) →*
          (modelUniv .trialityD4 n p e hp.out).K, ι.range = R := by
  intro R hR
  rcases fundamental_trialityD4_sl2_range hadm R hR with h | ⟨ι, hι⟩
  · exact Or.inr h
  · left
    have he : 1 ≤ e := hadm.2.1
    have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
      rw [GaloisField.card p (3 * e) (by omega), pow_mul']
    have h2 : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) p)
    have h4S : 4 ≤ Nat.card (GaloisField p (3 * e)) := by
      rw [hK]
      exact four_le_pow_three h2
    have hr := ModelFacts.fundPerfect_range_le_commutator
      (CFSG.ClassicalInvolution.sl2_isPerfect h4S) ι
    rw [hι] at hr
    exact hr

theorem false_of_commuting_pair_trialityD4 {n e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .trialityD4 n p e) {X : Type} [Group X]
    (ψ : (modelUniv .trialityD4 n p e hp.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv .trialityD4 n p e hp.out).K)
    {R₁ R₂ : Subgroup (modelUniv .trialityD4 n p e hp.out).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e hp.out).D)
    (hperf₂ : ⁅R₂, R₂⁆ = R₂) {z₁ z₂ : X} (hz₁ : z₁ ∈ R₁.map ψ) (hz₂ : z₂ ∈ R₂.map ψ)
    (hc₂ : ∀ y ∈ R₂.map ψ, z₂ * y = y * z₂) (hc₂₁ : ∀ y ∈ R₂.map ψ, z₁ * y = y * z₁)
    {F : Subgroup X} (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) {f₁ f₂ : X} (hf₁ : f₁ ∈ F)
    (hf₂ : f₂ ∈ F) (hf₁1 : f₁ ≠ 1) (hf₂1 : f₂ ≠ 1) (hf₁₂ : f₁ ≠ f₂)
    (hact₁ : ∀ y ∈ ψ.range, f₁ * y * f₁⁻¹ = z₁ * y * z₁⁻¹)
    (hact₂ : ∀ y ∈ ψ.range, f₂ * y * f₂⁻¹ = z₂ * y * z₂⁻¹) : False := by
  have hnc := Bootstrap.fundamentalSubgroups_eq_one_of_central (t := .trialityD4) (n := n)
    (p := p) (e := e) trivial hadm (by simp)
  have he : 1 ≤ e := hadm.2.1
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
  have hsq : c₁ * c₁ = 1 := by
    have hff : f₁ * f₁ = 1 := hF2 f₁ hf₁
    refine hnc R₁ hR₁ (c₁ * c₁) (R₁.mul_mem hc₁R hc₁R) fun y => ?_
    apply hker
    rw [MonoidHom.mem_ker]
    have h1' : f₁ * ψ y * f₁⁻¹ = ψ c₁ * ψ y * (ψ c₁)⁻¹ := hact₁ (ψ y) ⟨y, rfl⟩
    have h2' : f₁ * (ψ c₁ * ψ y * (ψ c₁)⁻¹) * f₁⁻¹ =
        ψ c₁ * (ψ c₁ * ψ y * (ψ c₁)⁻¹) * (ψ c₁)⁻¹ := by
      have := hact₁ (ψ (c₁ * y * c₁⁻¹)) ⟨_, rfl⟩
      simpa only [map_mul, map_inv] using this
    have h3 : ψ y = ψ c₁ * (ψ c₁ * ψ y * (ψ c₁)⁻¹) * (ψ c₁)⁻¹ := by
      rw [← h2', ← h1']
      have e1 : f₁ * (f₁ * ψ y * f₁⁻¹) * f₁⁻¹ = (f₁ * f₁) * ψ y * (f₁ * f₁)⁻¹ := by group
      rw [e1, hff]
      simp
    simp only [map_mul, map_inv]
    calc ψ c₁ * ψ c₁ * ψ y * (ψ c₁ * ψ c₁)⁻¹ * (ψ y)⁻¹
        = (ψ c₁ * (ψ c₁ * ψ y * (ψ c₁)⁻¹) * (ψ c₁)⁻¹) * (ψ y)⁻¹ := by group
      _ = 1 := by rw [← h3]; group
  have cent : ∀ {c : (modelUniv .trialityD4 n p e hp.out).K},
      (∀ y ∈ R₂.map ψ, ψ c * y = y * ψ c) → ∀ r ∈ R₂, c * r = r * c := by
    intro c hc r hr
    have h := Models.Transfer.mem_centralizer_of_map (θ := ψ) hker hperf₂ (g := c)
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm)
    exact (Subgroup.mem_centralizer_iff.mp h r hr).symm
  have hc : c₂ = c₁ :=
    ModelFacts.trialityD4_eq_of_central_in_perfect p e hp2 he hperf₂ hsq h1 h2 hc₂R (cent hc₂)
      (cent hc₂₁)
  refine hfaith (f₂⁻¹ * f₁) (F.mul_mem (F.inv_mem hf₂) hf₁) ?_ fun x hx => ?_
  · intro h
    exact hf₁₂ (inv_mul_eq_one.1 h).symm
  · have e1 := hact₁ x hx
    have e2 := hact₂ x hx
    rw [← hc] at e1
    have e3 : f₁ * x * f₁⁻¹ = f₂ * x * f₂⁻¹ := e1.trans e2.symm
    have e4 : f₁ * x = f₂ * x * f₂⁻¹ * f₁ := by
      rw [← e3]
      group
    calc f₂⁻¹ * f₁ * x = f₂⁻¹ * (f₁ * x) := by group
      _ = x * (f₂⁻¹ * f₁) := by
        rw [e4]
        group

end Model

end CFSG.ClassicalInvolution.Balance.Q27
