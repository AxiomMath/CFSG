module

public import CFSG.ClassicalInvolution.Balance.Q27D4Balance
import CFSG.ClassicalInvolution.RouteD.NoG2D4Model

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance
open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open CFSG.Blueprint.Chevalley (TwistTag adjointGroup)

section Facts

@[expose] def InvolutoryAutInner (K : Type) [Group K] : Prop :=
  ∀ σ : K ≃* K, (∀ y, σ (σ y) = y) → ∃ u : K, ∀ y, σ y = u * y * u⁻¹

@[expose] def InvolutionOddCoreTrivial (K : Type) [Group K] : Prop :=
  ∀ u : K, u * u = 1 → u ≠ 1 → ∀ N : Subgroup K, N ≤ Subgroup.centralizer ({u} : Set K) →
    (∀ c ∈ Subgroup.centralizer ({u} : Set K), ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
      Odd (Nat.card N) → N = ⊥

@[expose] def InvolutionCentralizersGenerate (K : Type) [Group K] : Prop :=
  ∀ u₁ u₂ : K, u₁ * u₁ = 1 → u₂ * u₂ = 1 → u₁ ≠ 1 → u₂ ≠ 1 → u₁ ≠ u₂ → u₁ * u₂ = u₂ * u₁ →
    Subgroup.centralizer ({u₁} : Set K) ⊔ Subgroup.centralizer ({u₂} : Set K) ⊔
      Subgroup.centralizer ({u₁ * u₂} : Set K) = ⊤

end Facts

section Abstract

private theorem exists_two_ne_one_of_card_four {X : Type*} [Group X] {F : Subgroup X}
    (h4 : Nat.card F = 4) : ∃ x ∈ F, ∃ y ∈ F, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F
  have hc : 2 < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
  by_cases ha1 : a = 1
  · exact ⟨b, b.2, c, c.2, fun h => hab (ha1.trans (Subtype.ext h).symm),
      fun h => hac (ha1.trans (Subtype.ext h).symm), fun h => hbc (Subtype.ext h)⟩
  · by_cases hb1 : b = 1
    · exact ⟨a, a.2, c, c.2, fun h => ha1 (Subtype.ext h),
        fun h => hbc (hb1.trans (Subtype.ext h).symm), fun h => hac (Subtype.ext h)⟩
    · exact ⟨a, a.2, b, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
        fun h => hab (Subtype.ext h)⟩

variable {K : Type} [Group K] {X : Type} [Group X]

private theorem eq_of_forall_conj_eq (hZ : Subgroup.center K = ⊥) {a b : K}
    (h : ∀ y : K, a * y * a⁻¹ = b * y * b⁻¹) : a = b := by
  have hc : b⁻¹ * a ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h g]
      _ = (b⁻¹ * a) * g := by group
  rw [hZ] at hc
  exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hc)).symm

private theorem exists_inner_of_involution [Finite K] (hA : InvolutoryAutInner K) {ψ : K →* X}
    (hψ : Function.Injective ψ) {f : X} (hf2 : f * f = 1)
    (hmem : ∀ y : K, f * ψ y * f⁻¹ ∈ ψ.range) :
    ∃ u : K, ∀ y : K, f * ψ y * f⁻¹ = ψ (u * y * u⁻¹) := by
  choose g hg using fun y => MonoidHom.mem_range.mp (hmem y)
  have hgmul : ∀ a b, g (a * b) = g a * g b := fun a b => hψ (by
    simp only [map_mul, hg]
    group)
  let φ : K →* K := MonoidHom.mk' g hgmul
  have hφinj : Function.Injective φ := fun a b hab => hψ (by
    have h1 : ψ (g a) = ψ (g b) := congrArg ψ hab
    rw [hg, hg] at h1
    have h2 : f⁻¹ * (f * ψ a * f⁻¹) * f = f⁻¹ * (f * ψ b * f⁻¹) * f := by rw [h1]
    simpa [mul_assoc] using h2)
  let σ : K ≃* K := MulEquiv.ofBijective φ (Finite.injective_iff_bijective.mp hφinj)
  have hσ : ∀ y, ψ (σ y) = f * ψ y * f⁻¹ := hg
  have hσ2 : ∀ y, σ (σ y) = y := fun y => hψ (by
    rw [hσ, hσ]
    calc f * (f * ψ y * f⁻¹) * f⁻¹ = (f * f) * ψ y * (f * f)⁻¹ := by group
      _ = ψ y := by rw [hf2]; group)
  obtain ⟨u, hu⟩ := hA σ hσ2
  exact ⟨u, fun y => by rw [← hσ, hu]⟩

theorem deltaCentralizes_of_parts (hZ : Subgroup.center K = ⊥) (hA : InvolutoryAutInner K)
    (hB : InvolutionOddCoreTrivial K) (hC : InvolutionCentralizersGenerate K) [Finite X]
    (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) :
    ∀ d ∈ deltaCore F, ∀ x ∈ ψ.range, d * x = x * d := by
  classical
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have : Finite K := Finite.of_injective ψ hψ
  have hFinv : ∀ f ∈ F, f⁻¹ = f := fun f hf => inv_eq_of_mul_eq_one_right (hF2 f hf)
  have hFcomm : ∀ f ∈ F, ∀ g ∈ F, f * g = g * f := fun f hf g hg => by
    have h := hF2 (f * g) (F.mul_mem hf hg)
    have h' : f * g = (f * g)⁻¹ := (inv_eq_of_mul_eq_one_right h).symm
    rw [h', mul_inv_rev, hFinv f hf, hFinv g hg]
  have hmem : ∀ f ∈ F, ∀ y : K, f * ψ y * f⁻¹ ∈ ψ.range := fun f _ y =>
    hnorm.conj_mem (ψ y) ⟨y, rfl⟩ f
  choose! u hu using fun f (hf : f ∈ F) => exists_inner_of_involution hA hψ (hF2 f hf) (hmem f hf)
  have hu1 : ∀ f ∈ F, f ≠ 1 → u f ≠ 1 := fun f hf hf1 h1 => by
    apply hfaith f hf hf1
    rintro _ ⟨y, rfl⟩
    have h := hu f hf y
    rw [h1] at h
    simp only [one_mul, inv_one, mul_one] at h
    calc f * ψ y = f * ψ y * f⁻¹ * f := by group
      _ = ψ y * f := by rw [h]
  have husq : ∀ f ∈ F, u f * u f = 1 := fun f hf => by
    refine eq_of_forall_conj_eq hZ fun y => hψ ?_
    calc ψ (u f * u f * y * (u f * u f)⁻¹)
        = ψ (u f * (u f * y * (u f)⁻¹) * (u f)⁻¹) := congrArg ψ (by group)
      _ = f * ψ (u f * y * (u f)⁻¹) * f⁻¹ := (hu f hf _).symm
      _ = f * (f * ψ y * f⁻¹) * f⁻¹ := by rw [hu f hf y]
      _ = (f * f) * ψ y * (f * f)⁻¹ := by group
      _ = ψ y := by rw [hF2 f hf]; group
      _ = ψ (1 * y * 1⁻¹) := by simp
  have humul : ∀ f ∈ F, ∀ g ∈ F, u (f * g) = u f * u g := fun f hf g hg => by
    refine eq_of_forall_conj_eq hZ fun y => hψ ?_
    calc ψ (u (f * g) * y * (u (f * g))⁻¹) = (f * g) * ψ y * (f * g)⁻¹ :=
          (hu _ (F.mul_mem hf hg) y).symm
      _ = f * (g * ψ y * g⁻¹) * f⁻¹ := by group
      _ = f * ψ (u g * y * (u g)⁻¹) * f⁻¹ := by rw [hu g hg y]
      _ = ψ (u f * (u g * y * (u g)⁻¹) * (u f)⁻¹) := hu f hf _
      _ = ψ (u f * u g * y * (u f * u g)⁻¹) := congrArg ψ (by group)
  have key : ∀ f ∈ F, f ≠ 1 → ∀ d ∈ deltaCore F, ∀ c ∈ Subgroup.centralizer ({u f} : Set K),
      d * ψ c = ψ c * d := by
    intro f hf hf1 d hd c hc
    have hdM : d ∈ oddCoreIn (Subgroup.centralizer ({f} : Set X)) :=
      mem_deltaCore_iff.mp hd f hf hf1
    have hψC : ∀ k ∈ Subgroup.centralizer ({u f} : Set K),
        ψ k ∈ Subgroup.centralizer ({f} : Set X) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hu f hf k
      have h2 : u f * k * (u f)⁻¹ = k := by
        rw [← Subgroup.mem_centralizer_singleton_iff.mp hk]
        group
      rw [h2] at h1
      calc ψ k * f = f * ψ k * f⁻¹ * f := by rw [h1]
        _ = f * ψ k := by group
    set N : Subgroup K := (oddCoreIn (Subgroup.centralizer ({f} : Set X))).comap ψ with hN
    have hNle : N ≤ Subgroup.centralizer ({u f} : Set K) := by
      intro k hk
      have hk' : ψ k ∈ Subgroup.centralizer ({f} : Set X) := oddCoreIn_le _ hk
      rw [Subgroup.mem_centralizer_singleton_iff] at hk' ⊢
      have h1 := hu f hf k
      have h2 : f * ψ k * f⁻¹ = ψ k := by rw [← hk']; group
      rw [h2] at h1
      have h3 : u f * k * (u f)⁻¹ = k := hψ h1.symm
      calc k * u f = u f * k * (u f)⁻¹ * u f := by rw [h3]
        _ = u f * k := by group
    have hNnorm : ∀ c' ∈ Subgroup.centralizer ({u f} : Set K), ∀ n ∈ N, c' * n * c'⁻¹ ∈ N := by
      intro c' hc' n hn
      have h : ψ (c' * n * c'⁻¹) = ψ c' * ψ n * (ψ c')⁻¹ := by simp
      show ψ (c' * n * c'⁻¹) ∈ oddCoreIn (Subgroup.centralizer ({f} : Set X))
      rw [h]
      exact conj_mem_oddCoreIn (hψC c' hc') hn
    have hNodd : Odd (Nat.card N) := by
      have h := Subgroup.card_comap_dvd_of_injective
        (oddCoreIn (Subgroup.centralizer ({f} : Set X))) ψ hψ
      exact (odd_card_oddCoreIn _).of_dvd_nat h
    have hNbot : N = ⊥ := hB (u f) (husq f hf) (hu1 f hf hf1) N hNle hNnorm hNodd
    have hcomm : d * ψ c * d⁻¹ * (ψ c)⁻¹ = 1 := by
      have hmem1 : d * ψ c * d⁻¹ * (ψ c)⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({f} : Set X)) := by
        have h := conj_mem_oddCoreIn (hψC c hc) hdM
        have h' := mul_mem hdM (inv_mem h)
        have e : d * (ψ c * d * (ψ c)⁻¹)⁻¹ = d * ψ c * d⁻¹ * (ψ c)⁻¹ := by group
        rwa [e] at h'
      have hmem2 : d * ψ c * d⁻¹ * (ψ c)⁻¹ ∈ ψ.range :=
        mul_mem (hnorm.conj_mem (ψ c) ⟨c, rfl⟩ d) (inv_mem ⟨c, rfl⟩)
      obtain ⟨k, hk⟩ := hmem2
      have hkN : k ∈ N := by
        show ψ k ∈ oddCoreIn (Subgroup.centralizer ({f} : Set X))
        rw [hk]
        exact hmem1
      rw [hNbot, Subgroup.mem_bot] at hkN
      rw [← hk, hkN, map_one]
    calc d * ψ c = d * ψ c * d⁻¹ * d := by group
      _ = ψ c * d := by rw [mul_inv_eq_one.mp hcomm]
  intro d hd x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨f₁, hf₁, f₂, hf₂, hf₁1, hf₂1, hf₁₂⟩ := exists_two_ne_one_of_card_four hcard
  have hf₃ : f₁ * f₂ ∈ F := F.mul_mem hf₁ hf₂
  have hf₃1 : f₁ * f₂ ≠ 1 := fun h => hf₁₂ ((eq_inv_of_mul_eq_one_left h).trans (hFinv f₂ hf₂))
  have hcomm₁₂ : u f₁ * u f₂ = u f₂ * u f₁ := by
    rw [← humul f₁ hf₁ f₂ hf₂, ← humul f₂ hf₂ f₁ hf₁, hFcomm f₁ hf₁ f₂ hf₂]
  have hne : u f₁ ≠ u f₂ := fun h => hu1 (f₁ * f₂) hf₃ hf₃1 (by
    rw [humul f₁ hf₁ f₂ hf₂, ← h]
    exact husq f₁ hf₁)
  have htop := hC (u f₁) (u f₂) (husq f₁ hf₁) (husq f₂ hf₂) (hu1 f₁ hf₁ hf₁1) (hu1 f₂ hf₂ hf₂1)
    hne hcomm₁₂
  have hS : ∀ f ∈ F, f ≠ 1 → Subgroup.centralizer ({u f} : Set K) ≤
      (Subgroup.centralizer ({d} : Set X)).comap ψ := fun f hf hf1 c hc => by
    show ψ c ∈ Subgroup.centralizer ({d} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (key f hf hf1 d hd c hc).symm
  have hle : (⊤ : Subgroup K) ≤ (Subgroup.centralizer ({d} : Set X)).comap ψ := by
    rw [← htop]
    refine sup_le (sup_le (hS f₁ hf₁ hf₁1) (hS f₂ hf₂ hf₂1)) ?_
    rw [← humul f₁ hf₁ f₂ hf₂]
    exact hS (f₁ * f₂) hf₃ hf₃1
  have hy : ψ y ∈ Subgroup.centralizer ({d} : Set X) := hle (Subgroup.mem_top y)
  exact (Subgroup.mem_centralizer_singleton_iff.mp hy).symm

end Abstract

section Model

variable {p : ℕ} [hp : Fact p.Prime]

set_option maxHeartbeats 400000 in
theorem involutoryAutInner_trialityD4 (hp2 : p ≠ 2) {n e : ℕ} (he : 1 ≤ e) (hodd : Odd e) :
    InvolutoryAutInner (modelUniv .trialityD4 n p e hp.out).K := by
  show InvolutoryAutInner ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
  set K0 := GaloisField p (3 * e) with hK0
  set σ := iterateFrobenius K0 p e with hσdef
  have hK3 : Nat.card K0 = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hfin : Finite K0 := Nat.finite_of_card_ne_zero (by
    rw [hK3]
    exact (pow_pos (pow_pos hp.out.pos e) _).ne')
  have hσ : ∀ c : K0, σ c = c ^ (p ^ e) := fun c => iterateFrobenius_def p e c
  let σK : K0 ≃+* K0 := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσK : σK.toRingHom = σ := RingHom.ext fun _ => rfl
  have h3 : (twistedGroup σ).map (adjointGroup d4 K0).subtype =
      graphFixedRootGroup TwistTag.D4 K0 σK.toRingHom := by
    rw [hσK]
    exact CFSG.ClassicalInvolution.RouteD.G2D4.map_twistedGroup_eq_graphFixedRootGroup p e hp2 he
  obtain ⟨-, -, ⟨Θ, -, -, hker, hinv⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp.out hp2 he K0 hK3 σK (fun c => hσ c)
  let e₁ := Subgroup.equivMapOfInjective (twistedGroup σ)
    (adjointGroup d4 K0).subtype (Subgroup.subtype_injective _)
  let e₂ := e₁.trans (MulEquiv.subgroupCongr h3)
  intro τ hτ
  let α : MulAut (graphFixedRootGroup TwistTag.D4 K0 σK.toRingHom) :=
    e₂.symm.trans (τ.trans e₂)
  have hα' : ∀ x, α (α x) = x := fun x => by
    show e₂ (τ (e₂.symm (e₂ (τ (e₂.symm x))))) = x
    rw [MulEquiv.symm_apply_apply, hτ, MulEquiv.apply_symm_apply]
  have hα : α ^ 2 = 1 := MulEquiv.ext fun x => by
    rw [pow_two]
    exact hα' x
  have hΘ : Θ α = 1 := by
    rcases hinv α hα with h | ⟨hev, -⟩
    · exact h
    · exact absurd hev (Nat.not_even_iff_odd.mpr hodd)
  have hmem : α ∈ Θ.ker := hΘ
  rw [hker] at hmem
  obtain ⟨g, hg⟩ := hmem
  have hαe : ∀ y, α (e₂ y) = e₂ (τ y) := fun y => by
    show e₂ (τ (e₂.symm (e₂ y))) = e₂ (τ y)
    rw [MulEquiv.symm_apply_apply]
  refine ⟨e₂.symm g, fun y => ?_⟩
  have h1 : e₂ (τ y) = g * e₂ y * g⁻¹ := by
    have h := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K0 σK.toRingHom) =>
      φ (e₂ y)) hg
    have h' : g * e₂ y * g⁻¹ = α (e₂ y) := h
    rw [h', hαe]
  have h2 : τ y = e₂.symm (g * e₂ y * g⁻¹) := by
    rw [← h1, MulEquiv.symm_apply_apply]
  have h4 : e₂.symm (g * e₂ y * g⁻¹) = e₂.symm g * y * (e₂.symm g)⁻¹ := by
    rw [map_mul e₂.symm, map_mul e₂.symm, map_inv e₂.symm, MulEquiv.symm_apply_apply]
  exact h2.trans h4

end Model

section Reduction

@[expose] def D4ThreeCentralizerFacts : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), StatedLieAdmissible .trialityD4 n p e → p ^ e = 3 →
    InvolutionOddCoreTrivial (modelUniv .trialityD4 n p e hp).K ∧
      InvolutionCentralizersGenerate (modelUniv .trialityD4 n p e hp).K

private theorem eq_one_of_pow_eq_three {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (h : p ^ e = 3) :
    e = 1 ∧ p = 3 := by
  have he1 : e = 1 := by
    by_contra hne
    have h2 : 2 ≤ e := by omega
    have : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos h2
    have : 2 * 2 ≤ p ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hp.two_le hp.two_le
    omega
  subst he1
  exact ⟨rfl, by simpa using h⟩

theorem deltaBalanceD4Three_of_facts (h : D4ThreeCentralizerFacts) : DeltaBalanceD4Three := by
  intro n p e hp hadm he3 X _ _ ψ hker hnorm F hcard hF2 hfaith d hd x hx
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨he1, hp3⟩ := eq_one_of_pow_eq_three hp he he3
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hB, hC⟩ := h n p e hp hadm he3
  exact deltaCentralizes_of_parts
    (CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) n he)
    (involutoryAutInner_trialityD4 hp2 he (by rw [he1]; exact odd_one)) hB hC ψ hker hnorm hcard
    hF2 hfaith d hd x hx

end Reduction

end CFSG.ClassicalInvolution.Balance.Q27
