module

public import CFSG.GH74.Generic.BProg.B3.S3T5L3Tmpl
public import CFSG.GH74.Generic.BProg.B3.S3T5L3Fix
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphRed

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T5L3

open Matrix Subgroup CFSG CFSG.Assembly.Dichotomy CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.Signalizer
open scoped MatrixGroups

theorem map_conj_eq_of_twist {G : Type*} [Group G] (ψ : G →* G) {M h : G}
    (hz : ∀ x, (M⁻¹ * ψ M) * x = x * (M⁻¹ * ψ M)) (hh : ψ h = h) :
    ψ (M * h * M⁻¹) = M * h * M⁻¹ := by
  obtain ⟨z, hz', hzM⟩ : ∃ z, (∀ x, z * x = x * z) ∧ ψ M = M * z := ⟨_, hz, by group⟩
  rw [map_mul, map_mul, map_inv, hh, hzM]
  calc M * z * h * (M * z)⁻¹ = M * (z * h) * z⁻¹ * M⁻¹ := by group
    _ = M * (h * z) * z⁻¹ * M⁻¹ := by rw [hz' h]
    _ = M * h * M⁻¹ := by group

variable {K : Type} [Group K]

theorem congr_apply_apply {P : Type} [Group P] (e₁ : K ≃* P) (α : MulAut K) (k : K) :
    MulAut.congr e₁ α (e₁ k) = e₁ (α k) := by
  simp [MulAut.congr_apply]

variable [Finite K]

theorem involutionOddCore_eq_bot_of_model {P : Type} [Group P] [Finite P] (e₁ : K ≃* P)
    (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1) {H : Subgroup (MulAut K)}
    (hH : (MulAut.conj : K →* MulAut K).range ≤ H) (u : H) {γ : MulAut P}
    (hγ : MulAut.congr e₁ (u : MulAut K) = γ) (Q : Subgroup P) [IsSimpleGroup Q]
    (hQfix : ∀ q ∈ Q, γ q = q) (hQn : ∀ s, γ s = s → ∀ q ∈ Q, s * q * s⁻¹ ∈ Q)
    (hCQ : ∀ y : P, (∀ q ∈ Q, y * q = q * y) → y = 1)
    (hB : ∀ (β : MulAut P) (m : ℕ), Odd m → β ^ m = 1 → (∀ q ∈ Q, β q = q) → β = 1) :
    involutionOddCore u = ⊥ := by
  have hfix : ∀ k, γ (e₁ k) = e₁ k ↔ (u : MulAut K) k = k := fun k => by
    rw [← hγ, congr_apply_apply, e₁.injective.eq_iff]
  have hfix' : ∀ s, γ s = s → (u : MulAut K) (e₁.symm s) = e₁.symm s := fun s hs => by
    rw [← hfix, MulEquiv.apply_symm_apply]; exact hs
  refine involutionOddCore_eq_bot_of_fix hZ hH u (fun N hNodd hNfix hNn => ?_)
    fun w hw hwfix => ?_
  · let S : Subgroup P := MonoidHom.eqLocus γ.toMonoidHom (MonoidHom.id P)
    have hS : ∀ s, s ∈ S ↔ γ s = s := fun s => Iff.rfl
    have h := eq_bot_of_simple_normal (S := S) (N := N.map e₁.toMonoidHom)
      (fun q hq => (hS q).2 (hQfix q hq)) (fun s hs q hq => hQn s ((hS s).1 hs) q hq) hCQ
      ?_ ?_ ?_
    · exact (map_eq_bot_iff_of_injective N e₁.injective).1 h
    · rintro _ ⟨k, hk, rfl⟩
      exact (hS _).2 ((hfix k).2 (hNfix k hk))
    · rintro s hs _ ⟨k, hk, rfl⟩
      refine ⟨e₁.symm s * k * (e₁.symm s)⁻¹, hNn _ (hfix' s ((hS s).1 hs)) k hk, ?_⟩
      simp
    · rwa [card_map_of_injective e₁.injective]
  · have hβ : MulAut.congr e₁ w ^ orderOf w = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have h1 := hB (MulAut.congr e₁ w) (orderOf w) hw hβ fun q hq => by
      calc MulAut.congr e₁ w q = MulAut.congr e₁ w (e₁ (e₁.symm q)) := by
            rw [e₁.apply_symm_apply]
        _ = e₁ (w (e₁.symm q)) := congr_apply_apply e₁ w _
        _ = q := by rw [hwfix _ (hfix' q (hQfix q hq)), e₁.apply_symm_apply]
    exact (MulAut.congr e₁).injective (by rw [h1, map_one])

variable {F : Type} [Field F] [Finite F]

theorem involutionOddCore_eq_bot_of_proj (e₁ : K ≃* projectiveSL 3 F)
    (hZ : ∀ z : K, (∀ x, z * x = x * z) → z = 1) {H : Subgroup (MulAut K)}
    (hH : (MulAut.conj : K →* MulAut K).range ≤ H) (u : H) {γ : MulAut (projectiveSL 3 F)}
    (hγ : MulAut.congr e₁ (u : MulAut K) = γ) (ψ : SL(3, F) →* SL(3, F))
    (hψ : ∀ g, γ (LinearFlag.proj 3 F g) = LinearFlag.proj 3 F (ψ g))
    (Ω : Subgroup SL(3, F)) (hΩ : ∀ g, g ∈ Ω ↔ ψ g = g) (hperf : Group.IsPerfect Ω)
    [IsSimpleGroup (Ω.map (LinearFlag.proj 3 F))] {R : Set SL(3, F)} (hRΩ : R ⊆ Ω)
    (hRfix : ∀ ρ : F ≃+* F, ∀ g ∈ R, (g : Matrix (Fin 3) (Fin 3) F).map ρ = g)
    (hRcomm : ∀ T : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ R, T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) →
        ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (hτ : ∀ (τ : F ≃+* F) (m : ℕ), Odd m → τ ^ m = 1 →
      (∀ g ∈ Ω, (g : Matrix (Fin 3) (Fin 3) F).map τ = g) → τ = 1) :
    involutionOddCore u = ⊥ := by
  refine involutionOddCore_eq_bot_of_model e₁ hZ hH u hγ (Ω.map (LinearFlag.proj 3 F)) ?_ ?_
    ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    rw [hψ, (hΩ g).1 hg]
  · intro s hs q hq
    obtain ⟨M, rfl⟩ := proj_surjective 3 F s
    obtain ⟨h, hh, rfl⟩ := hq
    rw [hψ] at hs
    have hz := proj_eq_proj_iff.1 hs.symm
    have hcen : ∀ x, (M⁻¹ * ψ M) * x = x * (M⁻¹ * ψ M) := fun x =>
      (mem_center_iff.1 (scalars_le_center 3 F hz) x).symm
    exact ⟨M * h * M⁻¹, (hΩ _).2 (map_conj_eq_of_twist ψ hcen ((hΩ h).1 hh)), by
      simp only [map_mul, map_inv]⟩
  · intro y hy
    obtain ⟨y₀, rfl⟩ := proj_surjective 3 F y
    exact Odd87.fl3g_proj_eq_one_of_commute hperf
      (fun T hT => hRcomm T fun g hg => hT g (hRΩ hg)) fun g hg => hy _ ⟨g, hg, rfl⟩
  · intro β m hm hβ hfixβ
    obtain ⟨A, τ, rfl⟩ := Odd87.exists_semilinear_of_odd_pow hm hβ
    obtain ⟨hA, hτΩ⟩ := semilinear_fix_reduce hperf hRΩ hRfix hRcomm fun g hg =>
      hfixβ _ ⟨g, hg, rfl⟩
    rw [hA, one_mul] at hβ ⊢
    have hτm : τ ^ m = 1 := by
      rw [← map_pow] at hβ
      exact (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) 1 (τ ^ m)
        (by rw [map_one, one_mul]; exact hβ)).1
    rw [hτ τ m hm hτm hτΩ, map_one]

end CFSG.GH74.Generic.BProg.B3.S3T5L3
