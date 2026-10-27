module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerCases

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open

section Step

variable {K : Type*} [Field K] [Finite K] {G : Type*} [Group G]

theorem exists_not_commute_SL3 (h3 : 3 ∣ Nat.card K - 1) :
    ∃ x y : SpecialLinearGroup (Fin 3) K, x * y ≠ y * x := by
  obtain ⟨k, hk, -⟩ := exists_notMem_center_commute h3 (γ := 1) ⟨1, by simp⟩
  rw [Subgroup.mem_center_iff] at hk
  push Not at hk
  obtain ⟨x, hx⟩ := hk
  exact ⟨x, k, hx⟩

theorem layerStep_of_three_copies (h3 : 3 ∣ Nat.card K - 1) (h4 : Nat.card K ≠ 4)
    {E : Subgroup (MulAut G)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27)
    {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* G} (hρ : ∀ i, Function.Injective (ρ i))
    (hcomm : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s)
    {σ : MulAut G} (hσ : σ ∈ E) (hσ1 : σ ≠ 1) (hσρ : ∀ i s, σ (ρ i s) = ρ i s)
    (hdec : ∀ ε ∈ E, ∃ k : Fin 3,
      (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + k)).range) ∧
        (k = 0 → ∀ i, ∃ γ : GL (Fin 3) K, ∀ s, ε (ρ i s) = ρ i (conjSL γ s)))
    (i : Fin 3) : (ρ i).range ≤ seitzHyperGamma 3 E := by
  classical
  set R : Fin 3 → Subgroup G := fun i => (ρ i).range with hR
  have hRcomm : ∀ i j, i ≠ j → ∀ x ∈ R i, ∀ y ∈ R j, x * y = y * x := by
    rintro i j hij _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact hcomm i j hij s t
  have hRne : ∀ i j, R i = R j → i = j := by
    intro i j hij
    by_contra hne
    obtain ⟨x, y, hxy⟩ := exists_not_commute_SL3 (K := K) h3
    apply hxy
    apply hρ i
    have hy : ρ i y ∈ R j := by
      rw [← hij]
      exact ⟨y, rfl⟩
    rw [map_mul, map_mul]
    exact hRcomm i j hne _ ⟨x, rfl⟩ _ hy
  have hSh_mul : ∀ {ε₁ ε₂ : MulAut G} {k₁ k₂ : Fin 3},
      (∀ i, (R i).map ε₁.toMonoidHom = R (i + k₁)) →
      (∀ i, (R i).map ε₂.toMonoidHom = R (i + k₂)) →
        ∀ i, (R i).map (ε₁ * ε₂).toMonoidHom = R (i + (k₁ + k₂)) := by
    intro ε₁ ε₂ k₁ k₂ h₁ h₂ i
    have e : (ε₁ * ε₂).toMonoidHom = ε₁.toMonoidHom.comp ε₂.toMonoidHom := rfl
    rw [e, ← Subgroup.map_map, h₂, h₁, add_assoc, add_comm k₂ k₁]
  have hSh_unique : ∀ {ε : MulAut G} {k k' : Fin 3},
      (∀ i, (R i).map ε.toMonoidHom = R (i + k)) →
      (∀ i, (R i).map ε.toMonoidHom = R (i + k')) → k = k' := by
    intro ε k k' h h'
    have := hRne _ _ ((h 0).symm.trans (h' 0))
    simpa using this
  have hAct : ∀ ε ∈ E, (∀ i, (R i).map ε.toMonoidHom = R (i + 0)) →
      ∀ i, ∃ γ : GL (Fin 3) K, ∀ s, ε (ρ i s) = ρ i (conjSL γ s) := by
    intro ε hε h0
    obtain ⟨k, hk, hact⟩ := hdec ε hε
    exact hact (hSh_unique hk h0)
  by_cases hI : ∀ ε ∈ E, ∀ i, (R i).map ε.toMonoidHom = R (i + 0)
  · exact le_seitzHyperGamma_of_acts h3 h4 hE hcard (hρ i) hσ hσ1 (hσρ i)
      (fun ε hε => hAct ε hε (hI ε hε) i)
  obtain ⟨τ, hτ, hτ0⟩ : ∃ τ ∈ E, ¬ ∀ i, (R i).map τ.toMonoidHom = R (i + 0) := by
    by_contra hcon
    exact hI fun ε hε => by_contra fun hne => hcon ⟨ε, hε, hne⟩
  obtain ⟨kτ, hτk, -⟩ := hdec τ hτ
  have hkτ : kτ ≠ 0 := by
    rintro rfl
    exact hτ0 hτk
  have hσ3 : σ ^ 3 = 1 := hE.2 σ hσ
  obtain ⟨ε₁, hε₁, hε₁σ⟩ := exists_notMem_zpowers hE hcard hσ
  obtain ⟨ε₂, hε₂, hε₂c⟩ := exists_notMem_closure_pair hE hcard hσ hε₁
  have hε₁3 : ε₁ ^ 3 = 1 := hE.2 ε₁ hε₁
  have hε₂3 : ε₂ ^ 3 = 1 := hE.2 ε₂ hε₂
  obtain ⟨s₁, hs₁, -⟩ := hdec ε₁ hε₁
  obtain ⟨s₂, hs₂, -⟩ := hdec ε₂ hε₂
  have hε₂σ : ε₂ ∉ Subgroup.zpowers σ := fun h =>
    hε₂c ((Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))) h)
  obtain ⟨f, hf, hfσ, hf0⟩ : ∃ f ∈ E, f ∉ Subgroup.zpowers σ ∧
      ∀ i, (R i).map f.toMonoidHom = R (i + 0) := by
    by_cases h₁ : s₁ = 0
    · subst h₁
      exact ⟨ε₁, hε₁, hε₁σ, hs₁⟩
    by_cases h₂ : s₂ = 0
    · subst h₂
      exact ⟨ε₂, hε₂, hε₂σ, hs₂⟩
    by_cases h12 : s₁ = s₂
    · refine ⟨ε₁ * ε₂ ^ 2, E.mul_mem hε₁ (E.pow_mem hε₂ 2), ?_, ?_⟩
      · intro hmem
        have := pow_mul_pow_mem_zpowers (a := 1) (b := 2) hε₁σ hε₂c hσ3 hε₁3 hε₂3
          (by rwa [pow_one])
        exact absurd this.1 (by norm_num)
      · have h := hSh_mul hs₁ (hSh_mul hs₂ hs₂)
        have e : s₁ + (s₂ + s₂) = 0 := by
          rw [← h12]
          exact (by decide : ∀ s : Fin 3, s + (s + s) = 0) s₁
        rw [e] at h
        rwa [pow_two]
    · refine ⟨ε₁ * ε₂, E.mul_mem hε₁ hε₂, ?_, ?_⟩
      · intro hmem
        have := pow_mul_pow_mem_zpowers (a := 1) (b := 1) hε₁σ hε₂c hσ3 hε₁3 hε₂3
          (by rwa [pow_one, pow_one])
        exact absurd this.1 (by norm_num)
      · have h := hSh_mul hs₁ hs₂
        have e : s₁ + s₂ = 0 :=
          (by decide : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → a ≠ b → a + b = 0) s₁ s₂ h₁ h₂ h12
        rwa [e] at h
  obtain ⟨γ, hγ⟩ := hAct f hf hf0 i
  have hγ3 := exists_pow_three_smul_one (hρ i) (hE.2 f hf) hγ
  have hτσ : τ ∉ Subgroup.zpowers σ := by
    intro hmem
    apply hτ0
    intro j
    have hfix : ∀ x ∈ R j, τ x = x := by
      rintro _ ⟨t, rfl⟩
      exact zpow_apply_eq_of_apply_eq (hσρ j t) hmem
    ext y
    rw [add_zero]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hfix x hx]
      exact hx
    · intro hy
      exact ⟨y, hy, hfix y hy⟩
  have hik : i ≠ i + kτ := (by decide : ∀ i k : Fin 3, k ≠ 0 → i ≠ i + k) i kτ hkτ
  have hik2 : i ≠ i + kτ + kτ := (by decide : ∀ i k : Fin 3, k ≠ 0 → i ≠ i + k + k) i kτ hkτ
  have hτρ : ∀ s, τ (ρ i s) ∈ R (i + kτ) := by
    intro s
    have : τ (ρ i s) ∈ (R i).map τ.toMonoidHom := ⟨ρ i s, ⟨s, rfl⟩, rfl⟩
    rwa [hτk i] at this
  have hτB : ∀ y ∈ R (i + kτ), τ y ∈ R (i + kτ + kτ) := by
    intro y hy
    have : τ y ∈ (R (i + kτ)).map τ.toMonoidHom := ⟨y, hy, rfl⟩
    rwa [hτk (i + kτ)] at this
  exact le_seitzHyperGamma_of_perm h3 hE hcard (ρ := ρ i) (B := R (i + kτ))
    (C := R (i + kτ + kτ)) hσ hτ hf hσ1 hτσ hfσ (hσρ i)
    (by rintro _ ⟨t, rfl⟩; exact hσρ _ t) (by rintro _ ⟨t, rfl⟩; exact hσρ _ t)
    (fun s y hy => hRcomm i (i + kτ) hik (ρ i s) ⟨s, rfl⟩ y hy)
    (fun s y hy => hRcomm i (i + kτ + kτ) hik2 (ρ i s) ⟨s, rfl⟩ y hy) hτρ hτB hγ hγ3

end Step

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
