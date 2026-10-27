module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSULift

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.AGLEmbedding Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem shortTorusFun_low {σ : F ≃+* F} {n : ℕ} (k j : ℕ) (hk : k + 1 < n / 2) (hj : j < n / 2)
    (c : F) :
    shortTorusFun σ (lowIdx (n := n) ⟨k, by omega⟩) (lowIdx (n := n) ⟨k + 1, hk⟩) c
        (lowIdx (n := n) ⟨j, hj⟩) =
      if j = k then c else if j = k + 1 then c⁻¹ else 1 := by
  simp only [shortTorusFun, lowIdx, Fin.ext_iff, Fin.val_rev]
  by_cases h1 : j = k
  · simp [h1]
  by_cases h2 : j = k + 1
  · simp [h2]
  have h3 : ¬ j = n - (k + 1) := by omega
  have h4 : ¬ j = n - (k + 1 + 1) := by omega
  simp [h1, h2, h3, h4]

theorem exists_torus_triple (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn : 8 ≤ n) :
    ∃ g₀ g₁ g₂ : SU (unitaryInvolution F 2 1) n,
      g₀ ∈ levelTorus (unitaryInvolution F 2 1) (⟨0, by omega⟩ : Fin (n / 2)) ∧
      g₁ ∈ levelTorus (unitaryInvolution F 2 1) (⟨1, by omega⟩ : Fin (n / 2)) ∧
      g₂ ∈ levelTorus (unitaryInvolution F 2 1) (⟨2, by omega⟩ : Fin (n / 2)) ∧
      g₀ * g₁ = g₁ * g₀ ∧ g₀ * g₂ = g₂ * g₀ ∧ g₁ * g₂ = g₂ * g₁ ∧
      g₀ ≠ 1 ∧ (∀ m : ℕ, g₀ ^ m ≠ g₁) ∧ ∀ a b : ℕ, g₀ ^ a * g₁ ^ b ≠ g₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := unitaryInvolution F 2 1 with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  obtain ⟨ω, hω0, hω1, hω3⟩ := exists_primitive_cube_root_of_card_four hF
  have hn2 : 4 ≤ n / 2 := by omega
  have hm : ∀ k : ℕ, k + 1 < n / 2 → k < n / 2 := fun k hk => by omega
  have hdiag : ∀ (k : ℕ) (hk : k + 1 < n / 2), ∃ g : SU σ n,
      g ∈ levelTorus σ ⟨k, by omega⟩ ∧
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        diagonal (shortTorusFun σ (lowIdx (n := n) ⟨k, by omega⟩) (lowIdx (n := n) ⟨k + 1, hk⟩)
          ω) := by
    intro k hk
    refine ⟨shortTorus σ hσ (lowIdx_ne_succ (k := ⟨k, by omega⟩) hk) (lowIdx_ne_rev _ _)
      (lowIdx_ne_rev _ _) ω, shortTorus_mem_levelTorus hσ hk (Units.mk0 ω hω0), ?_⟩
    exact coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) hω0
  obtain ⟨g₀, h₀, hv₀⟩ := hdiag 0 (by omega)
  obtain ⟨g₁, h₁, hv₁⟩ := hdiag 1 (by omega)
  obtain ⟨g₂, h₂, hv₂⟩ := hdiag 2 (by omega)
  have ev : ∀ (k j : ℕ) (hk : k + 1 < n / 2) (hj : j < n / 2),
      shortTorusFun σ (lowIdx (n := n) ⟨k, by omega⟩) (lowIdx (n := n) ⟨k + 1, hk⟩) ω
        (lowIdx (n := n) ⟨j, hj⟩) = if j = k then ω else if j = k + 1 then ω⁻¹ else 1 :=
    fun k j hk hj => shortTorusFun_low k j hk hj ω
  have e00 := ev 0 0 (by omega) (by omega)
  have e01 := ev 0 1 (by omega) (by omega)
  have e10 := ev 1 0 (by omega) (by omega)
  have e11 := ev 1 1 (by omega) (by omega)
  have e12 := ev 1 2 (by omega) (by omega)
  have e20 := ev 2 0 (by omega) (by omega)
  have e21 := ev 2 1 (by omega) (by omega)
  have e22 := ev 2 2 (by omega) (by omega)
  have ent : ∀ (g : SU σ n) (f : Fin n → F),
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal f → ∀ (s : Fin n) (m : ℕ),
      ((g ^ m : SU σ n) : GL (Fin n) F).1 s s = f s ^ m := by
    intro g f hg s m
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hg, diagonal_pow]
    simp
  have comm : ∀ (g h : SU σ n) (f f' : Fin n → F),
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal f →
      ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal f' → g * h = h * g := by
    intro g h f f' hg hh
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hg, hh, diagonal_mul_diagonal]
    congr 1
    funext s
    exact mul_comm _ _
  refine ⟨g₀, g₁, g₂, h₀, h₁, h₂, comm _ _ _ _ hv₀ hv₁, comm _ _ _ _ hv₀ hv₂,
    comm _ _ _ _ hv₁ hv₂, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun g : SU σ n => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      (lowIdx ⟨0, by omega⟩) (lowIdx ⟨0, by omega⟩)) h
    simp only [hv₀, Subgroup.coe_one, Units.val_one, diagonal_apply_eq, one_apply_eq, e00] at this
    simp at this
    exact hω1 this
  · intro m h
    have h1 := ent g₀ _ hv₀ (lowIdx ⟨2, by omega⟩) m
    rw [h] at h1
    have h2 := ent g₁ _ hv₁ (lowIdx ⟨2, by omega⟩) 1
    have e02 := ev 0 2 (by omega) (by omega)
    have e12' := e12
    simp only [pow_one] at h2
    rw [h2, e12', e02] at h1
    simp at h1
    exact hω1 h1
  · intro a b h
    have ent2 : ∀ s : Fin n, ((g₀ ^ a * g₁ ^ b : SU σ n) : GL (Fin n) F).1 s s =
        (shortTorusFun σ (lowIdx (n := n) ⟨0, by omega⟩) (lowIdx (n := n) ⟨0 + 1, by omega⟩) ω s) ^ a *
        (shortTorusFun σ (lowIdx (n := n) ⟨1, by omega⟩) (lowIdx (n := n) ⟨1 + 1, by omega⟩) ω s) ^ b := by
      intro s
      simp only [Subgroup.coe_mul, Units.val_mul, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val,
        hv₀, hv₁, diagonal_pow, diagonal_mul_diagonal, diagonal_apply_eq]
      rfl
    have a0 := ent2 (lowIdx ⟨0, by omega⟩)
    have a1 := ent2 (lowIdx ⟨1, by omega⟩)
    have a2 := ent2 (lowIdx ⟨2, by omega⟩)
    rw [h] at a0 a1 a2
    have e02 := ev 0 2 (by omega) (by omega)
    have e22' := e22
    have e2x0 := e20
    have e2x1 := e21
    have c0 := ent g₂ _ hv₂ (lowIdx ⟨0, by omega⟩) 1
    have c1 := ent g₂ _ hv₂ (lowIdx ⟨1, by omega⟩) 1
    have c2 := ent g₂ _ hv₂ (lowIdx ⟨2, by omega⟩) 1
    simp only [pow_one] at c0 c1 c2
    rw [c0, e20, e00, e10] at a0
    rw [c1, e21, e01, e11] at a1
    rw [c2, e22, e02, e12] at a2
    simp at a0 a1 a2
    rw [← a0] at a1
    simp at a1
    rw [← a1] at a2
    simp at a2
    exact hω1 a2

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
