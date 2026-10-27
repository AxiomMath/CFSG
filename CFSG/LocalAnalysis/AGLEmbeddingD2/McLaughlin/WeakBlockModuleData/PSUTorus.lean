module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSULift

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.AGLEmbedding Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_torus_pair (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn : 6 ≤ n) :
    ∃ g₀ g₁ : SU (unitaryInvolution F 2 1) n,
      g₀ ∈ levelTorus (unitaryInvolution F 2 1) (⟨0, by omega⟩ : Fin (n / 2)) ∧
      g₁ ∈ levelTorus (unitaryInvolution F 2 1) (⟨1, by omega⟩ : Fin (n / 2)) ∧
      g₀ * g₁ = g₁ * g₀ ∧ g₀ ≠ 1 ∧ ∀ m : ℕ, g₀ ^ m ≠ g₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := unitaryInvolution F 2 1 with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  obtain ⟨ω, hω0, hω1, hω3⟩ := exists_primitive_cube_root_of_card_four hF
  have hn2 : 3 ≤ n / 2 := by omega
  set k₀ : Fin (n / 2) := ⟨0, by omega⟩ with hk₀
  set k₁ : Fin (n / 2) := ⟨1, by omega⟩ with hk₁
  have hm0 : k₀.val + 1 < n / 2 := by simp [hk₀]; omega
  have hm1 : k₁.val + 1 < n / 2 := by simp [hk₁]; omega
  set g₀ := shortTorus σ hσ (lowIdx_ne_succ hm0) (lowIdx_ne_rev k₀ k₀) (lowIdx_ne_rev _ _) ω
    with hg₀
  set g₁ := shortTorus σ hσ (lowIdx_ne_succ hm1) (lowIdx_ne_rev k₁ k₁) (lowIdx_ne_rev _ _) ω
    with hg₁
  have hv₀ : ((g₀ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (shortTorusFun σ (lowIdx k₀) (lowIdx ⟨k₀.val + 1, hm0⟩) ω) :=
    coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) hω0
  have hv₁ : ((g₁ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (shortTorusFun σ (lowIdx k₁) (lowIdx ⟨k₁.val + 1, hm1⟩) ω) :=
    coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) hω0
  set f₀ := shortTorusFun σ (lowIdx k₀) (lowIdx ⟨k₀.val + 1, hm0⟩) ω with hf₀
  set f₁ := shortTorusFun σ (lowIdx k₁) (lowIdx ⟨k₁.val + 1, hm1⟩) ω with hf₁
  have hmem₀ : g₀ ∈ levelTorus σ k₀ := shortTorus_mem_levelTorus hσ hm0 (Units.mk0 ω hω0)
  have hmem₁ : g₁ ∈ levelTorus σ k₁ := shortTorus_mem_levelTorus hσ hm1 (Units.mk0 ω hω0)
  let p0 : Fin n := ⟨0, by omega⟩
  let p2 : Fin n := ⟨2, by omega⟩
  have hf₀0 : f₀ p0 = ω := by
    simp [hf₀, shortTorusFun, lowIdx, hk₀, p0]
  have hf₀2 : f₀ p2 = 1 := by
    simp only [hf₀, shortTorusFun, lowIdx, hk₀, p2]
    have h1 : (⟨2, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
    have h2 : (⟨2, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have h3 : (⟨2, by omega⟩ : Fin n) ≠ Fin.rev ⟨0, by omega⟩ := by
      simp [Fin.ext_iff, Fin.val_rev]; omega
    have h4 : (⟨2, by omega⟩ : Fin n) ≠ Fin.rev ⟨1, by omega⟩ := by
      simp [Fin.ext_iff, Fin.val_rev]; omega
    simp [h1, h2, h3, h4]
  have hf₁2 : f₁ p2 = ω⁻¹ := by
    simp only [hf₁, shortTorusFun, lowIdx, hk₁, p2]
    have h2 : (⟨2, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    simp [h2]
  refine ⟨g₀, g₁, hmem₀, hmem₁, ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hv₀, hv₁, diagonal_mul_diagonal]
    congr 1
    funext s
    exact mul_comm _ _
  · intro h
    have := congrArg (fun g : SU σ n => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p0 p0) h
    simp only [hv₀, Subgroup.coe_one, Units.val_one, diagonal_apply_eq, one_apply_eq, hf₀0] at this
    exact hω1 this
  · intro m h
    have := congrArg (fun g : SU σ n => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p2 p2) h
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hv₀, hv₁, diagonal_pow,
      diagonal_apply_eq, Pi.pow_apply, hf₀2, hf₁2, one_pow] at this
    have : ω⁻¹ = 1 := this.symm
    exact hω1 (inv_eq_one.mp this)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
