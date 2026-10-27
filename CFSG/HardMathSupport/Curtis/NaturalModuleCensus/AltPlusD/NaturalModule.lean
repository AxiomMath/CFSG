module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.NMFixed

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Matrix

theorem false_of_invariant_totSingular {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) (Φ : QuadForm K (ι → K))
    (hι : 5 ≤ Fintype.card ι) (W : Submodule K (ι → K)) (hWQ : ∀ w ∈ W, Φ.Q w = 0)
    (hW : 2 ≤ Module.finrank K W) (M : GL ι K)
    (hMQ : ∀ v, Φ.Q ((M : Matrix ι ι K) *ᵥ v) = Φ.Q v) (hM5 : M ^ 5 = 1)
    (hMW : ∀ w ∈ W, (M : Matrix ι ι K) *ᵥ w ∈ W)
    (hC : ∀ g ∈ StatedOmega Φ.Q, g * M = M * g → ∀ w ∈ W, (g : Matrix ι ι K) *ᵥ w ∈ W) :
    False := by
  set T : (ι → K) →ₗ[K] (ι → K) := Matrix.toLin' (M : Matrix ι ι K) with hTdef
  have hT : ∀ v, T v = (M : Matrix ι ι K) *ᵥ v := fun v => Matrix.toLin'_apply _ _
  have hT5 : T ^ 5 = 1 := by
    have h1 : T ^ 5 = Matrix.toLinAlgEquiv' ((M : Matrix ι ι K) ^ 5) := by
      rw [map_pow]
      rfl
    rw [h1, ← Units.val_pow_eq_pow_val, hM5]
    simp
  have hTQ : ∀ v, Φ.Q (T v) = Φ.Q v := fun v => by rw [hT]; exact hMQ v
  have hTW : ∀ w ∈ W, T w ∈ W := fun w hw => by rw [hT]; exact hMW w hw
  have hE : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 →
      (∀ v, Φ.eichler x y (T v) = T (Φ.eichler x y v)) → ∀ w ∈ W, Φ.eichler x y w ∈ W := by
    intro x y hx hxy hcomm w hw
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler' Φ hι hx hxy
    have hAM : A * M = M * A := by
      apply Units.ext
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      rw [Units.val_mul, Units.val_mul, Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAv, ← hT, hAv, hcomm, hT]
    have := hC A hA hAM w hw
    rwa [hAv] at this
  by_cases hfix : ∀ w ∈ W, T w = w
  · exact NM_false_of_fixed Φ T hT5 hTQ W hWQ hE hfix hW
  · push Not at hfix
    obtain ⟨f, hfW, hf⟩ := hfix
    obtain ⟨a, f', ha, hf'W, hf'0, hf'⟩ := NM_exists_quadratic_vec T hK hT5 W hTW hfW hf
    exact NM_false_of_quadratic Φ T hK hT5 hTQ W hWQ hTW hE ha hf'W hf'0 hf'

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
