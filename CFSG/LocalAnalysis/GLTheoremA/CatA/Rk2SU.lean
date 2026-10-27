module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Herm
public import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Matrix CFSG.RankThree.PartOne.LIT

@[expose] def rk2StdHerm {K : Type} [Field K] (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) (m : ℕ) :
    HermForm σ (Fin m → K) where
  B u w := ∑ i, σ (u i) * w i
  add_left u u' w := by simp [add_mul, Finset.sum_add_distrib]
  add_right u w w' := by simp [mul_add, Finset.sum_add_distrib]
  smul_left c u w := by simp [Finset.mul_sum, mul_assoc]
  smul_right c u w := by simp [Finset.mul_sum, mul_left_comm]
  herm u w := by simp [map_sum, hσσ, mul_comm]

theorem rk2_card_le_unitary {K : Type} [Field K] [Finite K] (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c)
    {r m : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0)
    (hσ : ∀ c : K, c ^ r = 1 → c * σ c = 1 → c = 1)
    (E : Subgroup (GL (Fin m) K)) [Finite E] (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ r = 1)
    (hpres : ∀ g ∈ E, ((g : Matrix (Fin m) (Fin m) K).map σ)ᵀ * (g : Matrix (Fin m) (Fin m) K) = 1) :
    Nat.card E ≤ r ^ (m / 2) := by
  have : Finite (E.map (glAut (Fin m) K)) :=
    Finite.of_equiv E (E.equivMapOfInjective (glAut (Fin m) K) glAut_injective).toEquiv
  have hnd : ∀ v : Fin m → K, (∀ w, (rk2StdHerm σ hσσ m).B v w = 0) → v = 0 := by
    intro v hv
    funext j
    have h1 := hv (Pi.single j 1)
    simp [rk2StdHerm, Pi.single_apply] at h1
    simpa using h1
  have h := card_le_pow_half_of_herm hr hrK σ hσ m (Fin m → K)
    (by simp) (rk2StdHerm σ hσσ m) hnd (E.map (glAut (Fin m) K)) (map_glAut_comm hcomm)
    (map_glAut_exp hexp) (by
      rintro _ ⟨a, ha, rfl⟩ u w
      have hp := hpres a ha
      simp only [rk2StdHerm, glAut_apply]
      set A : Matrix (Fin m) (Fin m) K := (a : Matrix (Fin m) (Fin m) K) with hA
      have e1 : (fun i => σ ((A *ᵥ u) i)) = (A.map σ) *ᵥ (fun i => σ (u i)) := by
        funext i
        exact RingHom.map_mulVec σ A u i
      have e2 : ∑ i, σ ((A *ᵥ u) i) * (A *ᵥ w) i = (fun i => σ ((A *ᵥ u) i)) ⬝ᵥ (A *ᵥ w) := rfl
      have e3 : ∑ i, σ (u i) * w i = (fun i => σ (u i)) ⬝ᵥ w := rfl
      rw [e2, e3, e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        hp, Matrix.one_mulVec])
  rwa [card_map_glAut] at h

end CFSG.LocalAnalysis.GLTheoremA
