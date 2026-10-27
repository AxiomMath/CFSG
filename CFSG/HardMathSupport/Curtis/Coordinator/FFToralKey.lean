module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterY

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open scoped commutatorElement
open Matrix CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.LocalAnalysis.ComponentInitial
  LinearFlag CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding.LinearThreeKit

section Key

variable {Y : Type} [Group Y] {L J : Subgroup Y} {K : Type} [Field K] {d : ℕ} {u : Y}

theorem toral_diag_key [Finite K] [CharP K 2] [Finite Y]
    {ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) K}
    (cfg : ToralCfg L J ψ d u) {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card K = 2 ^ f) (h3f : ¬ 3 ∣ f) (h9 : ¬ 9 ∣ Nat.card K - 1) {Q X : Subgroup Y}
    (hQJ : ∀ x ∈ Q, x ∈ Subgroup.normalizer (L : Set Y) → ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hX3 : IsPGroup 3 X) (hXL : X ≤ Subgroup.normalizer (L : Set Y)) (hXQ : X ≤ Q)
    (hXu : X ≤ Subgroup.centralizer ({u} : Set Y)) :
    ∃ b : Fin 3 → Fin 3 → K, LinearIndependent K b ∧
      ∀ (x : Y) (hx : x ∈ X), ∃ (A : GL (Fin 3) K) (a : Fin 3 → K),
        normAut ψ ⟨x, hXL hx⟩ =
          CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A ∧
        ∀ i, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = a i • b i := by
  obtain ⟨t, c, hc, htc⟩ := exists_mul_of_mem_sup_centralizer' cfg.hu
  have hs := psi_not_mem_scalars ψ hc htc cfg.huC
  have hs3 := psi_pow_three_mem_scalars ψ hc htc cfg.hu3
  have hsJ : ψ t ∈ stabilizer (flagSpace 3 K d) := (cfg.hJ t).mp (coe_mem_J hc htc cfg.hfix)
  have hs31 := pow_three_eq_one_of_not_nine_dvd h9 cfg.hd hsJ hs3
  obtain ⟨b, hb, hb0, hb1, hb2⟩ := exists_eigenbasis_of_pow_three (coe_pow_eq_one hs31)
    (ψ t).2 (ne_smul_one_of_notMem_scalars hs) hω1 hω3
  refine ⟨b, hb, fun x hx => ?_⟩
  have hxu : x * u * x⁻¹ = u := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
    rw [mul_inv_eq_iff_eq_mul]; exact this
  obtain ⟨A, a, h1, h2, -⟩ := aut_diag_small cfg hω1 hω3 hf hk h3f hc htc hb hb0 hb1 hb2 hQJ
    (hXL hx) (hXQ hx) hxu (by
      obtain ⟨k, hk3⟩ := hX3 ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk3⟩)
  exact ⟨A, a, h1, h2⟩

end Key

theorem mul_comm_of_diag {K : Type} [Field K] {b : Fin 3 → Fin 3 → K}
    (hb : LinearIndependent K b) {A A' : GL (Fin 3) K} {a a' : Fin 3 → K}
    (hA : ∀ i, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = a i • b i)
    (hA' : ∀ i, (A' : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = a' i • b i) : A * A' = A' * A := by
  let hbasis : Module.Basis (Fin 3) K (Fin 3 → K) :=
    basisOfLinearIndependentOfCardEqFinrank hb (by simp)
  have hcoe : ∀ i, hbasis i = b i := fun i =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hb (by simp)) i
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have key : Matrix.toLin' ((A : Matrix (Fin 3) (Fin 3) K) * (A' : Matrix (Fin 3) (Fin 3) K)) =
      Matrix.toLin' ((A' : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) := by
    refine hbasis.ext fun i => ?_
    rw [hcoe]
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hA, hA',
      Matrix.mulVec_smul]
    rw [smul_smul, smul_smul, mul_comm]
  exact Matrix.toLin'.injective key

end CFSG.HardMathSupport.Curtis.Coordinator
