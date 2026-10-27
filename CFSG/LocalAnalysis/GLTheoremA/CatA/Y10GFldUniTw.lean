module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniTw

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniMark CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU)
open CFSG.HardMathSupport.Foote.ModuleExclusions (Ai)

def uniTw {d : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (A : GL (Fin d) K) (x : GL (Fin d) K) : GL (Fin d) K :=
  A * glMap σ x * A⁻¹

theorem uniTw_iterate {d : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (A : GL (Fin d) K) (k : ℕ)
    (x : GL (Fin d) K) :
    (uniTw σ A)^[k] x = normProd σ A k * glMap (σ ^ k) x * (normProd σ A k)⁻¹ := by
  induction k generalizing x with
  | zero => simp [normProd, glMap_pow_zero, glMap_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hN : normProd σ A (k + 1) = A * glMap σ (normProd σ A k) := rfl
    simp only [hN, uniTw, glMap_pow_succ, map_mul, map_inv]
    group

theorem uniTw_iterate_mem {d n : ℕ} {K : Type} [Field K] {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x)
    (hτq : ∀ x, τ x = x ^ 2 ^ n) (σ : K ≃+* K) {A : GL (Fin d) K} (hA : A ∈ heldGU d K τ hτ)
    {x : GL (Fin d) K} (hx : x ∈ StatedSU d (2 ^ n) K) (k : ℕ) :
    (uniTw σ A)^[k] x ∈ StatedSU d (2 ^ n) K := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact conj_mem_statedSU hτ hτq hA (glMap_mem_statedSU hτ hτq σ ih)

theorem pow_mk_uni {d n : ℕ} {K : Type} [Field K] {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x)
    (hτq : ∀ x, τ x = x ^ 2 ^ n) (σ : K ≃+* K) {A : GL (Fin d) K} (hA : A ∈ heldGU d K τ hτ)
    (u : MulAut (LargeEvenProj (StatedSU d (2 ^ n) K)))
    (hβ : ∀ h h' : ↥(StatedSU d (2 ^ n) K), (h' : GL (Fin d) K) = A * glMap σ (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ n) K) h) = LargeEvenProjMk (StatedSU d (2 ^ n) K) h') (k : ℕ) :
    ∀ (x : GL (Fin d) K) (hx : x ∈ StatedSU d (2 ^ n) K),
      (u ^ k) (LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨x, hx⟩) =
        LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨(uniTw σ A)^[k] x, uniTw_iterate_mem hτ hτq σ hA hx k⟩ := by
  induction k with
  | zero => intro x hx; simp
  | succ k ih =>
    intro x hx
    have hstep : (uniTw σ A)^[k + 1] x = uniTw σ A ((uniTw σ A)^[k] x) := Function.iterate_succ_apply' _ _ _
    have hmem : uniTw σ A ((uniTw σ A)^[k] x) ∈ StatedSU d (2 ^ n) K :=
      conj_mem_statedSU hτ hτq hA (glMap_mem_statedSU hτ hτq σ (uniTw_iterate_mem hτ hτq σ hA hx k))
    have hβ' := hβ ⟨(uniTw σ A)^[k] x, uniTw_iterate_mem hτ hτq σ hA hx k⟩
      ⟨uniTw σ A ((uniTw σ A)^[k] x), hmem⟩ rfl
    rw [pow_succ', MulAut.mul_apply, ih x hx, hβ']
    exact congrArg (LargeEvenProjMk (StatedSU d (2 ^ n) K)) (Subtype.ext hstep.symm)

theorem normProd_scalar_of_sigma_pow {d n : ℕ} {K : Type} [Field K] [Finite K] {τ : K ≃+* K}
    (hτ : ∀ x, τ (τ x) = x) (hτq : ∀ x, τ x = x ^ 2 ^ n) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hd : 3 ≤ d) (hdQ : (d, 2 ^ n) ≠ (3, 2)) (σ : K ≃+* K) {A : GL (Fin d) K} (hA : A ∈ heldGU d K τ hτ)
    (u : MulAut (LargeEvenProj (StatedSU d (2 ^ n) K)))
    (hβ : ∀ h h' : ↥(StatedSU d (2 ^ n) K), (h' : GL (Fin d) K) = A * glMap σ (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ n) K) h) = LargeEvenProjMk (StatedSU d (2 ^ n) K) h')
    {p : ℕ} (hpow : u ^ p = 1) (hσp : σ ^ p = 1) :
    ∃ c : K, Ai σ (A : Matrix (Fin d) (Fin d) K) p = c • (1 : Matrix (Fin d) (Fin d) K) := by
  have hsc : ∀ c : Kˣ, ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = (c : K) • (1 : Matrix (Fin d) (Fin d) K) := fun c => by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hg : ∀ g : GL (Fin d) K, g ∈ StatedSU d (2 ^ n) K → ∃ c : K,
      (normProd σ A p : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
        (((normProd σ A p)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          c • (g : Matrix (Fin d) (Fin d) K) := by
    intro g hgmem
    have hmk : LargeEvenProjMk (StatedSU d (2 ^ n) K)
        ⟨(uniTw σ A)^[p] g, uniTw_iterate_mem hτ hτq σ hA hgmem p⟩ =
          LargeEvenProjMk (StatedSU d (2 ^ n) K) ⟨g, hgmem⟩ := by
      have h1 := pow_mk_uni hτ hτq σ hA u hβ p g hgmem
      rw [hpow, MulAut.one_apply] at h1
      exact h1.symm
    obtain ⟨c, hc⟩ := (projMk_eq_iff_uni _ _ _).1 hmk
    dsimp only at hc
    have hit : (uniTw σ A)^[p] g = normProd σ A p * g * (normProd σ A p)⁻¹ := by
      rw [uniTw_iterate, hσp, glMap_one]
    have h3 : (uniTw σ A)^[p] g * Matrix.GeneralLinearGroup.scalar (Fin d) c = g := by
      rw [hc, mul_inv_cancel_left]
    have hmat3 : ((uniTw σ A)^[p] g : Matrix (Fin d) (Fin d) K) * ((c : K) • (1 : Matrix (Fin d) (Fin d) K)) =
        (g : Matrix (Fin d) (Fin d) K) := by
      rw [← hsc c, ← Units.val_mul, h3]
    rw [Matrix.mul_smul, Matrix.mul_one] at hmat3
    have hT : ((uniTw σ A)^[p] g : Matrix (Fin d) (Fin d) K) =
        (c : K)⁻¹ • (g : Matrix (Fin d) (Fin d) K) := by
      rw [← hmat3, smul_smul, inv_mul_cancel₀ (Units.ne_zero c), one_smul]
    refine ⟨(c : K)⁻¹, ?_⟩
    rw [← hT, hit, Units.val_mul, Units.val_mul]
  obtain ⟨c, hc⟩ := uniScalar_holds K (2 ^ n) d τ hτ hτq hcard hd hdQ (normProd σ A p) hg
  exact ⟨c, by rw [← coe_normProd, hc]⟩

@[expose] def UniSigmaPowOne : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n d : ℕ) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x),
    (∀ x, τ x = x ^ 2 ^ n) → Nat.card K = (2 ^ n) ^ 2 → 3 ≤ d → (d, 2 ^ n) ≠ (3, 2) →
    ∀ (A : GL (Fin d) K) (hA : A ∈ heldGU d K τ hτ) (σ : K ≃+* K) (p : ℕ), p.Prime → p ≠ 2 →
      ∀ u : MulAut (LargeEvenProj (StatedSU d (2 ^ n) K)),
        (∀ h h' : ↥(StatedSU d (2 ^ n) K), (h' : GL (Fin d) K) = A * glMap σ (h : GL (Fin d) K) * A⁻¹ →
          u (LargeEvenProjMk (StatedSU d (2 ^ n) K) h) = LargeEvenProjMk (StatedSU d (2 ^ n) K) h') →
        u ^ p = 1 → σ ^ p = 1

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniTw

end
