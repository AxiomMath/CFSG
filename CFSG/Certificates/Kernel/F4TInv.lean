module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.F4T

open CFSG.Fischer

@[expose] def Normed (v : Fin 3 → F4) : Prop :=
  v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)

instance : DecidablePred Normed := fun v => by
  unfold Normed
  infer_instance

theorem exists_normed : ∀ u : Fin 3 → F4, u ≠ 0 → ∃ c : F4, c ≠ 0 ∧ Normed (c • u) := by
  decide +kernel

theorem F4_add_add : ∀ a b : F4, a = b + (a + b) := by decide

theorem F4_add_add' : ∀ a b : F4, a + b + (b + a) = 0 := by decide

theorem inv_eq_one_add_outer (t : Matrix (Fin 3) (Fin 3) F4) (h1 : t * t = 1) (h2 : t ≠ 1) :
    ∃ v w : Fin 3 → F4, Normed v ∧ w ≠ 0 ∧ w ⬝ᵥ v = 0 ∧ t = 1 + Matrix.vecMulVec v w := by
  set N := t + 1 with hN
  have htN : t = 1 + N := by
    rw [hN]
    ext i j
    simp only [Matrix.add_apply]
    exact F4_add_add _ _
  have hNN : N * N = 0 := by
    rw [hN, add_mul, mul_add, mul_add, h1, mul_one, one_mul, one_mul]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact F4_add_add' _ _
  have hN0 : N ≠ 0 := by
    intro h
    apply h2
    rw [htN, h, add_zero]
  set f := Matrix.mulVecLin N with hf
  have hrk : LinearMap.range f ≤ LinearMap.ker f := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    rw [LinearMap.mem_ker, hf, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  have hmono := Submodule.finrank_mono hrk
  rw [Module.finrank_fin_fun] at hdim
  have h1r : Module.finrank F4 (LinearMap.range f) ≤ 1 := by omega
  obtain ⟨g, hg⟩ := (finrank_le_one_iff (K := F4) (V := LinearMap.range f)).1 h1r
  have hcol : ∀ k : Fin 3, ∃ c : F4, ∀ i, N i k = c * (g : Fin 3 → F4) i := by
    intro k
    have hm : (fun i => N i k) ∈ LinearMap.range f := by
      refine LinearMap.mem_range.2 ⟨Pi.single k 1, ?_⟩
      rw [hf, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
      rfl
    obtain ⟨c, hc⟩ := hg ⟨_, hm⟩
    refine ⟨c, fun i => ?_⟩
    have := congrArg (fun x : LinearMap.range f => (x : Fin 3 → F4) i) hc
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  choose c hc using hcol
  have hNo : N = Matrix.vecMulVec (g : Fin 3 → F4) c := by
    ext i k
    rw [hc k i, Matrix.vecMulVec_apply, mul_comm]
  have hu0 : (g : Fin 3 → F4) ≠ 0 := by
    intro h
    apply hN0
    rw [hNo, h]
    ext i k
    simp [Matrix.vecMulVec_apply]
  have hc0 : c ≠ 0 := by
    intro h
    apply hN0
    rw [hNo, h]
    ext i k
    simp [Matrix.vecMulVec_apply]
  obtain ⟨s, hs, hsn⟩ := exists_normed _ hu0
  refine ⟨s • (g : Fin 3 → F4), s⁻¹ • c, hsn, ?_, ?_, ?_⟩
  · intro h
    apply hc0
    have := congrArg (fun x => s • x) h
    simpa [smul_smul, mul_inv_cancel₀ hs] using this
  ·
    have hsq : N * N = (c ⬝ᵥ (g : Fin 3 → F4)) • N := by
      rw [hNo]
      ext i k
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
        dotProduct, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [hNN] at hsq
    have hd : c ⬝ᵥ (g : Fin 3 → F4) = 0 := by
      by_contra hd
      exact hN0 (smul_eq_zero.1 hsq.symm |>.resolve_left hd)
    rw [smul_dotProduct, dotProduct_smul, hd, smul_zero, smul_zero]
  · rw [htN, hNo]
    congr 1
    ext i k
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    have e : s * (g : Fin 3 → F4) i * (s⁻¹ * c k) = (s * s⁻¹) * ((g : Fin 3 → F4) i * c k) := by
      ring
    rw [e, mul_inv_cancel₀ hs, one_mul]

end CFSG.KC.F4T

end
