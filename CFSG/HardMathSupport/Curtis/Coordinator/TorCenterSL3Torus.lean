module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitBasis

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LinearThreeKit

variable {K : Type*} [Field K]

@[expose] def diagSub (b : Fin 3 → Fin 3 → K) (m : ℕ) (hm : 0 < m) :
    Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | ∃ x : Fin 3 → K, (∀ i, x i ^ m = 1) ∧
    ∀ i, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = x i • b i}
  one_mem' := ⟨fun _ => 1, fun i => one_pow m, fun i => by simp⟩
  mul_mem' := by
    rintro g h ⟨x, hx, hxg⟩ ⟨y, hy, hyh⟩
    refine ⟨fun i => x i * y i, fun i => by rw [mul_pow, hx, hy, one_mul], fun i => ?_⟩
    rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hyh, Matrix.mulVec_smul, hxg,
      smul_smul, mul_comm]
  inv_mem' := by
    rintro g ⟨x, hx, hxg⟩
    have hx0 : ∀ i, x i ≠ 0 := fun i h0 => by
      have := hx i
      rw [h0, zero_pow hm.ne'] at this
      exact zero_ne_one this
    refine ⟨fun i => (x i)⁻¹, fun i => by rw [inv_pow, hx, inv_one], fun i => ?_⟩
    have h := congrArg (fun v => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
      (hxg i)
    simp only [Matrix.mulVec_smul] at h
    rw [inv_mulVec_mulVec] at h
    have h' := congrArg (fun v => (x i)⁻¹ • v) h
    simp only [smul_smul, inv_mul_cancel₀ (hx0 i), one_smul] at h'
    exact h'.symm

theorem diagSub_comm {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b) {m : ℕ} {hm : 0 < m}
    {g h : SpecialLinearGroup (Fin 3) K} (hg : g ∈ diagSub b m hm) (hh : h ∈ diagSub b m hm) :
    g * h = h * g := by
  obtain ⟨x, -, hx⟩ := hg
  obtain ⟨y, -, hy⟩ := hh
  refine Subtype.ext (eq_of_mulVec_eq hb fun i => ?_)
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hy, hx, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hy, smul_smul,
    smul_smul, mul_comm]

theorem pow_eq_one_of_mem_diagSub {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b) {m : ℕ}
    {hm : 0 < m} {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ diagSub b m hm) : g ^ m = 1 := by
  obtain ⟨x, hxm, hx⟩ := hg
  refine Subtype.ext (eq_of_mulVec_eq hb fun i => ?_)
  rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one, Matrix.one_mulVec,
    pow_mulVec_of_mulVec_eq_smul (hx i), hxm, one_smul]

theorem mul_comm_of_mem_diagSub {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b) {m : ℕ}
    {hm : 0 < m} {g s : SpecialLinearGroup (Fin 3) K} (hg : g ∈ diagSub b m hm) (d : Fin 3 → K)
    (hs : ∀ i, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d i • b i) : g * s = s * g := by
  obtain ⟨x, -, hx⟩ := hg
  refine Subtype.ext (eq_of_mulVec_eq hb fun i => ?_)
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hs, hx, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hs, smul_smul,
    smul_smul, mul_comm]

theorem card_diagSub_ge [Finite K] {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b) {m : ℕ}
    {hm : 0 < m} {ζ : K} (hζ : IsPrimitiveRoot ζ m) :
    m ^ 2 ≤ Nat.card (diagSub b m hm) := by
  have hb0 : ∀ i, b i ≠ 0 := fun i => hb.ne_zero i
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hm.ne'
  have hex : ∀ p : Fin m × Fin m, ∃ g : diagSub b m hm,
      (g : SpecialLinearGroup (Fin 3) K).1 *ᵥ b 0 = (ζ ^ (p.1 : ℕ)) • b 0 ∧
      (g : SpecialLinearGroup (Fin 3) K).1 *ᵥ b 1 = (ζ ^ (p.2 : ℕ)) • b 1 := by
    intro p
    let x : Fin 3 → K := ![ζ ^ (p.1 : ℕ), ζ ^ (p.2 : ℕ), (ζ ^ (p.1 : ℕ) * ζ ^ (p.2 : ℕ))⁻¹]
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 3) (Fin 3) K, ∀ j, A *ᵥ b j =
        ∑ i, (Matrix.diagonal x) i j • b i := exists_mulVec_eq_sum hb _
    have hAx : ∀ j, A *ᵥ b j = x j • b j := fun j => by
      rw [hA j]; simp [Matrix.diagonal_apply]
    have hdet : A.det = 1 := by
      rw [det_eq_of_mulVec_eq_sum hb hA, Matrix.det_diagonal, Fin.prod_univ_three]
      simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      field_simp [hζ0]
    have hpow : ∀ n : ℕ, (ζ ^ n) ^ m = 1 := fun n => by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    refine ⟨⟨⟨A, hdet⟩, x, forall_fin_three ?_ ?_ ?_, hAx⟩, hAx 0, hAx 1⟩
    · exact hpow _
    · exact hpow _
    · show ((ζ ^ (p.1 : ℕ) * ζ ^ (p.2 : ℕ))⁻¹) ^ m = 1
      rw [inv_pow, mul_pow, hpow, hpow, one_mul, inv_one]
  choose F hF using hex
  have hinj : Function.Injective F := by
    intro p q hpq
    have hc : ∀ (c d : K), c • b 0 = d • b 0 → c = d := fun c d h =>
      smul_left_injective K (hb0 0) h
    have hc1 : ∀ (c d : K), c • b 1 = d • b 1 → c = d := fun c d h =>
      smul_left_injective K (hb0 1) h
    have e0 : ζ ^ (p.1 : ℕ) = ζ ^ (q.1 : ℕ) := by
      apply hc
      rw [← (hF p).1, ← (hF q).1, hpq]
    have e1 : ζ ^ (p.2 : ℕ) = ζ ^ (q.2 : ℕ) := by
      apply hc1
      rw [← (hF p).2, ← (hF q).2, hpq]
    exact Prod.ext (Fin.ext (hζ.pow_inj p.1.2 q.1.2 e0)) (Fin.ext (hζ.pow_inj p.2.2 q.2.2 e1))
  have := Nat.card_le_card_of_injective F hinj
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  nlinarith [this]

end CFSG.HardMathSupport.Curtis.Coordinator
