module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4UniCent
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4UniPair

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
  {A : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {l : K}
  {E : Matrix (HypIndex 2 0) (Fin 2 ⊕ Fin 2) K}

namespace PairFrame

variable (hE : PairFrame h A l E)

include hE

theorem frm_inv_mul (Y : GL (HypIndex 2 0) K) :
    pairFrm h E ((Y⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      pairFrm h E Y = 1 := by
  rw [← hE.frm_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, pairFrm, Matrix.mul_one,
    hE.FE]

theorem frm_mul_inv (Y : GL (HypIndex 2 0) K) :
    pairFrm h E Y *
      pairFrm h E ((Y⁻¹ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 := by
  rw [← hE.frm_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, pairFrm, Matrix.mul_one,
    hE.FE]

theorem frm_eq_of_forall_smul (h2 : (2 : K) ≠ 0) {τ : K} (hτ : τ ≠ 0) (hτb : h.bar τ = -τ)
    {Y : GL (HypIndex 2 0) K}
    (hY : ∀ B : Matrix (Fin 2) (Fin 2) K, B.det = 1 → ∃ c : K,
      (Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * (E * pairLevi h B * pairF h E) =
        c • ((E * pairLevi h B * pairF h E) * (Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K))) :
    ∃ a b : K, pairFrm h E Y = fromBlocks (a • 1) 0 0 (b • 1) := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hcomm : ∀ B : Matrix (Fin 2) (Fin 2) K, B.det = 1 → (pairLevi h B).trace = 4 →
      pairFrm h E Y * pairLevi h B = pairLevi h B * pairFrm h E Y := by
    intro B hB htr
    obtain ⟨c, hc⟩ := hY B hB
    have hc' := hE.frm_mul_levi hc
    rw [eq_one_of_mul_eq_smul (hE.frm_mul_inv Y) (hE.frm_inv_mul Y) hc' (by rw [htr]; exact h4),
      one_smul] at hc'
    exact hc'
  have hu : ∀ t : K, pairFrm h E Y * fromBlocks !![1, t; 0, 1] 0 0 !![1, 0; -h.bar t, 1] =
      fromBlocks !![1, t; 0, 1] 0 0 !![1, 0; -h.bar t, 1] * pairFrm h E Y := by
    intro t
    have := hcomm !![1, t; 0, 1] (by simp [det_fin_two_of]) (by
      rw [pairLevi, leviStar_upper]
      exact trace_fromBlocks_unip (trace_upper t) (trace_lower _))
    rwa [pairLevi, leviStar_upper] at this
  have hl : pairFrm h E Y * fromBlocks !![1, 0; 1, 1] 0 0 !![1, -h.bar 1; 0, 1] =
      fromBlocks !![1, 0; 1, 1] 0 0 !![1, -h.bar 1; 0, 1] * pairFrm h E Y := by
    have := hcomm !![1, 0; 1, 1] (by simp [det_fin_two_of]) (by
      rw [pairLevi, leviStar_lower]
      exact trace_fromBlocks_unip (trace_lower 1) (trace_upper _))
    rwa [pairLevi, leviStar_lower] at this
  exact eq_fromBlocks_smul_of_comm h h2 hτ hτb (hu 1) (hu τ) hl

theorem comm_of_forall_smul (h2 : (2 : K) ≠ 0) {τ : K} (hτ : τ ≠ 0) (hτb : h.bar τ = -τ)
    {Y Y' : GL (HypIndex 2 0) K}
    (hY : ∀ B : Matrix (Fin 2) (Fin 2) K, B.det = 1 → ∃ c : K,
      (Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * (E * pairLevi h B * pairF h E) =
        c • ((E * pairLevi h B * pairF h E) * (Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K)))
    (hY' : ∀ B : Matrix (Fin 2) (Fin 2) K, B.det = 1 → ∃ c : K,
      (Y' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * (E * pairLevi h B * pairF h E) =
        c • ((E * pairLevi h B * pairF h E) * (Y' : Matrix (HypIndex 2 0) (HypIndex 2 0) K))) :
    (Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (Y' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      (Y' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := by
  obtain ⟨a, b, hab⟩ := hE.frm_eq_of_forall_smul h2 hτ hτb hY
  obtain ⟨a', b', hab'⟩ := hE.frm_eq_of_forall_smul h2 hτ hτb hY'
  rw [hE.eq_frm (Y : Matrix (HypIndex 2 0) (HypIndex 2 0) K),
    hE.eq_frm (Y' : Matrix (HypIndex 2 0) (HypIndex 2 0) K), hE.conj_mul, hE.conj_mul, hab, hab',
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, smul_smul, smul_zero, mul_comm a a', mul_comm b b']

end PairFrame

end CFSG.ClassicalInvolution.Q3.TA3.L4U4
