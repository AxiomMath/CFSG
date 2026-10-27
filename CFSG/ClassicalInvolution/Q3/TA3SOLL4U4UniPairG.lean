module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4Shape
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4PSL
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4UniComm
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4UniPsi

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem normalSimpleShape_of_paired (hp : p ≠ 2) {A : hypSU h 2 0} {l : K} (hl0 : l ≠ 0)
    (hAA : ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = (l ^ 2) • 1)
    {e g : Fin 2 → HypIndex 2 0 → K}
    (hAe : ∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ e i =
      l • e i)
    (hAg : ∀ i, ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ g i =
      (-l) • g i)
    (hee : ∀ i j, hypForm h 2 0 (e i) (e j) = 0) (hgg : ∀ i j, hypForm h 2 0 (g i) (g j) = 0)
    (heg : ∀ i j, hypForm h 2 0 (e i) (g j) = if i = j then 1 else 0) :
    NormalSimpleShape (hypPSU h 2 0) (hypProj h 2 0 A) := by
  have := h.finite
  have hE := exists_pairFrame h hAe hAg hee hgg heg
  set E := colMat (Sum.elim e g) with hEdef
  obtain ⟨ψ, hψ⟩ := hE.exists_psi
  have h2 : (2 : K) ≠ 0 := UnitaryHigher.two_ne_zero_of_odd h hp
  have h4 : 4 ≤ Nat.card K := by
    have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
    rw [h.card]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right (by omega) (by have := h.one_le; omega)
  have hker := hE.ker_psi hψ
  set φ := (hypProj h 2 0).comp ψ with hφ
  have hval : ∀ B : SL(2, K), ((ψ B : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      = E * pairLevi h (B : Matrix (Fin 2) (Fin 2) K) * pairF h E := hψ
  refine ⟨φ.range, ?_, ?_, isSimpleGroup_range_of_ker_eq_center h4 φ hker,
    isPerfect_range_of_ker_eq_center h4 φ hker, ?_⟩
  · rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hφ, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hval]
    exact hE.levi_comm _
  · refine le_normalizer_of_forall_conj fun y hy x hx => ?_
    obtain ⟨Y, rfl⟩ := hypProj_surjective h 2 0 y
    obtain ⟨B, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    obtain ⟨c, hc⟩ := exists_smul_of_hypProj_comm h hy
    have hc1 := eq_one_or_eq_neg_one_of_mul_eq_smul (pow_ne_zero 2 hl0) hAA hc
    obtain ⟨B', hB', hconj⟩ := hE.exists_conj (mul_ne_zero h2 hl0) (mem_hypSU.mp Y.2).1 hc1 hc
      B.2
    set B'' : SL(2, K) := ⟨B', hB'⟩ with hB''
    refine ⟨B'', ?_⟩
    have hYψ : Y * ψ B = ψ B'' * Y := by
      refine Subtype.ext (Units.ext ?_)
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [hval B, hval B'']
      exact hconj
    rw [hφ, MonoidHom.comp_apply, MonoidHom.comp_apply, eq_mul_inv_of_mul_eq hYψ.symm, map_mul,
      map_mul, map_inv]
  · intro a ha b hb _ _
    obtain ⟨Y, rfl⟩ := hypProj_surjective h 2 0 a
    obtain ⟨Y', rfl⟩ := hypProj_surjective h 2 0 b
    have hcomm : ∀ Z : hypSU h 2 0, hypProj h 2 0 Z ∈ Subgroup.centralizer (φ.range : Set _) →
        ∀ B : Matrix (Fin 2) (Fin 2) K, B.det = 1 → ∃ c : K,
          ((Z : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
            (E * pairLevi h B * pairF h E) =
          c • ((E * pairLevi h B * pairF h E) *
            ((Z : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by
      intro Z hZ B hB
      set B₀ : SL(2, K) := ⟨B, hB⟩
      have hmem := Subgroup.mem_centralizer_iff.mp hZ (φ B₀) ⟨B₀, rfl⟩
      rw [hφ, MonoidHom.comp_apply] at hmem
      obtain ⟨c, hc⟩ := exists_smul_of_hypProj_comm h hmem.symm
      rw [hval B₀] at hc
      exact ⟨c, hc⟩
    obtain ⟨τ, hτ, hτb⟩ := exists_bar_eq_neg h
    have hYY := hE.comm_of_forall_smul h2 hτ hτb (hcomm Y ha) (hcomm Y' hb)
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact hYY

end CFSG.ClassicalInvolution.Q3.TA3.L4U4
