module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailFlagTransitivity
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates

public section

namespace CFSG.AGLEmbedding.LeviBlock

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

variable (K A r) in
@[expose] def tailStdFlag (k : ℕ) : Fin k → Submodule K ((Fin r ⊕ Fin r → K) × A) :=
  fun i => tailFlag K A r (i + 1)

theorem orthFlag_smul_apply {k : ℕ} (g : ↥(orthElementaryGroup (quadTail r qA)))
    (W : Fin k → Submodule K ((Fin r ⊕ Fin r → K) × A)) (i : Fin k) :
    (g • W) i = (W i).map ((g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  rfl

theorem smul_mem_singularFlags_tail {k : ℕ} (g : ↥(orthElementaryGroup (quadTail r qA)))
    {W : Fin k → Submodule K ((Fin r ⊕ Fin r → K) × A)}
    (hW : W ∈ singularFlags (quadTail r qA) k) : g • W ∈ singularFlags (quadTail r qA) k := by
  obtain ⟨hWd, hWm, hWs⟩ := hW
  have hgO := orthElementaryGroup_le _ g.2
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [orthFlag_smul_apply, LinearEquiv.finrank_map_eq, hWd i]
  · rw [orthFlag_smul_apply, orthFlag_smul_apply]
    exact Submodule.map_mono (hWm hij)
  · rw [orthFlag_smul_apply]
    rintro _ ⟨y, hy, rfl⟩
    rw [LinearEquiv.coe_coe, map_of_mem hgO]
    exact hWs i y hy

theorem tailStdFlag_mem_singularFlags {k : ℕ} (hk : k ≤ r) :
    tailStdFlag K A r k ∈ singularFlags (quadTail r qA) k :=
  ⟨fun i => finrank_tailFlag (by omega), fun i j hij => orthTailFlag_mono (by
    have := Fin.le_def.1 hij
    omega), fun i _ hx => quadTail_eq_zero_of_mem_tailFlag hx⟩

theorem stabilizer_tailStdFlag (k : ℕ) :
    MulAction.stabilizer ↥(orthElementaryGroup (quadTail r qA)) (tailStdFlag K A r k) =
      orthParab r qA (fun i : Fin (k + 1) => (i : ℕ)) := by
  ext x
  rw [MulAction.mem_stabilizer_iff, mem_orthParab, funext_iff]
  constructor
  · intro h i
    cases i using Fin.cases with
    | zero => simp [tailFlag_zero]
    | succ j => exact h j
  · intro h i
    exact h i.succ

theorem orbit_tailStdFlag [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A}
    (ha₀ : a₀ ≠ 0) {k : ℕ} (hk : k ≤ r) :
    MulAction.orbit ↥(orthElementaryGroup (quadTail r qA)) (tailStdFlag K A r k) =
      singularFlags (quadTail r qA) k := by
  ext W
  constructor
  · rintro ⟨g, rfl⟩
    exact smul_mem_singularFlags_tail g (tailStdFlag_mem_singularFlags hk)
  · intro hW
    obtain ⟨g, hg, hgW⟩ := exists_mem_map_eq_tailFlag hani ha₀ hk hW
    refine ⟨⟨g, hg⟩⁻¹, funext fun i => ?_⟩
    change (tailFlag K A r (i + 1)).map _ = W i
    rw [← hgW i]
    exact map_map_inv (W i) g

theorem index_orthParab_eq_card_singularFlags [FiniteDimensional K A] (hani : qA.Anisotropic)
    {a₀ : A} (ha₀ : a₀ ≠ 0) {k : ℕ} (hk : k ≤ r) :
    (orthParab r qA (fun i : Fin (k + 1) => (i : ℕ))).index =
      Nat.card (singularFlags (quadTail r qA) k) := by
  rw [← stabilizer_tailStdFlag, MulAction.index_stabilizer, orbit_tailStdFlag hani ha₀ hk,
    Nat.card_coe_set_eq]

theorem omegaMinusFlagIndex_eq_prod_range (s : ℕ) :
    (omegaMinusFlagIndex (s + 3) : ℚ) =
      ∏ j ∈ Finset.range s, (((2 : ℚ) ^ (s + 2 - j) - 1) * ((2 : ℚ) ^ (s + 3 - j) + 1)) := by
  induction s with
  | zero => simp [omegaMinusFlagIndex]
  | succ s ih =>
    rw [Finset.prod_range_succ', ← Finset.prod_congr rfl fun j _ => by
      rw [show s + 1 + 2 - (j + 1) = s + 2 - j by omega,
        show s + 1 + 3 - (j + 1) = s + 3 - j by omega], ← ih, omegaMinusFlagIndex,
      omegaMinusFlagIndex, show s + 1 + 3 = s + 3 + 1 by omega,
      Finset.prod_Icc_succ_top (by omega : 4 ≤ s + 3 + 1)]
    push_cast [Nat.cast_sub Nat.one_le_two_pow]
    ring_nf

theorem card_singularFlags_minus_two {K : Type} [Field K] [Finite K] {b c : K}
    (hK : Nat.card K = 2) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (s : ℕ) :
    Nat.card (singularFlags (quadTail (s + 2) (minusTailForm K b c)) s) =
      omegaMinusFlagIndex (s + 3) := by
  have h := card_singularFlags_tail (anisotropic_minusTailForm hirr)
    (nondegenerate_minusTailForm hirr) (k := s) (r := s + 2) (by omega)
  rw [finrank_fin_two_fun, hK] at h
  have h' : (Nat.card (singularFlags (quadTail (s + 2) (minusTailForm K b c)) s) : ℚ) =
      omegaMinusFlagIndex (s + 3) := by
    rw [h, omegaMinusFlagIndex_eq_prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show s + 2 + 2 - j - 1 = s + 3 - j by omega]
    push_cast
    ring
  exact_mod_cast h'

theorem index_orthParab_minus_two {K : Type} [Field K] [Finite K] {b c : K}
    (hK : Nat.card K = 2) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (s : ℕ) :
    (orthParab (s + 2) (minusTailForm K b c) (fun i : Fin (s + 1) => (i : ℕ))).index =
      omegaMinusFlagIndex (s + 3) := by
  have ha₀ : (Pi.single 0 1 : Fin 2 → K) ≠ 0 := fun h => by simpa using congrFun h 0
  rw [index_orthParab_eq_card_singularFlags (anisotropic_minusTailForm hirr) ha₀ (by omega),
    card_singularFlags_minus_two hK hirr]

end CFSG.AGLEmbedding.LeviBlock
