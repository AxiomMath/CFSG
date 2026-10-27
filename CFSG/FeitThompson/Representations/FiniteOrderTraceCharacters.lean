module
public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Polynomial

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V] {g : G}

def irreducibleCharacters (G : Type*) [Group G] : Set (G → ℂ) :=
  {χ | ∃ W : FDRep ℂ G, Representation.IsIrreducible W.ρ ∧ W.character = χ}

theorem mem_irreducibleCharacters_iff {χ : G → ℂ} :
    χ ∈ irreducibleCharacters G ↔
      ∃ W : FDRep ℂ G, Representation.IsIrreducible W.ρ ∧ W.character = χ := Iff.rfl

theorem Representation.character_mem_irreducibleCharacters {V : Type} [AddCommGroup V]
    [Module ℂ V] [Module.Finite ℂ V] (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) :
    ρ.character ∈ irreducibleCharacters G := by
  refine ⟨FDRep.of ρ, ?_, ?_⟩
  · rw [FDRep.of_ρ']; exact h
  · funext g; rw [FDRep.character, FDRep.of_ρ']; rfl

theorem Representation.nontrivial_of_isIrreducible (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) : Nontrivial V := by
  have h1 : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  rw [Ne, Subrepresentation.ext_iff] at h1
  rcases subsingleton_or_nontrivial V with hs | hn
  · exact absurd (Subsingleton.elim _ _) h1
  · exact hn

theorem irreducibleCharacters.one_pos {χ : G → ℂ} (hχ : χ ∈ irreducibleCharacters G) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = n := by
  obtain ⟨W, hW, rfl⟩ := hχ
  have : Nontrivial W.V := Representation.nontrivial_of_isIrreducible _ hW
  exact ⟨finrank ℂ W.V, finrank_pos, W.char_one⟩

variable [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

omit [FiniteDimensional ℂ V] in
theorem Representation.isSemisimple_apply_of_isOfFinOrder (hg : IsOfFinOrder g) :
    Module.End.IsSemisimple (ρ g) := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := X ^ orderOf g - 1) ?_ ?_
  · exact (Polynomial.X_pow_sub_one_separable_iff.2 (by
      simpa using (Nat.cast_ne_zero (R := ℂ)).2 hg.orderOf_pos.ne')).squarefree
  · have h : (ρ g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    simp [h]

omit [FiniteDimensional ℂ V] in
theorem Representation.pow_orderOf_eq_one_of_hasEigenvalue {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (ρ g) μ) : μ ^ orderOf g = 1 := by
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have h1 : ((ρ g) ^ orderOf g) v = μ ^ orderOf g • v :=
    Module.End.HasEigenvector.pow_apply ⟨hv, hv0⟩ _
  rw [show ((ρ g) ^ orderOf g) = 1 by rw [← map_pow, pow_orderOf_eq_one, map_one]] at h1
  have h2 : (μ ^ orderOf g - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1]; simp
  rcases smul_eq_zero.1 h2 with h | h
  · linear_combination (norm := ring_nf) h
  · exact absurd h hv0

theorem Representation.exists_basis_eigenvector (hg : IsOfFinOrder g) :
    ∃ (b : Basis (Fin (finrank ℂ V)) ℂ V) (d : Fin (finrank ℂ V) → ℂ),
      (∀ i, ρ g (b i) = d i • b i) ∧ ∀ i, d i ^ orderOf g = 1 := by
  classical
  have hint : DirectSum.IsInternal (Module.End.eigenspace (ρ g)) := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨Module.End.eigenspaces_iSupIndep _,
      (Representation.isSemisimple_apply_of_isOfFinOrder ρ hg).iSup_eigenspace_eq_top⟩
  set b0 := hint.collectedBasis fun μ => Module.Free.chooseBasis ℂ (Module.End.eigenspace (ρ g) μ)
    with hb0
  have key : ∀ a, ρ g (b0 a) = a.1 • b0 a := by
    intro a
    rw [← Module.End.mem_eigenspace_iff, hb0]
    exact hint.collectedBasis_mem _ a
  have hFin : Fintype _ := FiniteDimensional.fintypeBasisIndex b0
  let _ := hFin
  have hcard : Fintype.card _ = finrank ℂ V := (Module.finrank_eq_card_basis b0).symm
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨b0.reindex e, fun i => (e.symm i).1, fun i => ?_, fun i => ?_⟩
  · rw [Basis.reindex_apply]; exact key _
  · exact Representation.pow_orderOf_eq_one_of_hasEigenvalue ρ
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 (key (e.symm i)), b0.ne_zero _⟩)

omit [FiniteDimensional ℂ V] in
theorem Representation.character_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ V) (d : ι → ℂ) (h : ∀ i, ρ g (b i) = d i • b i) :
    ρ.character g = ∑ i, d i := by
  classical
  have hm : LinearMap.toMatrix b b (ρ g) = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix_apply, h j, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one, Finsupp.single_apply, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij, eq_comm]
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b, hm, Matrix.trace_diagonal]

theorem Representation.norm_character_le_finrank (hg : IsOfFinOrder g) :
    ‖ρ.character g‖ ≤ (finrank ℂ V : ℝ) := by
  obtain ⟨b, d, hd, hpow⟩ := Representation.exists_basis_eigenvector ρ hg
  have hn : orderOf g ≠ 0 := hg.orderOf_pos.ne'
  have hnorm : ∀ i, ‖d i‖ = 1 := fun i => Complex.norm_eq_one_of_pow_eq_one (hpow i) hn
  calc ‖ρ.character g‖ = ‖∑ i, d i‖ := by
        rw [Representation.character_eq_sum_of_eigenbasis ρ b d hd]
    _ ≤ ∑ i, ‖d i‖ := norm_sum_le _ _
    _ = (finrank ℂ V : ℝ) := by simp [hnorm]

theorem Representation.character_inv (hg : IsOfFinOrder g) :
    ρ.character g⁻¹ = starRingEnd ℂ (ρ.character g) := by
  obtain ⟨b, d, hd, hpow⟩ := Representation.exists_basis_eigenvector ρ hg
  have hn : orderOf g ≠ 0 := hg.orderOf_pos.ne'
  have hnorm : ∀ i, ‖d i‖ = 1 := fun i => Complex.norm_eq_one_of_pow_eq_one (hpow i) hn
  have hne : ∀ i, d i ≠ 0 := fun i => norm_ne_zero_iff.1 (by rw [hnorm i]; norm_num)
  have hinv : ∀ i, ρ g⁻¹ (b i) = (d i)⁻¹ • b i := by
    intro i
    have h1 : d i • ρ g⁻¹ (b i) = b i := by
      have h2 := ρ.inv_self_apply g (b i)
      rwa [hd i, map_smul] at h2
    calc ρ g⁻¹ (b i) = (d i)⁻¹ • (d i • ρ g⁻¹ (b i)) := by
          rw [smul_smul, inv_mul_cancel₀ (hne i), one_smul]
      _ = (d i)⁻¹ • b i := by rw [h1]
  rw [Representation.character_eq_sum_of_eigenbasis ρ b _ hinv,
    Representation.character_eq_sum_of_eigenbasis ρ b d hd, map_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.inv_eq_conj (hnorm i)

theorem Representation.character_eq_finrank_iff (hg : IsOfFinOrder g) :
    ρ.character g = (finrank ℂ V : ℂ) ↔ ρ g = 1 := by
  constructor
  · intro h
    obtain ⟨b, d, hd, hpow⟩ := Representation.exists_basis_eigenvector ρ hg
    have hn : orderOf g ≠ 0 := hg.orderOf_pos.ne'
    have hnorm : ∀ i, ‖d i‖ = 1 := fun i => Complex.norm_eq_one_of_pow_eq_one (hpow i) hn
    have hsum : ∑ i, (d i).re = ∑ _i : Fin (finrank ℂ V), (1 : ℝ) := by
      have h1 := Representation.character_eq_sum_of_eigenbasis ρ b d hd
      rw [h] at h1
      simpa [Complex.re_sum] using congrArg Complex.re h1.symm
    have hle : ∀ i ∈ Finset.univ, (d i).re ≤ (1 : ℝ) := fun i _ => by
      simpa [hnorm i] using Complex.re_le_norm (d i)
    have hre := (Finset.sum_eq_sum_iff_of_le hle).1 hsum
    have hd1 : ∀ i, d i = 1 := by
      intro i
      have h1 : (d i).re = 1 := hre i (Finset.mem_univ i)
      have h2 : (d i).im = 0 := by
        nlinarith [Complex.normSq_apply (d i), Complex.normSq_eq_norm_sq (d i),
          sq_nonneg (d i).im, hnorm i]
      exact Complex.ext (by simpa using h1) (by simpa using h2)
    refine b.ext fun i => ?_
    rw [hd i, hd1 i, one_smul, Module.End.one_eq_id, LinearMap.id_apply]
  · intro h
    rw [Representation.character, h, Module.End.one_eq_id, LinearMap.trace_id]

theorem Representation.character_eq_finrank_iff_of_finite [Finite G] :
    ρ.character g = (finrank ℂ V : ℂ) ↔ ρ g = 1 :=
  Representation.character_eq_finrank_iff ρ (isOfFinOrder_of_finite g)

end CFSG.FeitThompson
