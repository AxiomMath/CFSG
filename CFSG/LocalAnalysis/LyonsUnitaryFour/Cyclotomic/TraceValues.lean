module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.FrobeniusResidue
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Induction
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.WittVector.IsPoly

public section

namespace CFSG.LyonsUnitaryFour

open IntermediateField

variable {N k : ℕ} {ζ : ℂ}

theorem mem_adjoin_of_pow_eq_one [NeZero N] (hζ : IsPrimitiveRoot ζ N) {μ : ℂ}
    (hμ : μ ^ N = 1) : μ ∈ ℚ⟮ζ⟯ := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  exact pow_mem (mem_adjoin_simple_self ℚ ζ) i

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem trace_pow_mem_adjoin [NeZero N] (hζ : IsPrimitiveRoot ζ N) {f : Module.End ℂ V}
    (hf : f ^ N = 1) (j : ℕ) : LinearMap.trace ℂ V (f ^ j) ∈ ℚ⟮ζ⟯ := by
  classical
  rw [CFSG.Theory.Representation.trace_pow_eq_sum_eigenvalues (NeZero.ne N) hf]
  refine sum_mem fun μ _ => mul_mem (pow_mem (mem_adjoin_of_pow_eq_one hζ ?_) j)
    (IntermediateField.natCast_mem _ _)
  exact CFSG.Theory.Representation.eigenvalue_pow_eq_one_of_pow_eq_one hf μ.property

theorem trace_mem_adjoin [NeZero N] (hζ : IsPrimitiveRoot ζ N) {f : Module.End ℂ V}
    (hf : f ^ N = 1) : LinearMap.trace ℂ V f ∈ ℚ⟮ζ⟯ := by
  simpa using trace_pow_mem_adjoin hζ hf 1

theorem galois_trace_eq [NeZero N] (hζ : IsPrimitiveRoot ζ N) {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯}
    (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) {f : Module.End ℂ V} (hf : f ^ N = 1) :
    ((σ ⟨LinearMap.trace ℂ V f, trace_mem_adjoin hζ hf⟩ : ℚ⟮ζ⟯) : ℂ) =
      LinearMap.trace ℂ V (f ^ k) := by
  classical
  let : Fintype f.Eigenvalues := Fintype.ofFinite _
  have hroot : ∀ μ : f.Eigenvalues, (μ : ℂ) ^ N = 1 := fun μ =>
    CFSG.Theory.Representation.eigenvalue_pow_eq_one_of_pow_eq_one hf μ.property
  let S : ℚ⟮ζ⟯ := ∑ μ : f.Eigenvalues,
    (⟨(μ : ℂ), mem_adjoin_of_pow_eq_one hζ (hroot μ)⟩ : ℚ⟮ζ⟯) *
      (Module.finrank ℂ (f.eigenspace (μ : ℂ)) : ℚ⟮ζ⟯)
  have hS : (⟨LinearMap.trace ℂ V f, trace_mem_adjoin hζ hf⟩ : ℚ⟮ζ⟯) = S := by
    apply Subtype.ext
    have := CFSG.Theory.Representation.trace_pow_eq_sum_eigenvalues (k := 1) (NeZero.ne N) hf
    simp only [pow_one] at this
    change LinearMap.trace ℂ V f = (S : ℂ)
    rw [this]
    simp only [S, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    push_cast
    rfl
  rw [hS, CFSG.Theory.Representation.trace_pow_eq_sum_eigenvalues (NeZero.ne N) hf]
  simp only [S, map_sum, map_mul, map_natCast]
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [galois_apply_of_pow_eq_one hζ hσ (Subtype.ext (by simpa using hroot μ))]
  simp

theorem character_mem_adjoin [NeZero N] (hζ : IsPrimitiveRoot ζ N) {G : Type*} [Group G]
    (ρ : Representation ℂ G V) {g : G} (hg : g ^ N = 1) : ρ.character g ∈ ℚ⟮ζ⟯ :=
  trace_mem_adjoin hζ (f := ρ g) (by rw [← map_pow, hg, map_one])

theorem galois_character_eq [NeZero N] (hζ : IsPrimitiveRoot ζ N) {σ : ℚ⟮ζ⟯ ≃ₐ[ℚ] ℚ⟮ζ⟯}
    (hσ : (σ (AdjoinSimple.gen ℚ ζ) : ℂ) = ζ ^ k) {G : Type*} [Group G]
    (ρ : Representation ℂ G V) {g : G} (hg : g ^ N = 1) :
    ((σ ⟨ρ.character g, character_mem_adjoin hζ ρ hg⟩ : ℚ⟮ζ⟯) : ℂ) = ρ.character (g ^ k) := by
  have := galois_trace_eq hζ hσ (f := ρ g) (by rw [← map_pow, hg, map_one])
  calc ((σ ⟨ρ.character g, character_mem_adjoin hζ ρ hg⟩ : ℚ⟮ζ⟯) : ℂ) =
      LinearMap.trace ℂ V (ρ g ^ k) := this
    _ = ρ.character (g ^ k) := by
      change _ = LinearMap.trace ℂ V (ρ (g ^ k))
      rw [map_pow ρ]

end CFSG.LyonsUnitaryFour
