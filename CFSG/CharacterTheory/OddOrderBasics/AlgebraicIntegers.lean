module

public import Mathlib.NumberTheory.Niven
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_1

public section

namespace CFSG.OddOrderBasics

theorem integer_matrix_eigenvalue_isIntegral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (z : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (hMv : (M.map (Int.cast : ℤ → ℂ)).mulVec v = z • v) : IsIntegral ℤ z := by
  have hdet : (Matrix.scalar ι z - M.map (Int.cast : ℤ → ℂ)).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, hMv, Matrix.scalar_apply]
    ext i
    simp
  refine ⟨M.charpoly, Matrix.charpoly_monic M, ?_⟩
  rw [← Polynomial.eval_map, algebraMap_int_eq, ← Matrix.charpoly_map M (Int.castRingHom ℂ),
    Matrix.eval_charpoly]
  exact hdet

theorem algebraic_integer_calculus :
    (∀ n : ℤ, (n : ℂ) ∈ integralClosure ℤ ℂ) ∧
    (∀ a ∈ integralClosure ℤ ℂ, ∀ b ∈ integralClosure ℤ ℂ,
      a + b ∈ integralClosure ℤ ℂ ∧ a - b ∈ integralClosure ℤ ℂ ∧
        a * b ∈ integralClosure ℤ ℂ) ∧
    (∀ a ∈ integralClosure ℤ ℂ, starRingEnd ℂ a ∈ integralClosure ℤ ℂ) ∧
    {z : ℂ | z ∈ integralClosure ℤ ℂ} ∩ Set.range ((↑) : ℚ → ℂ) =
      Set.range ((↑) : ℤ → ℂ) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (z : ℂ) (v : ι → ℂ),
      v ≠ 0 → (M.map (Int.cast : ℤ → ℂ)).mulVec v = z • v → z ∈ integralClosure ℤ ℂ) ∧
    ∀ n : ℤ, 1 ≤ n →
      {z : ℂ | ∃ a ∈ integralClosure ℤ ℂ, z = n * a} ∩ Set.range ((↑) : ℚ → ℂ) =
        Set.range fun m : ℤ => ((n * m : ℤ) : ℂ) := by
  have hint : ∀ n : ℤ, (n : ℂ) ∈ integralClosure ℤ ℂ := fun n =>
    (mem_integralClosure_iff ℤ ℂ).mpr isIntegral_algebraMap
  have hrat : ∀ z : ℂ, z ∈ integralClosure ℤ ℂ → (∃ q : ℚ, z = q) → ∃ m : ℤ, z = m :=
    fun z hz hq => (IsIntegral.exists_int_iff_exists_rat ((mem_integralClosure_iff ℤ ℂ).mp hz)).mp
      hq
  refine ⟨hint, fun a ha b hb => ⟨add_mem ha hb, sub_mem ha hb, mul_mem ha hb⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [mem_integralClosure_iff] at ha ⊢
    exact ha.map (starRingEnd ℂ).toIntAlgHom
  · ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨hz, q, rfl⟩
      obtain ⟨m, hm⟩ := hrat _ hz ⟨q, rfl⟩
      exact ⟨m, hm.symm⟩
    · rintro ⟨m, rfl⟩
      exact ⟨hint m, m, by push_cast; rfl⟩
  · intro ι _ _ M z v hv hMv
    exact (mem_integralClosure_iff ℤ ℂ).mpr (integer_matrix_eigenvalue_isIntegral M z v hv hMv)
  · intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, q, hq⟩
      have haq : a = ((q / n : ℚ) : ℂ) := by
        push_cast
        rw [hq]
        field_simp
      obtain ⟨m, hm⟩ := hrat a ha ⟨_, haq⟩
      exact ⟨m, by rw [hm]; push_cast; ring⟩
    · rintro ⟨m, rfl⟩
      exact ⟨⟨m, hint m, by push_cast; ring⟩, n * m, by push_cast; ring⟩

theorem character_values_algebraic_integer {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g ∈ integralClosure ℤ ℂ :=
  (mem_integralClosure_iff ℤ ℂ).mpr (ρ.isIntegral_character g)

theorem complex_character_inversion {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = starRingEnd ℂ (ρ.character g) :=
  Section1.representation_character_inv_eq_star_character ρ g

end CFSG.OddOrderBasics
