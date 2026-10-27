module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3D4Compat
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Scalar

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3.D4

open CFSG.Blueprint.Chevalley Matrix

variable (K : Type) [Field K]

abbrev adj8 (a b : Fin 8) : Prop := a ≠ b ∧ a.val % 4 ≠ b.val % 4

theorem adj8_symm : ∀ a b : Fin 8, adj8 a b → adj8 b a := by decide +kernel

theorem adj8_irr : ∀ a : Fin 8, ¬ adj8 a a := by decide +kernel

theorem adj8_two : ∀ a : Fin 8, ∃ b c : Fin 8, b ≠ c ∧ adj8 a b ∧ adj8 a c := by
  decide +kernel

theorem adj8_tri : ∀ a : Fin 8, ∃ b c : Fin 8, adj8 a b ∧ adj8 b c ∧ adj8 a c := by
  decide +kernel

theorem adj8_diam : ∀ a b : Fin 8, a ≠ b → adj8 a b ∨ ∃ c : Fin 8, adj8 a c ∧ adj8 c b := by
  decide +kernel

theorem edge_root_all : ∀ a b : Fin 8, adj8 a b →
    ∃ α ∈ d4Roots, phiRootZ α = W a b ∨ phiRootZ α = -W a b := by
  decide +kernel

theorem castM_E (r s : Fin 8) : castM K (E r s) = Matrix.single r s (1 : K) := by
  ext i j
  simp [castM, E, Matrix.single_apply]

theorem castM_W (a b : Fin 8) :
    castM K (W a b) = Matrix.single a b (1 : K) - Matrix.single b a 1 := by
  rw [W, map_sub, castM_E, castM_E]

theorem fix_of_intertwiner (H : Matrix (Fin 8) (Fin 8) K)
    (hh : rho K H ∘ₗ phi K = phi K) (β : Fin 4 → ℤ) :
    H * castM K (phiRootZ β) * Hᵀ = castM K (phiRootZ β) := by
  have h := LinearMap.congr_fun hh (rootVec Tag.D4 K β)
  rw [LinearMap.comp_apply, phi_rootVec, rho_apply] at h
  exact h

theorem fix_edge (H : Matrix (Fin 8) (Fin 8) K)
    (hH : ∀ β : Fin 4 → ℤ, H * castM K (phiRootZ β) * Hᵀ = castM K (phiRootZ β))
    {a b : Fin 8} (hab : adj8 a b) :
    H * (Matrix.single a b (1 : K) - Matrix.single b a 1) * Hᵀ =
      Matrix.single a b 1 - Matrix.single b a 1 := by
  rcases edge_root_all a b hab with ⟨α, -, hα | hα⟩
  · have h := hH α
    rwa [hα, castM_W] at h
  · have h := hH α
    rw [hα, map_neg, castM_W, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
    exact h

theorem phi_fix_scalar (h : GL (Fin 8) K)
    (hh : rho K (h : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K = phi K) :
    h ∈ Subgroup.center (GL (Fin 8) K) := by
  obtain ⟨l, -, hl⟩ := scalar_of_fixes_edges adj8 adj8_symm adj8_irr adj8_two adj8_tri
    adj8_diam (h : Matrix (Fin 8) (Fin 8) K)
    (fun _ _ hab => fix_edge K _ (fix_of_intertwiner K _ hh) hab)
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hl, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul]

end CFSG.ComponentClassification.CatFC.KGHS3.D4
