module

public import CFSG.ClassicalInvolution.Phan.PhanS13BDiag

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3

section Main

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))}

theorem exists_mem_U1_move (S : Setup M E D) {β γ : GaloisField p (2 * f)}
    (hff : IsFF7 D (β • vE2 D + γ • vE3 D)) :
    ∃ u ∈ (E.ι 1).range, ∃ c' : GaloisField p (2 * f), c' ≠ 0 ∧
      actK u (vE2 D) = c' • (β • vE2 D + γ • vE3 D) ∧ actK u (vXi D) = vXi D := by
  obtain ⟨A, c', hc', hA⟩ := S.n1.move β γ hff
  obtain ⟨hmap, -⟩ := U1_spec M.D S.h4
  have hmem : La1 h2 A ∈ (fr1 h2).La.range := ⟨A, rfl⟩
  rw [← hmap] at hmem
  obtain ⟨u, hu, hu'⟩ := hmem
  have hu1 : u ∈ (E.ι 1).range := by
    rw [S.range 1]
    exact hu
  exact ⟨u, hu1, c', hc', by rw [actK_eq_of_spinAction_eq hu']; exact hA,
    by rw [actK_eq_of_spinAction_eq hu']; exact S.n1.fix_vXi A⟩

theorem exists_diag_of_lineFix (S : Setup M E D)
    (hA : ∀ g ∈ (E.ι 0).range ⊔ (E.ι 1).range, PiDetOne D g)
    {g : spinGroup (quadOdd 3 (GaloisField p f))} (hg : g ∈ (E.ι 0).range ⊔ (E.ι 1).range)
    (hl : LineFix g (vXi D)) :
    ∃ u ∈ (E.ι 1).range, ∃ l₁ l₂ l₃ : GaloisField p (2 * f),
      l₁ * D.τ l₁ = 1 ∧ l₂ * D.τ l₂ = 1 ∧ l₃ * D.τ l₃ = 1 ∧ l₁ * l₂ * l₃ = 1 ∧
        actK (u⁻¹ * g) (vXi D) = l₁ • vXi D ∧ actK (u⁻¹ * g) (vE2 D) = l₂ • vE2 D ∧
          actK (u⁻¹ * g) (vE3 D) = l₃ • vE3 D := by
  have h2K := S.h2K
  obtain ⟨β, γ, hy⟩ := exists_vE2_comb_of_lineFix D h2K (hA g hg) hl
  obtain ⟨c, hc, e1⟩ := hl
  have hff : IsFF7 D (β • vE2 D + γ • vE3 D) := by
    rw [← hy]
    exact isFF7_actK D h2K g (isFF7_vE2 D h2K)
  obtain ⟨u, hu, c', hc', hu2, hu1⟩ := exists_mem_U1_move S hff
  have hg' : u⁻¹ * g ∈ (E.ι 0).range ⊔ (E.ι 1).range :=
    mul_mem (inv_mem (Subgroup.mem_sup_right hu)) hg
  have f1 : actK (u⁻¹ * g) (vXi D) = c • vXi D := by
    rw [actK_mul, e1, map_smul, actK_inv_of_eigen one_ne_zero (by rw [one_smul]; exact hu1),
      inv_one, one_smul]
  have f2 : actK (u⁻¹ * g) (vE2 D) = c'⁻¹ • vE2 D := by
    rw [actK_mul, hy]
    calc actK u⁻¹ (β • vE2 D + γ • vE3 D)
        = actK u⁻¹ (c'⁻¹ • (c' • (β • vE2 D + γ • vE3 D))) := by
          rw [smul_smul, inv_mul_cancel₀ hc', one_smul]
      _ = c'⁻¹ • vE2 D := by rw [← hu2, map_smul, actK_inv_actK]
  obtain ⟨l₃, n1, n2, n3, hprod, f3⟩ :=
    diag_of_eigen_of_piDetOne D h2K (hA _ hg') hc (inv_ne_zero hc') f1 f2
  exact ⟨u, hu, c, c'⁻¹, l₃, n1, n2, n3, hprod, f1, f2, f3⟩

end Main

end CFSG.ClassicalInvolution.PhanB3.S
