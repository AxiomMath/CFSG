module

public import CFSG.ClassicalInvolution.Phan.PhanQ14PentW0
public import CFSG.ClassicalInvolution.Phan.PhanQ6Bwd
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
public import CFSG.ClassicalInvolution.Phan.PhanQ12KData

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs

section Std

variable {p e : ℕ} [Fact p.Prime]

theorem pairPent_std (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (a c d : NPair M.ε)
    (hcd : ColP M.ε c d) : ∃ f : NPair M.ε, ColP M.ε f c ∧ ColP M.ε f d ∧ ColP M.ε a f := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have h2 := two_ne_zero_gf hp2 e
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  obtain ⟨g₁, hg₁⟩ := exists_smul_z0 h2 hodd M.hε M.h4 c
  have hcol1 : ColP M.ε (z0 M.ε) (g₁⁻¹ • d) := by
    have := (colP_smul g₁⁻¹).2 hcd
    rwa [← hg₁, NPair.inv_smul_smul'] at this
  obtain ⟨g, hgz, N, hN, hgx, hgy⟩ := exists_normal_pair M hp2 hq hcol1
  have hc' : (g * g₁⁻¹) • c = z0 M.ε := by
    rw [NPair.mul_smul', ← hg₁, NPair.inv_smul_smul', hgz]
  have hcolh : ColP M.ε (z0 M.ε) (g • (g₁⁻¹ • d)) := by
    have := (colP_smul (g * g₁⁻¹)).2 hcd
    rwa [hc', NPair.mul_smul' g g₁⁻¹ d] at this
  have hinz : InW0 (z0 M.ε).x ∧ InW0 (z0 M.ε).y := by
    rw [z0_x_eq, z0_y_eq]
    exact ⟨inW0_incl _, inW0_incl _⟩
  have hind : InW0 (g • (g₁⁻¹ • d)).x ∧ InW0 (g • (g₁⁻¹ • d)).y := by
    rw [hgx, hgy]
    exact ⟨inW0_incl _, inW0_incl _⟩
  have hF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hK := StdModel.card_K hq
  let _ : Algebra (GaloisField p e) (GaloisField p (2 * e)) := (Aniso.nonempty_algebra hF hK).some
  obtain ⟨D⟩ := exists_kdata (F := GaloisField p e) (K := GaloisField p (2 * e)) p e hF hK hp2
    M.hε M.nonsq
  have := Fintype.ofFinite (GaloisField p (2 * e))
  classical
  have h2K := two_ne_zero_gf hp2 (2 * e)
  have hq2 : 2 ≤ Nat.card (GaloisField p e) := by omega
  have hq5 : 4 * (Nat.card (GaloisField p e) + 1) < Nat.card (GaloisField p e) ^ 2 := by
    rw [hF]
    nlinarith
  obtain ⟨f', h1, h2', h3⟩ := exists_pent_inW0 D hodd h2K M.hε hq2 hq5 hinz hind hcolh
    ((g * g₁⁻¹) • a)
  refine ⟨(g * g₁⁻¹)⁻¹ • f', ?_, ?_, ?_⟩
  · rw [← colP_smul (g * g₁⁻¹), NPair.smul_inv_smul', hc']
    exact h1
  · rw [← colP_smul (g * g₁⁻¹), NPair.smul_inv_smul', NPair.mul_smul' g g₁⁻¹ d]
    exact h2'
  · rw [← colP_smul (g * g₁⁻¹), NPair.smul_inv_smul']
    exact h3

end Std

end CFSG.ClassicalInvolution.PhanQ
