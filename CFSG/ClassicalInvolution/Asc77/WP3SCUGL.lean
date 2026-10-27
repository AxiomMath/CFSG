module

public import CFSG.ClassicalInvolution.Balance.StrongPowDiagLinear

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)
open CFSG.ClassicalInvolution.Balance.StrongBalance
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.ClassicalInvolution.RouteD.Gaps (LinearAutClassification diagGL)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open scoped MatrixGroups

variable {n : ℕ} {k : Type} [Field k] {X : Type} [Group X]

theorem commutator_trivial_gl [Finite k] [Finite X] (hn : 3 ≤ n) (h2 : (2 : k) ≠ 0)
    (h4 : 4 ≤ Nat.card k) (hcl : LinearAutClassification k n) (ψ : SL(n, k) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, k)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (htoral : ToralDiagGL 2 ψ F) {f : X} (hf : f ∈ F) {d : X}
    (hd : d ∈ involutionOddCore f) {g : X} (hg : g ∈ F) {x : X} (hx : x ∈ ψ.range) :
    d * g * x * (d * g)⁻¹ = g * d * x * (g * d)⁻¹ := by
  obtain ⟨P₀, σ₁, σ₂, hch₁, hch₂⟩ := exists_chart_of_lifts_gl (by omega) h2 ψ htoral hf hg
  have hrange : (ψ.comp (MulAut.conj P₀).toMonoidHom).range = ψ.range :=
    CFSG.ClassicalInvolution.Balance.range_comp_conj ψ P₀
  have hΨnorm : (ψ.comp (MulAut.conj P₀).toMonoidHom).range.Normal := by
    rw [hrange]
    exact hnorm
  obtain ⟨u, -, hu⟩ := act_diagonal_of_mem_involutionOddCore hn h2 h4 hcl _
    (ker_comp_conj_le_center ψ hker P₀) hΨnorm f σ₁ hch₁ hd
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  have e1 : d * g * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * (d * g)⁻¹ =
      d * (g * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * g⁻¹) * d⁻¹ := by group
  have e2 : g * d * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * (g * d)⁻¹ =
      g * (d * (ψ.comp (MulAut.conj P₀).toMonoidHom) y * d⁻¹) * g⁻¹ := by group
  rw [e1, e2, hch₂ y, hu (slConjugation n k (signGL k σ₂) y), hu y,
    hch₂ (slConjugation n k (diagGL u) y)]
  exact congrArg _ (slConjugation_diagGL_comm u (fun i => signUnit k (σ₂ i)) y)

theorem strongConclusion_gl [Finite k] [Finite X] (hn : 3 ≤ n) (h2 : (2 : k) ≠ 0)
    (h4 : 4 ≤ Nat.card k) (hcl : LinearAutClassification k n) (ψ : SL(n, k) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, k)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (htoral : ToralDiagGL 2 ψ F) : StrongConclusion ψ.range F :=
  ⟨fun _ hd _ hx => deltaCore_trivial_gl hn h2 h4 hcl ψ hker hnorm hcard hF2 htoral hd hx,
    fun _ hf _ _ hd _ hg _ hx => commutator_trivial_gl hn h2 h4 hcl ψ hker hnorm htoral hf hd hg hx⟩

variable {p e : ℕ} [Fact p.Prime]

theorem strongConclusion_gf_diag {n : ℕ} (hn : 3 ≤ n) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) {X : Type}
    [Group X] [Finite X] (ψ : SL(n, GaloisField p e) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, GaloisField p e)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (htoral : ToralDiagGL 2 ψ F) : StrongConclusion ψ.range F := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  exact strongConclusion_gl hn (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2)
    h4 (CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification hp2 h5 hn) ψ hker
    hnorm hcard hF2 htoral

end CFSG.ClassicalInvolution.Asc77
