module

public import CFSG.ClassicalInvolution.Balance.StrongPowDiagUnitary

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)
open CFSG.ClassicalInvolution.Balance.StrongBalance
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.ClassicalInvolution.Models (signOf)

variable {K : Type} [Field K] [Finite K] {n : ℕ} {p f : ℕ} [Fact p.Prime] [CharP K p]
  {X : Type} [Group X] [Finite X]

theorem commutator_trivial_gu (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hn : 3 ≤ n) (ψ : Su K p f n →* X) (hker : ψ.ker ≤ Subgroup.center (Su K p f n))
    (hnorm : ψ.range.Normal) {F : Subgroup X} (htoral : ToralDiagGU 2 ψ F) {f₀ : X}
    (hf₀ : f₀ ∈ F) {d : X} (hd : d ∈ involutionOddCore f₀) {g₀ : X} (hg₀ : g₀ ∈ F) {x : X}
    (hx : x ∈ ψ.range) : d * g₀ * x * (d * g₀)⁻¹ = g₀ * d * x * (g₀ * d)⁻¹ := by
  obtain ⟨P, hP, hact⟩ := htoral
  obtain ⟨x₁, hx₁P, hx₁sq, hx₁⟩ := hact f₀ hf₀
  obtain ⟨x₂, hx₂P, hx₂sq, hx₂⟩ := hact g₀ hg₀
  obtain ⟨P₀, D₁, D₂, σ₁, σ₂, hD₁, hD₂, hch₁, hch₂⟩ := exists_chart_gu hK hp2 (by omega) ψ hx₁ hx₂
    (by rwa [← pow_two]) (by rwa [← pow_two]) (hP x₁ hx₁P x₂ hx₂P)
  set Ψ' : Su K p f n →* X := ψ.comp (MulAut.conj P₀).toMonoidHom with hΨ'
  have hrange : Ψ'.range = ψ.range := CFSG.ClassicalInvolution.Balance.range_comp_conj ψ P₀
  have hΨnorm : Ψ'.range.Normal := by
    rw [hrange]
    exact hnorm
  have hΨker := CFSG.ClassicalInvolution.Balance.StrongBalance.Linear.ker_comp_conj_le_center ψ
    hker P₀
  obtain ⟨u, α, -, hαΨ, hαmat⟩ := act_diagonal_gu hK hp2 hq hn Ψ' hΨker hΨnorm f₀ σ₁
    (D₁ : GL (Fin n) K) (conjSUid (unitaryInvolution K p f) n D₁) hD₁
    (fun y => coe_conjSUid _ n D₁ y) hch₁ hd
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  have e1 : d * g₀ * Ψ' y * (d * g₀)⁻¹ = d * (g₀ * Ψ' y * g₀⁻¹) * d⁻¹ := by group
  have e2 : g₀ * d * Ψ' y * (g₀ * d)⁻¹ = g₀ * (d * Ψ' y * d⁻¹) * g₀⁻¹ := by group
  have hD₂inv : ((D₂ : GL (Fin n) K))⁻¹ = (D₂ : GL (Fin n) K) := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, hD₂, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    cases σ₂ i <;> simp [signOf]
  have hcomm : α (conjSUid (unitaryInvolution K p f) n D₂ y) =
      conjSUid (unitaryInvolution K p f) n D₂ (α y) := by
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    rw [hαmat, coe_conjSUid, coe_conjSUid, hD₂inv]
    simp only [Units.val_mul, hD₂, diagonal_mul, mul_diagonal, hαmat]
    ring
  rw [e1, e2, hch₂ y, ← hαΨ (conjSUid (unitaryInvolution K p f) n D₂ y), ← hαΨ y,
    hch₂ (α y), hcomm]

theorem strongConclusion_gu (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hn : 3 ≤ n) (ψ : Su K p f n →* X) (hker : ψ.ker ≤ Subgroup.center (Su K p f n))
    (hnorm : ψ.range.Normal) {F : Subgroup X} (hcard : Nat.card F = 4)
    (hF2 : ∀ f' ∈ F, f' * f' = 1) (htoral : ToralDiagGU 2 ψ F) : StrongConclusion ψ.range F :=
  ⟨fun _ hd _ hx => deltaCore_trivial_gu hK hp2 hq hn ψ hker hnorm hcard hF2 htoral hd hx,
    fun _ hf _ _ hd _ hg _ hx => commutator_trivial_gu hK hp2 hq hn ψ hker hnorm htoral hf hd hg
      hx⟩

theorem strongConclusion_su_gf {e : ℕ} (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) (hn : 3 ≤ n) {X : Type}
    [Group X] [Finite X] (ψ : Su (GaloisField p (2 * e)) p e n →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su (GaloisField p (2 * e)) p e n)) (hnorm : ψ.range.Normal)
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f' ∈ F, f' * f' = 1)
    (htoral : ToralDiagGU 2 ψ F) : StrongConclusion ψ.range F :=
  strongConclusion_gu
    (CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq h5) hp2 h5 hn ψ
    hker hnorm hcard hF2 htoral

end CFSG.ClassicalInvolution.Asc77
