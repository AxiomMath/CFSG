module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCoreX
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinear

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.ClassicalInvolution.RouteD.Gaps (LinearAutClassification diagGL coe_diagGL)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {n : ℕ} {k : Type} [Field k] [Finite k] {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem act_diagonal_of_fix_blocks (hn : 3 ≤ n) (h4 : 4 ≤ Nat.card k)
    (hcl : LinearAutClassification k n) (Ψ : SL(n, k) →* X)
    (hker : Ψ.ker ≤ Subgroup.center SL(n, k)) (hnorm : Ψ.range.Normal) (σ : Fin n → Bool)
    {d : X} (hodd : Odd (orderOf d))
    (hdc : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSL k (coordSet σ b),
      d * Ψ s = Ψ s * d) :
    ∃ u : Fin n → kˣ, (∀ i j, σ i = σ j → u i = u j) ∧
      ∀ y, d * Ψ y * d⁻¹ = Ψ (slConjugation n k (diagGL u) y) := by
  have hdc₂ : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSL k (coordSet σ b),
      (d * d) * Ψ s = Ψ s * (d * d) := by
    intro b hb s hs
    rw [mul_assoc, hdc b hb s hs, ← mul_assoc, hdc b hb s hs, mul_assoc]
  have := hnorm
  have hkerR : Ψ.rangeRestrict.ker ≤ Subgroup.center SL(n, k) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨α, g, φ, ε, hαΨ, hαf⟩ := hcl ↥Ψ.range Ψ.rangeRestrict Ψ.rangeRestrict_surjective hkerR
    (MulAut.conjNormal d)
  have hαd : ∀ x, Ψ (α x) = d * Ψ x * d⁻¹ := by
    intro x
    have h := congrArg Subtype.val (hαΨ x)
    simpa [MulAut.conjNormal_apply] using h
  obtain ⟨g₂, hg₂⟩ := exists_sq_form α g φ ε hαf
  have hα₂d : ∀ x, Ψ (α (α x)) = (d * d) * Ψ x * (d * d)⁻¹ := by
    intro x
    rw [hαd, hαd]
    group
  have hfix : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSL k (coordSet σ b),
      (α.comp α) s = s := by
    intro b hb s hs
    have hperf : Group.IsPerfect ↥(coordBlockSL k (coordSet σ b)) :=
      ⟨(isQuasisimple_coordBlockSL hb h4).1⟩
    have hhom := CFSG.ClassicalInvolution.RouteD.Gaps.hom_eq_of_central_ker Ψ hker
      (L := ↥(coordBlockSL k (coordSet σ b)))
      ((α.comp α).comp (coordBlockSL k (coordSet σ b)).subtype)
      (coordBlockSL k (coordSet σ b)).subtype (fun l => by
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
        rw [hα₂d, hdc₂ b hb l l.2, mul_inv_cancel_right])
    exact congrArg (fun h => (h ⟨s, hs⟩ : SL(n, k))) hhom
  obtain ⟨hφ, u₂, hg₂u, hconst⟩ := diag_of_fixes_blocks hn σ (α.comp α) g₂ (φ.trans φ)
    (fun x => hg₂ x) hfix
  have hd₂act : ∀ y, (d * d) * Ψ y * (d * d)⁻¹ = Ψ (slConjugation n k (diagGL u₂) y) := by
    intro y
    rw [← hα₂d]
    congr 1
    refine Subtype.ext ?_
    rw [slConjugation_matrix]
    have hmap : (φ.trans φ).mapMatrix (y : Matrix (Fin n) (Fin n) k) = y := by
      ext i j
      exact hφ _
    have := hg₂ y
    rw [hmap, hg₂u] at this
    exact this
  obtain ⟨r, hr⟩ := hodd
  have hdpow : d = (d * d) ^ (r + 1) := by
    have h1 : (d * d) ^ (r + 1) = d ^ (2 * (r + 1)) := by rw [pow_mul, sq]
    rw [h1, show 2 * (r + 1) = orderOf d + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have hpowact : ∀ j : ℕ, ∀ y, (d * d) ^ j * Ψ y * ((d * d) ^ j)⁻¹ =
      Ψ (slConjugation n k (diagGL (u₂ ^ j)) y) := by
    intro j
    induction j with
    | zero =>
      intro y
      rw [pow_zero, pow_zero, slConjugation_diagGL_one]
      group
    | succ j ih =>
      intro y
      have e1 : ∀ (e z : X), e ^ (j + 1) * z * (e ^ (j + 1))⁻¹ =
          e ^ j * (e * z * e⁻¹) * (e ^ j)⁻¹ := by
        intro e z
        rw [pow_succ, _root_.mul_inv_rev]
        simp only [mul_assoc]
      rw [e1 (d * d) (Ψ y), hd₂act, ih, slConjugation_diagGL_mul, pow_succ', mul_comm]
  refine ⟨u₂ ^ (r + 1), fun i j hij => ?_, fun y => ?_⟩
  · simp only [Pi.pow_apply, hconst i j hij]
  · conv_lhs => rw [hdpow]
    exact hpowact (r + 1) y

theorem commute_of_split (hn : 3 ≤ n) (h2 : (2 : k) ≠ 0) (h4 : 4 ≤ Nat.card k)
    (hcl : LinearAutClassification k n) (Ψ : SL(n, k) →* X)
    (hker : Ψ.ker ≤ Subgroup.center SL(n, k)) (hnorm : Ψ.range.Normal)
    (hfaith : ∀ x : X, (∀ y, x * Ψ y * x⁻¹ = Ψ y) → x = 1) (f : X) (σ : Fin n → Bool)
    (hf : ∀ y, f * Ψ y * f⁻¹ = Ψ (slConjugation n k (signGL k σ) y)) {R : Subgroup X}
    (hRodd : Odd (Nat.card R)) (hRi : ∀ r ∈ R, r * f = f * r)
    (hRconj : ∀ s ∈ Ψ.range ⊓ centralizer ({f} : Set X), Odd (orderOf s) → ∀ r ∈ R,
      s * r * s⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  have := hnorm
  have hact : ∀ r ∈ R, ∃ u : Fin n → kˣ, ∀ y,
      r * Ψ y * r⁻¹ = Ψ (slConjugation n k (diagGL u) y) := by
    intro r hr
    have hodd : Odd (orderOf r) := by
      have h := orderOf_dvd_natCard (⟨r, hr⟩ : R)
      rw [Subgroup.orderOf_mk] at h
      exact Odd.of_dvd_nat hRodd h
    have hdc : ∀ b, 2 ≤ (coordSet σ b).card → ∀ s ∈ coordBlockSL k (coordSet σ b),
        r * Ψ s = Ψ s * r := by
      intro b hb s hs
      exact commute_of_isComponentOf (L := Ψ.range) hRodd hRi hRconj
        (isComponentOf_block_centralizer h2 h4 Ψ hker f σ hf b hb) hr ⟨s, hs, rfl⟩
    obtain ⟨u, -, hu⟩ := act_diagonal_of_fix_blocks hn h4 hcl Ψ hker hnorm σ hodd hdc
    exact ⟨u, hu⟩
  intro r₁ h₁ r₂ h₂
  obtain ⟨u₁, hu₁⟩ := hact r₁ h₁
  obtain ⟨u₂, hu₂⟩ := hact r₂ h₂
  have hx : ∀ y, ((r₂ * r₁)⁻¹ * (r₁ * r₂)) * Ψ y * ((r₂ * r₁)⁻¹ * (r₁ * r₂))⁻¹ = Ψ y := by
    intro y
    have e1 : (r₁ * r₂) * Ψ y * (r₁ * r₂)⁻¹ =
        Ψ (slConjugation n k (diagGL u₁) (slConjugation n k (diagGL u₂) y)) := by
      rw [← hu₁, ← hu₂]
      group
    have e2 : (r₂ * r₁) * Ψ y * (r₂ * r₁)⁻¹ =
        Ψ (slConjugation n k (diagGL u₂) (slConjugation n k (diagGL u₁) y)) := by
      rw [← hu₂, ← hu₁]
      group
    rw [slConjugation_diagGL_comm] at e1
    calc ((r₂ * r₁)⁻¹ * (r₁ * r₂)) * Ψ y * ((r₂ * r₁)⁻¹ * (r₁ * r₂))⁻¹ =
        (r₂ * r₁)⁻¹ * ((r₁ * r₂) * Ψ y * (r₁ * r₂)⁻¹) * (r₂ * r₁) := by group
      _ = (r₂ * r₁)⁻¹ * ((r₂ * r₁) * Ψ y * (r₂ * r₁)⁻¹) * (r₂ * r₁) := by rw [e1, e2]
      _ = Ψ y := by group
  have h1 := hfaith _ hx
  rw [inv_mul_eq_one] at h1
  exact h1.symm

end CFSG.ComponentClassification.Foote5.OddLieCore
