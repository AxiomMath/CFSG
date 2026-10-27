module

public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleFixed
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleMinus

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (SemiSim IsConj IsHypFam)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet orth_or_twin)
open scoped Matrix MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame


section Fixes

theorem fixes_of_gen3_of_ker {G Y : Type*} [Group G] [Group Y] (π : G →* Y)
    (hker : π.ker ≤ Subgroup.center G) (hk3 : ∀ x ∈ π.ker, x ^ 3 = 1 → x = 1)
    {R : Subgroup G} (hR : ModelFacts.Gen3 R) (α : G ≃* G)
    (h : ∀ r ∈ R, r⁻¹ * α r ∈ π.ker) : ∀ r ∈ R, α r = r := by
  obtain ⟨S, hSR, hS3, hRS⟩ := hR
  have hS : ∀ s ∈ S, α s = s := by
    intro s hs
    have hc : s⁻¹ * α s ∈ π.ker := h s (hSR hs)
    have hcen : s⁻¹ * α s ∈ Subgroup.center G := hker hc
    have hcomm : Commute s (s⁻¹ * α s) := Subgroup.mem_center_iff.mp hcen s
    have e : α s = s * (s⁻¹ * α s) := by group
    have h3 : (s⁻¹ * α s) ^ 3 = 1 := by
      have h1 : α s ^ 3 = 1 := by rw [← map_pow, hS3 s hs, map_one]
      rw [e, hcomm.mul_pow, hS3 s hs, one_mul] at h1
      exact h1
    have h1 := hk3 _ hc h3
    rw [e, h1, mul_one]
  have hle : Subgroup.closure S ≤ MonoidHom.eqLocus (α : G →* G) (MonoidHom.id G) :=
    (Subgroup.closure_le _).mpr fun s hs => hS s hs
  intro r hr
  exact hle (hRS hr)

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem fixes_twin_of_isConj3 (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 5 ≤ Module.finrank F V)
    {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q} (hα : IsConj α g) (hα2 : ∀ y, α (α y) = y)
    (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q))
    (hk3 : ∀ x ∈ (spinAction Q).ker, x ^ 3 = 1 → x = 1) (fr : OFrame Q)
    {R R' : Subgroup (spinGroup Q)} (hR' : ModelFacts.Gen3 R')
    (hR : R.map (spinAction Q) = fr.La.range) (hRs : R'.map (spinAction Q) = fr.swap.La.range)
    (hfix : ∀ r ∈ R, α r = r)
    (hno : ∀ g' : V →ₗ[F] V, Function.Injective g' →
      (∀ x y, polar Q (g' x) y = -polar Q x (g' y)) →
      (∃ c : F, c ≠ 0 ∧ ∀ x, g' (g' x) = c • x) → False) :
    ∀ r ∈ R', α r = r := by
  have hcommR : ∀ (A : SL(2, F)) z, g (fr.La A z) = fr.La A (g z) := by
    intro A z
    have hmem : fr.La A ∈ R.map (spinAction Q) := by rw [hR]; exact ⟨A, rfl⟩
    obtain ⟨r, hr, hrA⟩ := hmem
    have h1 := hα r z
    rw [hfix r hr] at h1
    rw [← hrA]
    exact h1.symm
  have hphi : ∀ c : F, g.φ c = c := by
    refine semiSim_phi_eq_id g fr (fun c z => ?_)
    have := hcommR (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) z
    rwa [fr.La_transvection_zero_one c] at this
  let gl : V →ₗ[F] V := g.toLinear hphi
  have hgl : ∀ x, gl x = g x := fun x => rfl
  have hginj : Function.Injective gl := g.bijective.1
  have hμ : ∀ x, Q (gl x) = (g.μ : F) * Q x := fun x => by rw [hgl, g.map_Q, hphi]
  have hG : ∀ ω ∈ elementaryGroup Q, ∀ z, gl (gl (ω z)) = ω (gl (gl z)) := by
    intro ω hω z
    obtain ⟨y, rfl⟩ := elementaryGroup_le_range_spinAction hQ hdim hω
    exact hα.comm_sq hα2 y z
  have hS := commutes_swap_of_commutes_La gl hginj hμ hG fr hcommR hno
  have hact : ∀ r ∈ R', spinAction Q (α r) = spinAction Q r := by
    intro r' hr'
    have hmem : spinAction Q r' ∈ fr.swap.La.range := by rw [← hRs]; exact ⟨r', hr', rfl⟩
    obtain ⟨B, hB⟩ := hmem
    refine LinearEquiv.ext fun w => ?_
    obtain ⟨z, rfl⟩ := g.bijective.2 w
    calc spinAction Q (α r') (g z) = g (spinAction Q r' z) := hα r' z
      _ = g (fr.swap.La B z) := by rw [← hB]
      _ = fr.swap.La B (g z) := hS B z
      _ = spinAction Q r' (g z) := by rw [hB]
  exact fixes_of_gen3_of_ker (spinAction Q) hker hk3 hR' α fun r hr => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hact r hr, inv_mul_cancel]

end Fixes

section Minus

variable {F : Type} [Field F] [Finite F]

theorem quadMinus_four_same_involution3 (hodd : Odd (Nat.card F)) {b c₀ : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c₀ ≠ 0) (h4 : 2 ≤ Nat.card F)
    {R₀ R₁ : Subgroup (_ ≃ₗ[F] _)} {i₀ i₁ : _ ≃ₗ[F] _}
    (h₀ : IsFundamental (quadMinus 4 F b c₀) R₀ i₀)
    (h₁ : IsFundamental (quadMinus 4 F b c₀) R₁ i₁) (hc : Commutes R₀ R₁) : i₁ = i₀ := by
  rcases orth_or_twin hodd h₀ h₁ hc with horth | heq
  swap
  · exact heq
  exfalso
  obtain ⟨F₀, rfl, rfl⟩ := h₀
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  exact ModelFacts.TG3.false_of_orth_quadMinus_four3 (IsFundamental.two_ne_zero_of_odd hodd)
    hirr h4 F₀ F₁ (span_le_perp_of_negSpace hodd horth)

theorem false_of_skewRoot_quadMinus_four3 (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F))
    {b c₀ : F} (hirr : ∀ s : F, s ^ 2 + b * s + c₀ ≠ 0) (h4 : 2 ≤ Nat.card F)
    {g : (Fin (3 + 1 - 1) ⊕ Fin (3 + 1 - 1) ⊕ Fin 2 → F) →ₗ[F]
      (Fin (3 + 1 - 1) ⊕ Fin (3 + 1 - 1) ⊕ Fin 2 → F)} {c : F}
    (hg : SkewRoot (quadMinus (3 + 1) F b c₀) g c) : False := by
  classical
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite (n := 3 + 1) (K := F) hirr
  have hdim : Module.finrank F (Fin (3 + 1 - 1) ⊕ Fin (3 + 1 - 1) ⊕ Fin 2 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨G₁, -, hG₁g⟩ := exists_gstable_frame h2 hodd hQ hg (C := ⊤) (polarNondegOn_top hQ)
    (by rw [finrank_top]; omega) (fun _ _ => Submodule.mem_top)
  have hC1 := CFSG.ClassicalInvolution.ModelFacts.polarNondegOn_perp hQ G₁
  have hd1 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four G₁
  have hC1g : ∀ y ∈ G₁.perp, g y ∈ G₁.perp := by
    intro y hy
    rw [Frame.mem_perp_iff_forall_incl] at hy ⊢
    intro X
    obtain ⟨X', hX'⟩ := hG₁g _ ⟨X, rfl⟩
    rw [hg.skew, ← hX', hy X', neg_zero]
  obtain ⟨G₂, hG₂C, -⟩ := exists_gstable_frame h2 hodd hQ hg hC1 (by omega) hC1g
  obtain ⟨o01, o02, o03, o04⟩ := orth_pairs_of_span_le_perp hG₂C
  let P : Fin 4 → HypPair (quadMinus (3 + 1) F b c₀) := ![G₁.P, G₁.P', G₂.P, G₂.P']
  have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [P] <;>
      first
      | exact absurd rfl hij
      | exact G₁.orth | exact G₁.orth.symm | exact G₂.orth | exact G₂.orth.symm
      | exact o01 | exact o01.symm | exact o02 | exact o02.symm
      | exact o03 | exact o03.symm | exact o04 | exact o04.symm
  exact false_of_isHypFam_quadMinus3 (m := 3) h2 hirr h4 _ (isHypFam_of_pairs P hP)

end Minus

end CFSG.ClassicalInvolution.Q3.Q3W.EX
