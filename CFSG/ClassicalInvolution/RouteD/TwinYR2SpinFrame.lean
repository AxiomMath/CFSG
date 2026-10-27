module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinStmt
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Extract

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem sq_eq_one_of_central_le_la (fr : OFrame Q) {g : V ≃ₗ[F] V} (hg : g ∈ fr.La.range)
    (hc : ∀ h ∈ fr.La.range, g * h = h * g) : g * g = 1 := by
  obtain ⟨A, rfl⟩ := hg
  have hA : A ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    have h := hc (fr.La B) ⟨B, rfl⟩
    rw [← map_mul, ← map_mul] at h
    exact (fr.La_injective h).symm
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have h1 : A * A = 1 := by
    apply Subtype.ext
    simp only [Fintype.card_fin] at hr
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hrA, ← map_mul, ← pow_two, hr, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  rw [← map_mul, h1, map_one]

theorem sq_eq_neg_one_of_sq_mem_center (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ : CenterScalar Q) [Finite F] (fr : OFrame Q) (hperp : fr.perp ≠ ⊥) {a x : spinGroup Q}
    {A : SL(2, F)} (hA : fr.La A = spinAction Q a) (hx : spinAction Q x = fr.La (-1))
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup Q)) : A * A = -1 := by
  obtain ⟨w, hwperp, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hsq
  have hinv : (fr.La (-1))⁻¹ = fr.La (-1) := inv_eq_of_mul_eq_one_right fr.La_neg_one_mul_self
  have hw1 : fr.La (-1) w = w := La_neg_one_of_mem_perp fr hwperp
  have hw2 : fr.La A w = w :=
    Frame.La_apply_of_coords_eq_zero fr A ((Frame.mem_perp_iff fr).mp hwperp)
  have e1 : spinAction Q (a * a * x⁻¹) w = w := by
    rw [map_mul, map_mul, map_inv, ← hA, hx, hinv]
    simp only [LinearEquiv.mul_apply]
    rw [hw1, hw2, hw2]
  have hμ1 : μ = 1 := by
    have h2 : (μ - 1) • w = 0 := by rw [sub_smul, ← hμ w, e1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw0)
  have h1 : spinAction Q (a * a * x⁻¹) = 1 := LinearEquiv.ext fun v => by
    rw [hμ v, hμ1, one_smul]
    rfl
  have h3 : fr.La (A * A) = fr.La (-1) := by
    rw [map_mul, hA, ← map_mul, ← hx]
    have := h1
    rw [map_mul, map_mul, map_inv, mul_inv_eq_one] at this
    rw [map_mul]
    exact this
  exact fr.La_injective h3

theorem exists_pair_frame [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 1 ≤ Module.finrank F V)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hnc : ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    (hnc' : ∀ r ∈ R', r ∈ Subgroup.center (spinGroup Q) → r = 1) (hne : R ≠ R')
    {x x' : spinGroup Q} (hx : x ∈ R) (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ∃ F₁ : OFrame Q, R.map (spinAction Q) = F₁.La.range ∧
      R'.map (spinAction Q) = F₁.swap.La.range ∧ spinAction Q x = F₁.La (-1) ∧
      spinAction Q x' = F₁.swap.La (-1) := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center hker fun r hr hcen =>
      hnc r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center hker fun r hr hcen =>
      hnc' r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hsqx : ∀ {R₀ : Subgroup (spinGroup Q)} {y : spinGroup Q}, R₀.map (spinAction Q) ∈ fundSet Q →
      (∀ r ∈ R₀, spinAction Q r = 1 → r = 1) → y ∈ R₀ → (∀ r ∈ R₀, y * r = r * y) → y * y = 1 := by
    intro R₀ y hR₀ hinj₀ hy hcy
    obtain ⟨i, FR, hFR, -⟩ := hR₀
    have hθy : spinAction Q y ∈ FR.La.range := hFR ▸ Subgroup.mem_map_of_mem _ hy
    have hθyc : ∀ h ∈ FR.La.range, spinAction Q y * h = h * spinAction Q y := by
      intro h hh
      rw [← hFR] at hh
      obtain ⟨r, hr, rfl⟩ := hh
      rw [← map_mul, ← map_mul, hcy r hr]
    have h1 := sq_eq_one_of_central_le_la FR hθy hθyc
    apply hinj₀ (y * y) (R₀.mul_mem hy hy)
    rw [map_mul]
    exact h1
  have hx2 : x * x = 1 := hsqx hR hinj hx hcx
  have hx'2 : x' * x' = 1 := hsqx hR' hinj' hx' hcx'
  have hψ : (QuotientGroup.mk' (Subgroup.center (spinGroup Q))).ker ≤
      Subgroup.center (spinGroup Q) := by
    rw [QuotientGroup.ker_mk']
  have hxx' : QuotientGroup.mk' (Subgroup.center (spinGroup Q)) x =
      QuotientGroup.mk' (Subgroup.center (spinGroup Q)) x' := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv] using hsame
  exact swap_of_twin_pair hodd hrange hZ hproj hRp hR'p hR hR' hinj hinj' hne hx hx2 hx1 hx' hx'2
    hx'1 (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) hψ hxx'

theorem exists_twin_frame [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hnc : ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    (hnc' : ∀ r ∈ R', r ∈ Subgroup.center (spinGroup Q) → r = 1) (hne : R ≠ R')
    {x x' a a' : spinGroup Q} (hx : x ∈ R) (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup Q))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup Q)) :
    ∃ (F₁ : OFrame Q) (A A' : SL(2, F)), R.map (spinAction Q) = F₁.La.range ∧
      R'.map (spinAction Q) = F₁.swap.La.range ∧ spinAction Q x = F₁.La (-1) ∧
      spinAction Q x' = F₁.swap.La (-1) ∧ spinAction Q a = F₁.La A ∧
      spinAction Q a' = F₁.swap.La A' ∧ (A : Matrix (Fin 2) (Fin 2) F) * A = -1 ∧
      (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1 := by
  classical
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ := exists_pair_frame hodd hrange hZ (by omega) hproj hRp hR'p
    hR hR' hnc hnc' hne hx hcx hx1 hx' hcx' hx'1 hsame
  obtain ⟨A, hA⟩ : ∃ A : SL(2, F), F₁.La A = spinAction Q a := by
    have : spinAction Q a ∈ F₁.La.range := hF₁ ▸ Subgroup.mem_map_of_mem _ ha
    exact this
  obtain ⟨A', hA'⟩ : ∃ A' : SL(2, F), F₁.swap.La A' = spinAction Q a' := by
    have : spinAction Q a' ∈ F₁.swap.La.range := hF₁' ▸ Subgroup.mem_map_of_mem _ ha'
    exact this
  have hperp : ∀ fr : OFrame Q, fr.perp ≠ ⊥ := by
    intro fr h
    have h1 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    rw [h, finrank_bot] at h1
    omega
  have hAA := sq_eq_neg_one_of_sq_mem_center hrange hZ F₁ (hperp F₁) hA hθx hsq
  have hA'A' := sq_eq_neg_one_of_sq_mem_center hrange hZ F₁.swap (hperp F₁.swap) hA' hθx' hsq'
  refine ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hA.symm, hA'.symm, ?_, ?_⟩
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hAA
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this
  · have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hA'A'
    simpa [Matrix.SpecialLinearGroup.coe_mul] using this

end Extract

end CFSG.ClassicalInvolution.RouteD.TwinY
