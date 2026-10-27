module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinSpin
import CFSG.ClassicalInvolution.Asc77.AscE186CentA
import CFSG.ClassicalInvolution.Asc77.AscIH8Red

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic QuadraticMap
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

section Swap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem swap_of_twin_pair_ord [Finite F] (hodd : Odd (Nat.card F))
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x') :
    ∃ F₁ : Frame Q, R.map (spinAction Q) = F₁.La.range ∧
      R'.map (spinAction Q) = F₁.swap.La.range ∧ spinAction Q x = F₁.La (-1) ∧
        spinAction Q x' = F₁.swap.La (-1) := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set θ := spinAction Q with hθ
  obtain ⟨i₁, F₁, hF₁, -⟩ := hR
  obtain ⟨i₂, F₂, hF₂, -⟩ := hR'
  have hθx : θ x = F₁.La (-1) := by
    have hmem : θ x ∈ F₁.La.range := hF₁ ▸ Subgroup.mem_map_of_mem _ hx
    have hsq : θ x * θ x = 1 := by rw [← map_mul, hx2, map_one]
    have hne1 : θ x ≠ 1 := fun h => hx1 (hinj x hx h)
    have hord2 : orderOf (θ x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₁).eq_of_orderOf_eq_two hodd hmem hord2
  have hθx' : θ x' = F₂.La (-1) := by
    have hmem : θ x' ∈ F₂.La.range := hF₂ ▸ Subgroup.mem_map_of_mem _ hx'
    have hsq : θ x' * θ x' = 1 := by rw [← map_mul, hx'2, map_one]
    have hne1 : θ x' ≠ 1 := fun h => hx'1 (hinj' x' hx' h)
    have hord2 : orderOf (θ x') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₂).eq_of_orderOf_eq_two hodd hmem hord2
  have hFeq : F₂.La (-1) = F₁.La (-1) := by rw [← hθx, ← hθx', hord]
  rcases Frame.La_range_eq_or_eq_swap h2 hFeq with h | h
  · exfalso
    apply hne
    apply ih8_eq_of_map_eq θ (ker_spinAction_le_center Q) hRp hR'p
    rw [hF₁, hF₂, h]
  · refine ⟨F₁, hF₁, hF₂.trans h, hθx, ?_⟩
    have hmem : θ x' ∈ F₁.swap.La.range := by
      rw [← h, ← hF₂]
      exact Subgroup.mem_map_of_mem _ hx'
    have hsq : θ x' * θ x' = 1 := by rw [← map_mul, hx'2, map_one]
    have hne1 : θ x' ≠ 1 := fun h => hx'1 (hinj' x' hx' h)
    have hord2 : orderOf (θ x') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₁.swap).eq_of_orderOf_eq_two hodd hmem hord2

end Swap

section Alpha

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite F]
  {Q : QuadraticForm F V}

theorem alphaOf_spin_twin_pair_ord (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') (hcomm : Commutes R R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x') {H : Type} [Group H] [Finite H]
    (ψ : spinGroup Q →* H) (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) (hxx' : ψ x = ψ x')
    {u : H} (hu : u ∈ R.map ψ ⊔ R'.map ψ)
    (hun : u ∈ Subgroup.normalizer (ψ.range : Set H)) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ ψ x) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨u, hun⟩,
      toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ := swap_of_twin_pair_ord hodd hRp hR'p hR hR'
    hinj hinj' hne hx hx2 hx1 hx' hx'2 hx'1 hord
  have hcommψ : Commutes (R.map ψ) (R'.map ψ) := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    rw [← map_mul, ← map_mul, hcomm r hr r' hr']
  obtain ⟨a, ha, b, hb, hab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcommψ hu
  obtain ⟨r, hr, rfl⟩ := ha
  obtain ⟨r', hr', rfl⟩ := hb
  have hθr : spinAction Q r ∈ F₁.La.range := hF₁ ▸ Subgroup.mem_map_of_mem _ hr
  have hθr' : spinAction Q r' ∈ F₁.swap.La.range := hF₁' ▸ Subgroup.mem_map_of_mem _ hr'
  obtain ⟨A, hA⟩ := hθr
  obtain ⟨A', hA'⟩ := hθr'
  have hker2 : (r * r') * (r * r') ∈ Subgroup.center (spinGroup Q) := by
    apply hψ
    rw [MonoidHom.mem_ker]
    simp only [map_mul]
    calc ψ r * ψ r' * (ψ r * ψ r') = u * u := by rw [hab]
      _ = 1 := hu2
  obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hker2
  have hθrr' : spinAction Q (r * r') = twinInv F₁ A A' := by
    rw [map_mul, ← hA, ← hA']
    rfl
  have hsq : ∀ v, twinInv F₁ A A' (twinInv F₁ A A' v) = μ • v := by
    intro v
    have := hμ v
    rwa [map_mul, hθrr'] at this
  have hperp : F₁.perp ≠ ⊥ := by
    intro h
    have h1 := finrank_perp_add_four F₁
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨ε, hε, hAA, hA'A'⟩ := sq_eq_of_twinInv_sq_scalar F₁ hperp hsq
  have hmk : (⟨ψ (r * r'), mem_normalizer_range ψ (r * r')⟩ : ↥(Subgroup.normalizer
      (ψ.range : Set H))) = ⟨u, hun⟩ := Subtype.ext (show ψ (r * r') = u by rw [map_mul, hab])
  rcases hε with rfl | rfl
  ·
    exfalso
    rw [one_smul] at hAA hA'A'
    have hrcases : r = 1 ∨ r = x := by
      rcases eq_one_or_neg_one_of_sq h2 A.2 hAA with h | h
      · left
        have hA1 : A = 1 := Subtype.ext h
        apply hinj r hr
        rw [← hA, hA1, map_one]
      · right
        have hA1 : A = -1 := Subtype.ext (by rw [h]; simp)
        have h1 : spinAction Q r = spinAction Q x := by rw [← hA, hA1, hθx]
        have h2' : r * x⁻¹ = 1 := hinj _ (R.mul_mem hr (R.inv_mem hx)) (by
          rw [map_mul, map_inv, h1, mul_inv_cancel])
        exact mul_inv_eq_one.mp h2'
    have hr'cases : r' = 1 ∨ r' = x' := by
      rcases eq_one_or_neg_one_of_sq h2 A'.2 hA'A' with h | h
      · left
        have hA1 : A' = 1 := Subtype.ext h
        apply hinj' r' hr'
        rw [← hA', hA1, map_one]
      · right
        have hA1 : A' = -1 := Subtype.ext (by rw [h]; simp)
        have h1 : spinAction Q r' = spinAction Q x' := by rw [← hA', hA1, hθx']
        have h2' : r' * x'⁻¹ = 1 := hinj' _ (R'.mul_mem hr' (R'.inv_mem hx')) (by
          rw [map_mul, map_inv, h1, mul_inv_cancel])
        exact mul_inv_eq_one.mp h2'
    have hxsq : ψ x * ψ x = 1 := by rw [← map_mul, hx2, map_one]
    rcases hrcases with h1 | h1 <;> rcases hr'cases with h3 | h3 <;> rw [h1, h3] at hab
    · exact hu1 (by rw [← hab, map_one, one_mul])
    · exact huz (by rw [← hab, map_one, one_mul, hxx'])
    · exact huz (by rw [← hab, map_one, mul_one])
    · exact hu1 (by rw [← hab, ← hxx', hxsq])
  ·
    rw [neg_one_smul] at hAA hA'A'
    have key := alphaOf_spin_frame_eq_bot hodd h5 hQ hrange F₁ hAA hA'A' hV
      (s₁ := r * r') (s₂ := x) hθrr' hθx ψ hψ
    rw [hmk] at key
    exact key

end Alpha

end CFSG.ClassicalInvolution.G2D4Models.Twin
