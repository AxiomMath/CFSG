module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinMat
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Aut
import CFSG.ClassicalInvolution.Asc77.AscE186CentA
import CFSG.ClassicalInvolution.Asc77.AscIH8Red

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

section Center

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem exists_smul_of_central (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ : CenterScalar Q) {s : spinGroup Q} (hs : s ∈ Subgroup.center (spinGroup Q)) :
    ∃ μ : F, ∀ v, spinAction Q s v = μ • v := by
  have hmem : spinAction Q s ∈ elementaryGroup Q := by
    rw [← hrange]
    exact ⟨s, rfl⟩
  have hcenter : (⟨spinAction Q s, hmem⟩ : ↥(elementaryGroup Q)) ∈
      Subgroup.center ↥(elementaryGroup Q) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : (y : V ≃ₗ[F] V) ∈ (spinAction Q).range := by
      rw [hrange]
      exact y.2
    obtain ⟨s', hs'⟩ := hy
    apply Subtype.ext
    show (y : V ≃ₗ[F] V) * spinAction Q s = spinAction Q s * (y : V ≃ₗ[F] V)
    rw [← hs', ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs s']
  obtain ⟨μ, hμ⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp (hZ hcenter))
  exact ⟨μ, fun v => hμ v⟩

end Center

section Swap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem swap_of_twin_pair [Finite F] (hodd : Odd (Nat.card F))
    (hrange : (spinAction Q).range = elementaryGroup Q) (hZ : CenterScalar Q) [Nontrivial V]
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) {H : Type} [Group H]
    (ψ : spinGroup Q →* H) (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) (hxx' : ψ x = ψ x') :
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
    have hord : orderOf (θ x) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₁).eq_of_orderOf_eq_two hodd hmem hord
  have hθx' : θ x' = F₂.La (-1) := by
    have hmem : θ x' ∈ F₂.La.range := hF₂ ▸ Subgroup.mem_map_of_mem _ hx'
    have hsq : θ x' * θ x' = 1 := by rw [← map_mul, hx'2, map_one]
    have hne1 : θ x' ≠ 1 := fun h => hx'1 (hinj' x' hx' h)
    have hord : orderOf (θ x') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₂).eq_of_orderOf_eq_two hodd hmem hord
  have hc : x' * x⁻¹ ∈ Subgroup.center (spinGroup Q) :=
    hψ (by rw [MonoidHom.mem_ker, map_mul, map_inv, ← hxx', mul_inv_cancel])
  obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hc
  have hF₁sq : F₁.La (-1) * F₁.La (-1) = 1 := F₁.La_neg_one_mul_self
  have hF₂sq : F₂.La (-1) * F₂.La (-1) = 1 := F₂.La_neg_one_mul_self
  have hF₁w : ∀ w, F₁.La (-1) (F₁.La (-1) w) = w := fun w => by
    have := congrArg (fun g : V ≃ₗ[F] V => g w) hF₁sq
    simpa using this
  have hrel : ∀ w, F₂.La (-1) w = μ • F₁.La (-1) w := by
    intro w
    have h1 := hμ (F₁.La (-1) w)
    rw [map_mul, map_inv, hθx', hθx] at h1
    have hinv : (F₁.La (-1))⁻¹ = F₁.La (-1) := inv_eq_of_mul_eq_one_right hF₁sq
    rw [hinv] at h1
    simpa only [LinearEquiv.mul_apply, hF₁w] using h1
  have hμ2 : μ * μ = 1 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have h1 : F₂.La (-1) (F₂.La (-1) w) = w := by
      have := congrArg (fun g : V ≃ₗ[F] V => g w) hF₂sq
      simpa using this
    rw [hrel w, map_smul, hrel (F₁.La (-1) w), smul_smul, hF₁w] at h1
    have h4 : (μ * μ - 1) • w = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hw)
  have hμ1 : μ = 1 := by
    rcases mul_self_eq_one_iff.mp hμ2 with h | h
    · exact h
    · exfalso
      refine hproj F₁ F₂ (LinearEquiv.ext fun w => ?_)
      rw [hrel, h, LinearEquiv.mul_apply, LinearEquiv.neg_apply, neg_one_smul]
  have hFeq : F₂.La (-1) = F₁.La (-1) := LinearEquiv.ext fun w => by rw [hrel, hμ1, one_smul]
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
    have hord : orderOf (θ x') = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne1
    exact (IsFundamental.of_frame F₁.swap).eq_of_orderOf_eq_two hodd hmem hord

end Swap

section Alpha

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite F]
  {Q : QuadraticForm F V}

theorem alphaOf_spin_twin_pair (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V)
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') (hcomm : Commutes R R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) {H : Type} [Group H]
    [Finite H] (ψ : spinGroup Q →* H) (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hxx' : ψ x = ψ x') {u : H} (hu : u ∈ R.map ψ ⊔ R'.map ψ)
    (hun : u ∈ Subgroup.normalizer (ψ.range : Set H)) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ ψ x) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨u, hun⟩,
      toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  classical
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ := swap_of_twin_pair hodd hrange hZ hproj hRp hR'p hR hR'
    hinj hinj' hne hx hx2 hx1 hx' hx'2 hx'1 ψ hψ hxx'
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

section Induced

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {H : Type} [Group H]

@[expose] def spinInd (ψ : spinGroup Q →* H) : spinGroup Q →* ↥(inducedAutOn ψ.range) :=
  (toInducedAutOn ψ.range).comp (ψ.codRestrict _ (fun s => mem_normalizer_range ψ s))

theorem spinInd_apply (ψ : spinGroup Q →* H) (s : spinGroup Q) :
    spinInd ψ s = toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ := rfl

theorem spinInd_eq_one_of_central (ψ : spinGroup Q →* H) {κ : spinGroup Q}
    (hκ : κ ∈ Subgroup.center (spinGroup Q)) : spinInd ψ κ = 1 := by
  apply Subtype.ext
  apply MulEquiv.ext
  intro ℓ
  obtain ⟨s, rfl⟩ := ψ.rangeRestrict_surjective ℓ
  apply Subtype.ext
  show ψ κ * ψ s * (ψ κ)⁻¹ = ψ s
  rw [← map_mul, ← map_inv, ← map_mul, ← (Subgroup.mem_center_iff.mp hκ s)]
  simp

theorem commute_spinInd_of_mem_map_sup (hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q))
    (ψ : spinGroup Q →* H) {R R' : Subgroup (spinGroup Q)} (v : ↥(inducedAutOn ψ.range))
    (hR : ∀ r ∈ R, v * spinInd ψ r = spinInd ψ r * v)
    (hR' : ∀ r ∈ R', v * spinInd ψ r = spinInd ψ r * v) {s : spinGroup Q}
    (hs : spinAction Q s ∈ R.map (spinAction Q) ⊔ R'.map (spinAction Q)) :
    v * spinInd ψ s = spinInd ψ s * v := by
  rw [← Subgroup.map_sup] at hs
  obtain ⟨w, hw, hws⟩ := hs
  have hle : R ⊔ R' ≤ (Subgroup.centralizer ({v} : Set ↥(inducedAutOn ψ.range))).comap
      (spinInd ψ) := by
    refine sup_le (fun r hr => ?_) (fun r hr => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hR r hr).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hR' r hr).symm
  have hwc := Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hκ : w⁻¹ * s ∈ Subgroup.center (spinGroup Q) := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hws, inv_mul_cancel])
  have h1 : spinInd ψ s = spinInd ψ w := by
    have : s = w * (w⁻¹ * s) := by group
    rw [this, map_mul, spinInd_eq_one_of_central ψ hκ, mul_one]
  rw [h1]
  exact hwc.symm

end Induced

section OuterAlpha

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem alphaOf_spin_twin_pair_outer (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F (ι → F))
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) {H : Type} [Group H] [Finite H]
    {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) (hlift : LiftSim Q ψ)
    (hxx' : ψ x = ψ x') (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * spinInd ψ r = spinInd ψ r * v)
    (hvR' : ∀ r ∈ R', v * spinInd ψ r = spinInd ψ r * v) (hy2 : v * v * (v * v) = 1)
    (hy1 : v * v ≠ 1) (hyz : v * v ≠ spinInd ψ x) :
    alphaOf (Subgroup.closure ({spinInd ψ x, v * v} : Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨F₁, hF₁, hF₁', hθx, -⟩ := swap_of_twin_pair hodd hrange hZ hproj hRp hR'p hR hR'
    hinj hinj' hne hx hx2 hx1 hx' hx'2 hx'1 ψ hψ hxx'
  have hv' : ∀ s : spinGroup Q, spinAction Q s ∈ F₁.La.range ⊔ F₁.swap.La.range →
      v * toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ =
        toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ * v := by
    intro s hs
    rw [← hF₁, ← hF₁'] at hs
    exact commute_spinInd_of_mem_map_sup (ker_spinAction_le_center Q) ψ v hvR hvR' hs
  exact alphaOf_spin_frame_centralizer_eq_bot hodd h5 hQ hrange F₁ hV hψ hlift hθx v hv' hy2
    hy1 hyz

end OuterAlpha

end CFSG.ClassicalInvolution.ModelFacts.Orth15
