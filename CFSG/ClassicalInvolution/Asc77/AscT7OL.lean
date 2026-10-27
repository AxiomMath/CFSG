module

public import CFSG.ClassicalInvolution.Asc77.AscT7OK
public import CFSG.ClassicalInvolution.Asc77.AscT7OF

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

open CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.Dichotomy QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

section Sq

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)}

theorem alphaOf_spin_twin_pair_sq (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hV : 7 ≤ Module.finrank F (ι → F))
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x') {H : Type} [Group H] [Finite H]
    {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hlift : LiftSimFr Q ψ) {k : spinGroup Q} (hk : k ∈ R) (hkk : ψ k * ψ k = ψ x)
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * spinInd ψ r = spinInd ψ r * v)
    (hvR' : ∀ r ∈ R', v * spinInd ψ r = spinInd ψ r * v) (hvv : v * v = spinInd ψ x) :
    alphaOf (Subgroup.closure ({spinInd ψ k * v, spinInd ψ x} :
      Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  classical
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨F₁, hF₁, hF₁', hθx, -⟩ := swap_of_twin_pair_ord hodd hRp hR'p hR hR' hinj hinj' hne hx
    hx2 hx1 hx' hx'2 hx'1 hord
  have hv' : ∀ s : spinGroup Q, spinAction Q s ∈ F₁.La.range ⊔ F₁.swap.La.range →
      v * toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ =
        toInducedAutOn ψ.range ⟨ψ s, mem_normalizer_range ψ s⟩ * v := by
    intro s hs
    rw [← hF₁, ← hF₁'] at hs
    exact commute_spinInd_of_mem_map_sup (ker_spinAction_le_center Q) ψ v hvR hvR' hs
  have hσ : ∀ s : spinGroup Q, spinAction Q s ∈ F₁.La.range ⊔ F₁.swap.La.range →
      ∀ ℓ : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * (v : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    have h := congrArg (fun g : ↥(inducedAutOn ψ.range) => ((g : MulAut ↥ψ.range) ℓ : ↥ψ.range))
      (hv' s hs)
    exact Subtype.ext (congrArg Subtype.val h)
  obtain ⟨e, he, hker, hnorm, hcent⟩ := exists_hom_spin hodd hQ (by omega) hrange ψ hψ
  have : Finite ↥(inducedAutOn ψ.range) := inferInstance
  have := hnorm
  obtain ⟨α, w, hαψ, hwO, hwspan, hθw⟩ := exists_isometry_of_centralizing_at hodd h5 hrange F₁ hψ
    (v : MulAut ↥ψ.range) (hlift F₁ (v : MulAut ↥ψ.range) hσ) hσ
  have hconj := conj_e_of_lift e he hrange v α w hαψ hθw
  have hzmem : F₁.La (-1) ∈ elementaryGroup Q := F₁.La_mem_elementaryGroup (-1)
  set zE : ↥(elementaryGroup Q) := ⟨F₁.La (-1), hzmem⟩ with hzE
  have hmemθ : ∀ s : spinGroup Q, spinAction Q s ∈ elementaryGroup Q := fun s => by
    rw [← hrange]; exact ⟨s, rfl⟩
  have hez : e zE = spinInd ψ x := by
    have := he x (hmemθ x)
    rw [spinInd_apply, ← this]
    congr 1
    exact Subtype.ext hθx.symm
  have hy_mem : w * w ∈ elementaryGroup Q := sq_mem_of_frame hodd hQ F₁ hV hwO
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift hrange α hy_mem hθw
  have hey : e ⟨w * w, hy_mem⟩ = v * v := e_sq_eq e he v α hαψ hy_mem hŷ hαα
  have hLinv : (F₁.La (-1))⁻¹ = F₁.La (-1) := inv_eq_of_mul_eq_one_right F₁.La_neg_one_mul_self
  have hLL : ∀ u, F₁.La (-1) (F₁.La (-1) u) = u := fun u =>
    congrArg (fun m : (ι → F) ≃ₗ[F] (ι → F) => m u) F₁.La_neg_one_mul_self
  have hww : ∀ u, w (w u) = -(F₁.La (-1) u) := by
    have h1 : e (⟨w * w, hy_mem⟩ * zE⁻¹) = 1 := by
      rw [map_mul, map_inv, hey, hvv, hez, mul_inv_cancel]
    obtain ⟨c₁, hc₁⟩ := mem_scalars.mp (hker _ h1)
    obtain ⟨z₀, hz₀, hz₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (span_ne_bot F₁)
    have hLz₀ : F₁.La (-1) z₀ = -z₀ := La_neg_one_of_mem_span F₁ hz₀
    have hc₁' : ∀ u, w (w ((F₁.La (-1))⁻¹ u)) = c₁ • u := fun u => hc₁ u
    have hc1 : c₁ = -1 := by
      have h2' := hc₁' z₀
      rw [hLinv, hLz₀, map_neg, map_neg, hwspan z₀ hz₀, hwspan z₀ hz₀] at h2'
      have : (c₁ + 1) • z₀ = 0 := by
        rw [add_smul, one_smul, ← h2', neg_add_cancel]
      exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp this).resolve_right hz₀0)
    intro u
    have h3 := hc₁' (F₁.La (-1) u)
    rw [hLinv, hLL, hc1, neg_one_smul] at h3
    exact h3
  have hkmem : spinAction Q k ∈ F₁.La.range := hF₁ ▸ Subgroup.mem_map_of_mem _ hk
  obtain ⟨a, ha⟩ := hkmem
  have hLaE : ∀ b : SL(2, F), F₁.La b ∈ elementaryGroup Q := fun b => F₁.La_mem_elementaryGroup b
  have hek : e ⟨F₁.La a, hLaE a⟩ = spinInd ψ k := by
    have := he k (hmemθ k)
    rw [spinInd_apply, ← this]
    congr 1
    exact Subtype.ext ha
  have hκκ : spinInd ψ k * spinInd ψ k = spinInd ψ x := by
    rw [← map_mul, spinInd_apply, spinInd_apply]
    congr 1
    exact Subtype.ext (by simpa [map_mul] using hkk)
  have hperp : F₁.perp ≠ ⊥ := perp_ne_bot F₁ (by omega)
  have haa : a * a = -1 := by
    have h1 : e (⟨F₁.La a, hLaE a⟩ * ⟨F₁.La a, hLaE a⟩) = e zE := by
      rw [map_mul, hek, hκκ, hez]
    have h3 := eq_of_e_eq_of_fix_perp hker hperp h1
      (fun u hu => by
        change F₁.La a (F₁.La a u) = u
        rw [La_fix_perp F₁ a hu, La_fix_perp F₁ a hu])
      (fun u hu => La_fix_perp F₁ (-1) hu)
    apply F₁.La_injective
    have := congrArg Subtype.val h3
    simpa [← map_mul] using this
  have hz : ∀ n ∈ involutionOddCore (e zE), n = 1 := by
    rw [hez]
    exact oddCore_frame_eq_one hodd h5 hQ hrange F₁ hV hψ hlift hθx
  have key := alphaOf_klein_of_twist hodd h5 hQ F₁ hV e hker hwO hwspan hww hconj
    (by rw [hvv, hez]) haa hz
  rw [hek, hez] at key
  exact key

end Sq

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
