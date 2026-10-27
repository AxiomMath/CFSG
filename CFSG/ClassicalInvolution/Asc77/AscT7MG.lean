module

public import CFSG.ClassicalInvolution.Asc77.AscT7JSq

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)

section Neg

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem twinSqAlphaOn_of_spin_neg (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F (ι → F))
    (hneg : (LinearEquiv.neg F : (ι → F) ≃ₗ[F] (ι → F)) ∉ elementaryGroup Q)
    (hproj : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hlift : ∀ (H : Type) [Group H] [Finite H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → LiftSim Q ψ)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) ∈ fundSet Q)
    (hperf : ∀ R ∈ fundamentalSubgroups t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) :
    TwinSqAlphaOn t ⟨spinGroup Q, D⟩ := by
  intro H _ _ ψ R R' x x' hpair k hk hkk v hvR hvR' hvv
  exfalso
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have h3 : 3 ≤ Module.finrank F (ι → F) := by omega
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R hpair.mem r hr (ModelFacts.Orth15.mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  have hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1 :=
    injOn_of_ker_le_center (ker_spinAction_le_center Q) fun r hr hcen =>
      hnc R' hpair.mem' r hr (ModelFacts.Orth15.mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  obtain ⟨F₁, hF₁, hF₁', hθx, -⟩ := swap_of_twin_pair hodd hrange hZ hproj (hperf R hpair.mem)
    (hperf R' hpair.mem') (hcorr R hpair.mem) (hcorr R' hpair.mem') hinj hinj' hpair.ne
    hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 ψ hpair.ker hpair.same
  have hv' : ∀ s : spinGroup Q, spinAction Q s ∈ F₁.La.range ⊔ F₁.swap.La.range →
      v * toInducedAutOn ψ.range ⟨ψ s, ModelFacts.Orth15.mem_normalizer_range ψ s⟩ =
        toInducedAutOn ψ.range ⟨ψ s, ModelFacts.Orth15.mem_normalizer_range ψ s⟩ * v := by
    intro s hs
    rw [← hF₁, ← hF₁'] at hs
    exact commute_spinInd_of_mem_map_sup (ker_spinAction_le_center Q) ψ v hvR hvR' hs
  obtain ⟨e, he, hker, hnorm, hcent⟩ := exists_hom_spin hodd hQ h3 hrange ψ hpair.ker
  have hσ : ∀ s : spinGroup Q, spinAction Q s ∈ F₁.La.range ⊔ F₁.swap.La.range →
      ∀ ℓ : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * (v : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    have h := congrArg
      (fun g : ↥(inducedAutOn ψ.range) => ((g : MulAut ↥ψ.range) ℓ : ↥ψ.range)) (hv' s hs)
    exact Subtype.ext (congrArg Subtype.val h)
  obtain ⟨α, w, hαψ, hwiso, hwspan, hθw⟩ :=
    exists_isometry_of_centralizing hodd h5 hrange F₁ hpair.ker (hlift H ψ hpair.ker)
      (v : MulAut ↥ψ.range) hσ
  have hy_mem : w * w ∈ elementaryGroup Q := sq_mem_of_frame hodd hQ F₁ hV hwiso
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift hrange α hy_mem hθw
  have hey : e ⟨w * w, hy_mem⟩ = v * v := e_sq_eq e he v α hαψ hy_mem hŷ hαα
  have hzmem : F₁.La (-1) ∈ elementaryGroup Q := F₁.La_mem_elementaryGroup (-1)
  have hez : e ⟨F₁.La (-1), hzmem⟩ = FrameVertex.innerHom ψ x := by
    have := he x (by rw [hθx]; exact hzmem)
    rw [FrameVertex.innerHom_apply, ← this]
    congr 1
    exact Subtype.ext hθx.symm
  have hsq1 : e ⟨(w * w) * F₁.La (-1), mul_mem hy_mem hzmem⟩ = 1 := by
    have h1 : e ⟨(w * w) * F₁.La (-1), mul_mem hy_mem hzmem⟩ =
        e ⟨w * w, hy_mem⟩ * e ⟨F₁.La (-1), hzmem⟩ := by
      rw [← map_mul]
      rfl
    rw [h1, hey, hez, hvv, ← map_mul, hpair.hx2, map_one]
  obtain ⟨c, hc⟩ := mem_scalars.mp (hker _ hsq1)
  have hne : F₁.incl 1 ≠ 0 := by
    intro h0
    have := congrArg F₁.coords h0
    rw [Frame.coords_incl, map_zero] at this
    exact one_ne_zero (congrFun (congrFun this 0) 0)
  have hspan1 : F₁.incl 1 ∈ F₁.span := ⟨1, rfl⟩
  have hc1 : c = -1 := by
    have h1 := hc (F₁.incl 1)
    have h2' : ((w * w) * F₁.La (-1)) (F₁.incl 1) = -(F₁.incl 1) := by
      simp [LinearEquiv.mul_apply, La_neg_one_of_mem_span F₁ hspan1, hwspan _ hspan1]
    rw [h2'] at h1
    have h3 : (c + 1) • F₁.incl 1 = 0 := by
      rw [add_smul, one_smul, ← h1]
      simp
    exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp h3).resolve_right hne)
  have hww : (w * w) * F₁.La (-1) = LinearEquiv.neg F := by
    refine LinearEquiv.ext fun z => ?_
    rw [hc z, hc1]
    simp
  exact hneg (hww ▸ mul_mem hy_mem hzmem)

end Neg

end CFSG.ClassicalInvolution.Asc77
