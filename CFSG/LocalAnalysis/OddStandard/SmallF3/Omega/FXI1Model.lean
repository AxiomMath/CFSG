module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXI1Invol
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXI1Cplx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXI1Orbit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MClassModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fx_false_of_sq_neg_one (hdim : Module.finrank (ZMod 3) V = 6) (γ : ↥(simGroup Q))
    (hγ : ∀ v, (γ : V ≃ₗ[ZMod 3] V) ((γ : V ≃ₗ[ZMod 3] V) v) = -v) {u : OGroup Q}
    (hu1 : simAct Q γ u = u) (hu9 : u ^ 9 = 1) (hu3 : u ^ 3 ≠ 1) : False := by
  refine fx_step5 hdim (g := ((γ : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V))
    (U := ((u : V ≃ₗ[ZMod 3] V) : Module.End (ZMod 3) V))
    (fx_toEnd_mul_self_eq_neg_one _ hγ) (fx_toEnd_commute γ u hu1) ?_ ?_
  · rw [← fx_toEnd_pow, hu9]
    rfl
  · intro h
    apply hu3
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have h1 := congrArg (fun e : Module.End (ZMod 3) V => e v) ((fx_toEnd_pow u 3).trans h)
    simpa using h1

theorem fx_not_mid_of_fixed (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {t : OGroup Q} (htt : t * t = 1) {w : ↥(omegaProj hQ)}
    (hw : w ∈ ffFix hQ (by omega) (QuotientGroup.mk (orthToSim Q t) : ProjSim Q))
    (h9 : orderOf w = 9) : invDim t ≤ 1 ∨ 5 ≤ invDim t := by
  obtain ⟨u, hu1, hu9, hu3⟩ := fx_exists_commuting_nine hQ hdim hsgn (orthToSim Q t) hw h9
  rw [simAct_orthToSim] at hu1
  refine fx_invDim_not_mid hQ hdim htt ?_ hu9 hu3
  calc t * u = (t * u * t⁻¹) * t := by group
    _ = u * t := by rw [hu1]

theorem fx_simHasType_one (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {x : ProjSim Q} (hx1 : x ≠ 1) (hx2 : x * x = 1)
    {w : ↥(omegaProj hQ)} (hw : w ∈ ffFix hQ (by omega) x) (h9 : orderOf w = 9) :
    ∃ α : ℤˣ, SimHasType x 1 α := by
  have fromType : ∀ {r : ℕ} {α : ℤˣ}, SimHasType x r α → ∃ t : OGroup Q, t * t = 1 ∧
      invDim t = r ∧ (QuotientGroup.mk (orthToSim Q t) : ProjSim Q) = x := by
    rintro r α ⟨y, hyx, -, t, htt, hty, hyt⟩
    exact ⟨t, htt, congrArg Prod.fst hty, by rw [← hyx, ← hyt, projOrthToProjSim_toProj]⟩
  have hnot : ∀ {r : ℕ} {α : ℤˣ}, SimHasType x r α → r ≤ 1 ∨ 5 ≤ r := by
    intro r α h
    obtain ⟨t, htt, hd, htx⟩ := fromType h
    rw [← hd]
    exact fx_not_mid_of_fixed hQ hdim hsgn htt (by rw [htx]; exact hw) h9
  rcases ff6m_model_classify hQ hdim hsgn hx2 with h1 | h0 | h4 | h2 | h3 | hN2 | hM4
  · exact absurd h1 hx1
  · have := hnot h0
    omega
  · have := hnot h4
    omega
  · exact h2
  · obtain ⟨α, h3⟩ := h3
    have := hnot h3
    omega
  · obtain ⟨y, hyx, -, -, p, hp, hpy⟩ := hN2
    exfalso
    have hx' : (QuotientGroup.mk (orthToSim Q p) : ProjSim Q) = x := by
      rw [← hyx, ← hpy, projOrthToProjSim_toProj]
    obtain ⟨u, hu1, hu9, hu3⟩ :=
      fx_exists_commuting_nine hQ hdim hsgn (orthToSim Q p) (by rw [hx']; exact hw) h9
    refine fx_false_of_sq_neg_one hdim (orthToSim Q p) (fun v => ?_) hu1 hu9 hu3
    have h1 := LinearEquiv.congr_fun (congrArg (fun z : OGroup Q => (z : V ≃ₗ[ZMod 3] V)) hp) v
    simpa [coe_piOrth_apply] using h1
  · obtain ⟨ρ, hρx, -, hρ⟩ := ff6m_K4_split hQ hdim hsgn hx2 hM4
    exfalso
    obtain ⟨u, hu1, hu9, hu3⟩ :=
      fx_exists_commuting_nine hQ hdim hsgn ρ (by rw [hρx]; exact hw) h9
    exact fx_false_of_sq_neg_one hdim ρ hρ hu1 hu9 hu3

end CFSG.OddStandard.SmallF3.Omega
