module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SG3F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SD
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25L7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SB

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C25W (InFour)

section Six

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem fourData_of_four (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (h4 : Nat.card ↥(cA S R R') = 4) (hcl : Subgroup.closure {a, z} = cA S R R')
    (hbad : BadElt z a) : P25S.FourData hyp a := by
  obtain ⟨ha2, ha1, haz⟩ := cA_pair_facts hyp h4 hcl hbad
  obtain ⟨hzA, hz2, hz1⟩ := z_facts hyp
  have haA : a ∈ cA S R R' := hcl ▸ Subgroup.subset_closure (by simp)
  have hza : a * z = z * a := hyp.hzS a haA.1
  have hA0 : ∀ b ∈ cA S R R', InFour a z b := fun b hb =>
    (P25S.inFour_iff_mem_closure ha2 hz2 hza).mpr (hcl ▸ hb)
  refine ⟨ha2, ha1, haz, haA, fun s hs => ?_, hA0⟩
  have hmem : s * a * s⁻¹ ∈ cA S R R' := by
    have h1 : s * a * s⁻¹ ∈ conjSub s (cA S R R') := Generic.conj_mem_conjSub haA
    rwa [cA_normal hyp hs] at h1
  have hsz : s * z * s⁻¹ = z := by
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
      _ = z := by group
  rcases hA0 _ hmem with h | h | h | h
  · exfalso
    apply ha1
    have : a = s⁻¹ * (s * a * s⁻¹) * s := by group
    rw [this, h]; group
  · exact Or.inl h
  · exfalso
    apply haz
    have : a = s⁻¹ * (s * a * s⁻¹) * s := by group
    rw [this, h]
    calc s⁻¹ * z * s = s⁻¹ * (s * z * s⁻¹) * s := by rw [hsz]
      _ = z := by group
  · exact Or.inr h

theorem not_layerLie6 (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (h4 : Nat.card ↥(cA S R R') = 4) (hcl : Subgroup.closure {a, z} = cA S R R')
    (hbad : BadElt z a) (hT : TwinThmE.T4Supply) (hno : SecNoExitAt Ω a) : ¬ LayerLie Ω a 6 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨D, hD1, i, hi⟩
  have hFD := fourData_of_four hyp h4 hcl hbad
  have ha2 : a * a = 1 := hFD.ha2
  have ha1 : a ≠ 1 := hFD.ha1
  have hacA : a ∈ cA S R R' := hFD.haA
  have hnGF := P25S.not_goodFusion hyp hFD.ha2 hFD.ha1 hFD.haz hFD.haA hFD.hconj hFD.hA0
  unfold C25Y.GoodFusion at hnGF
  push Not at hnGF
  obtain ⟨w, hwC, hw⟩ := hnGF
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  have hS := layer_q8Section hyp ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  obtain ⟨h2, -, hex⟩ := lifts_of_noExit hih.2 hlt hS hno
  obtain ⟨htC, htY, A, A', a₀, b₀, htw⟩ := layer_twinSect0 hyp ha2 ha1 hacA hno
  have hπ : (!piSign 3 1) = true := by decide
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hb2 : (w * z * w⁻¹) * (w * z * w⁻¹) = 1 := by
    calc (w * z * w⁻¹) * (w * z * w⁻¹) = w * (z * z) * w⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hbH2 : (⟨w * z * w⁻¹, hwC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) *
      ⟨w * z * w⁻¹, hwC⟩ = 1 := Subtype.ext hb2
  set β := secAct hΩ hc2 ⟨w * z * w⁻¹, hwC⟩ with hβ
  have hββ : ∀ y, β (β y) = y := by
    intro y
    have h1 : β * β = 1 := by rw [hβ, ← map_mul, hbH2, map_one]
    have h2 := congrArg (fun φ => φ y) h1
    simpa [MulAut.mul_apply] using h2
  obtain ⟨J, hJ, y, hyJ, hy4, hy2, hβy⟩ :=
    ModelFacts.L6C.layer6Cen4_proved 3 1 _ _ D _ _ _ _ _ hD1 ⟨i, by rw [hπ]; exact hi⟩ htw
      (liftFam_conj hyp ha2) β hββ
  obtain ⟨M, hM, hyM⟩ := mem_member_of_mem_liftFam hS.hyp h2 hex hJ hyJ hy4
  obtain ⟨J', hJ', hJ'b⟩ := nc4_lift_sec hyp hΩ hc2 hwC hM hyM hy4 hy2 hβy
  obtain ⟨h, -, hh⟩ := conj_of_member_sec hyp ha2 ha1 hacA hT hbad hJ' hJ'b
  exact hw (h : G) h.2 hh

end Six

section Typing

variable {G : Type} [Group G] [Finite G] [CoreLike G]

@[expose] def LayerT5L (Ω : Set (Subgroup G)) (c : G) : Prop := SecNoExitAt Ω c ∧ LayerLie Ω c 5

end Typing

@[expose] def P25_AE5Excl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a : G,
      Nat.card ↥(cA S R R') = 4 → Subgroup.closure {a, z} = cA S R R' →
      BadElt z a → BadElt z (a * z) → LayerTypedL Ω (a * z) → ¬ LayerAE5 Ω a

@[expose] def P25_OneL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a : G,
      Nat.card ↥(cA S R R') = 4 → Subgroup.closure {a, z} = cA S R R' →
      BadElt z a → BadElt z (a * z) → LayerT5L Ω a

@[expose] def P25_EndL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a : G,
      Nat.card ↥(cA S R R') = 4 → Subgroup.closure {a, z} = cA S R R' →
      BadElt z a → BadElt z (a * z) → LayerT5L Ω a → LayerT5L Ω (a * z) → False

theorem p25_oneL_of_typing (hty : P25_TypedL) (hAx : P25_AE5Excl) : P25_OneL := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a h4 hcl hbad hbad'
  obtain ⟨ha2, ha1, haz⟩ := cA_pair_facts hyp h4 hcl hbad
  obtain ⟨hzA, hz2, hz1⟩ := z_facts hyp
  have haA : a ∈ cA S R R' := hcl ▸ Subgroup.subset_closure (by simp)
  have hza : a * z = z * a := hyp.hzS a haA.1
  have hazA : a * z ∈ cA S R R' := Subgroup.mul_mem _ haA hzA
  have haz2 : (a * z) * (a * z) = 1 := by
    calc (a * z) * (a * z) = a * (z * a) * z := by simp only [mul_assoc]
      _ = a * (a * z) * z := by rw [← hza]
      _ = (a * a) * (z * z) := by simp only [mul_assoc]
      _ = 1 := by rw [ha2, hz2, one_mul]
  have haz1 : a * z ≠ 1 := by
    intro hh
    apply haz
    have : a = z⁻¹ := eq_inv_of_mul_eq_one_left hh
    rw [this]
    exact (inv_eq_of_mul_eq_one_right hz2)
  have hTaz := hty G Ω K K' W S R R' z t u₁ u₂ hyp (a * z) hazA haz2 haz1 hbad'
  rcases hty G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 hbad with ⟨hno, h5 | h6⟩ | hae
  · exact ⟨hno, h5⟩
  · exact (not_layerLie6 hyp h4 hcl hbad TwinThmE.t4Supply_proved hno h6).elim
  · exact (hAx G Ω K K' W S R R' z t u₁ u₂ hyp a h4 hcl hbad hbad' hTaz hae).elim

theorem four_of_oneL_endL (h1 : P25_OneL) (hE : P25_EndL) : C25_11FourP := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a h4 hcl hbad hbad'
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hcl' : Subgroup.closure {a * z, z} = cA S R R' := (closure_az_pair hz2).trans hcl
  have hbad'' : BadElt z (a * z * z) := by rw [mul_z_z hz2]; exact hbad
  exact hE G Ω K K' W S R R' z t u₁ u₂ hyp a h4 hcl hbad hbad'
    (h1 G Ω K K' W S R R' z t u₁ u₂ hyp a h4 hcl hbad hbad')
    (h1 G Ω K K' W S R R' z t u₁ u₂ hyp (a * z) h4 hcl' hbad' hbad'')

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem twinPerp25A_of_typing_leaves {n : ℕ} (hE : TwinThmE.EIHAll n)
    (hA4 : Q8P.Asc77.P25S.P25_A4) (hAE : Q8P.Asc77.P25R.AE5SqModel)
    (hO2 : Q8P.Asc77.P25R.P25_TypedO2) (hE4 : Q8P.Asc77.P25R.P25_TypedE4)
    (hAx : Q8P.Asc77.P25R.P25_AE5Excl) (hEnd : Q8P.Asc77.P25R.P25_EndL) : TwinPerp25A n :=
  twinPerp25A_of_9_fourP hE
    (Q8P.Asc77.P25S.c25_9P_of_a4_nomixed hA4
      (Q8P.Asc77.P25S.no_mixed_of_sqz (Q8P.Asc77.P25R.p25_sqZ_of_exits_proved hAE hO2 hE4)))
    (Q8P.Asc77.P25R.four_of_oneL_endL
      (Q8P.Asc77.P25R.p25_oneL_of_typing
        (Q8P.Asc77.P25R.p25_typedL_of_exits TwinThmE.t4Supply_proved TwinDisc.oddCentEdge_proved hO2 hE4)
        hAx) hEnd)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
