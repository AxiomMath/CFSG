module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLAlpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Defs
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.AE

section Cert



variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem ue_quiet_at_u (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (hueC : u * e ∈ Subgroup.centralizer ({u} : Set Y)) :
    ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk u ⟨u * e, hueC⟩ * y = y * oddQuotMk u ⟨u * e, hueC⟩ := by
  obtain ⟨x, _, _, ψ, _, _, hx, _, _, _, _, hψinj, _, hψx, _, _⟩ := AY.frame_psi hc hA5
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hHn : (coreHull (Om R) u).Normal := ⟨fun a ha g' => by
    have h := conj_mem_conjSub (n := g') ha
    rwa [conjSub_coreHull hΩ hc2 g'] at h⟩
  have hHs : IsSubnormal (coreHull (Om R) u) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hHn.isSubnormal
  have hVn : ((vecSub 5).map (mkQ 5)).Normal :=
    (vecSub_normal (n := 5)).map (mkQ 5) (QuotientGroup.mk'_surjective _)
  have hV2 : IsPGroup 2 ↥((vecSub 5).map (mkQ 5)) := by
    rintro ⟨_, a, ha, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (mkQ 5 a) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two, ← map_mul, vecSub_mul_self ha, map_one]
  have hO2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u))
      (⟨(x : ↥(Subgroup.centralizer ({u} : Set Y))), x.2⟩ : ↥(coreHull (Om R) u))) := by
    refine ⟨((vecSub 5).map (mkQ 5)).comap ψ, hVn.comap ψ, hV2.comap_of_injective ψ hψinj, ?_⟩
    show ψ (QuotientGroup.mk x) ∈ (vecSub 5).map (mkQ 5)
    rw [hψx]
    exact Subgroup.mem_map_of_mem _ (zOf_perm _)
  have hxC : (x : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨u * e, hueC⟩ := Subtype.ext hx
  intro L hL
  have h := TL4.quiet_of_inO2_sub hHs x.2 hO2 L hL
  rw [hxC] at h
  exact h

namespace L7

theorem cu_le_normalizer_alpha (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hA5 : SecAE R u 5) (hA6 : SecAE R e 6) :
    Subgroup.centralizer ({u} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hu_ue : u * (u * e) = u * e * u := hWab _ hd.huW _ (W.mul_mem hd.huW heW)
  have hue2 : u * e * (u * e) = 1 := by
    have hue : u * e = e * u := hWab _ hd.huW _ heW
    calc u * e * (u * e) = u * (e * u) * e := by group
      _ = u * (u * e) * e := by rw [hue]
      _ = (u * u) * (e * e) := by group
      _ = 1 := by rw [hd.hu2, hd.he2, one_mul]
  have hsup : ∀ x, x ∈ tightCore R ⊔ K' → u⁻¹ * x ∈ tightCore R ⊔ K' := fun x hx =>
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hd.hu) hx
  have hue1 : u * e ≠ 1 := by
    intro h
    apply e_not_mem_sup hc
    have : e = u⁻¹ * 1 := by rw [← h]; group
    rw [this]; exact hsup 1 (Subgroup.one_mem _)
  have hu_ne : u ≠ u * e := by
    intro h
    exact hd.he1 (by simpa using congrArg (u⁻¹ * ·) h.symm)
  obtain ⟨-, hbal⟩ := hα Y R S t K' W u e g hc (Or.inr (Or.inr (Or.inr hA5)))
  have hmemB : ∀ x, (x = u * e ∨ x = u ∨ x = t) → x ∈ p23B t u e := by
    rintro x (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
  have hA1B : Subgroup.closure ({u, u * e} : Set Y) ≤ p23B t u e := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hmemB _ (Or.inr (Or.inl rfl))
    · exact hmemB _ (Or.inl rfl)
  have hA1E := T7A.isElemAbelian2_closure_pair hd.hu2 hue2 hd.hu1 hue1 hu_ne hu_ue
  have hA1 : alphaOf (Subgroup.closure ({u, u * e} : Set Y)) =
      alphaOf (Subgroup.closure ({u, t} : Set Y)) := hbal _ hA1B hA1E
  have hY : rLayer (Om R) u ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) :=
    (YGam.p23E8YGam_proved hcit hP Y R S t K' W u e g hc hno hA5 hA6).trans
      (p23Gam_le_normalizer hbal hA1B hA1E _)
  intro x hx
  obtain ⟨y, hyY, hyC, hcomm⟩ := p23_cu_frattini hT hc hx
  have hℓC : y⁻¹ * x ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hyC) hx
  have hO := oddCoreOf_centralizer_le_normalizer_alphaOf (c := u) (z := u * e) hue2 hd.hu1 hu_ue
  rw [Set.pair_comm] at hO
  have hN := T7B.mem_normalizer_alphaOf_of_commutator (t := u * e) (z := u) (ℓ := y⁻¹ * x) hue2
    hu_ue hℓC hcomm hO
  rw [Set.pair_comm, hA1] at hN
  have ex : x = y * (y⁻¹ * x) := by group
  rw [ex]
  exact Subgroup.mul_mem _ (hY hyY) hN

theorem ct_le_normalizer_alpha (hα : P23Alpha n) {Z : Subgroup Y} {f : Y}
    (hX : L7Ctx n Y R S t K' W u e g Z f) :
    Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, t} : Set Y)) : Set Y) := by
  have hc := hX.cfg
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hu_ue : u * (u * e) = u * e * u := hWab _ hd.huW _ (W.mul_mem hd.huW heW)
  have hsup : ∀ x, x ∈ tightCore R ⊔ K' → u⁻¹ * x ∈ tightCore R ⊔ K' := fun x hx =>
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hd.hu) hx
  have hue1 : u * e ≠ 1 := by
    intro h
    apply e_not_mem_sup hc
    have : e = u⁻¹ * 1 := by rw [← h]; group
    rw [this]; exact hsup 1 (Subgroup.one_mem _)
  have hu_ne : u * e ≠ u := by
    intro h
    exact hd.he1 (by simpa using congrArg (u⁻¹ * ·) h)
  have hueC : u * e ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hu_ue.symm
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
  have hgC : g ∈ Subgroup.centralizer ({e} : Set Y) := normalizer_le_centralizer_e hd hgN
  have hge : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have h1 : g⁻¹ * (u * e) * g⁻¹⁻¹ = t := by
    rw [← hd.hgt]
    group
  have he2 : e⁻¹ = e := inv_eq_of_mul_eq_one_right hd.he2
  have hge' : g⁻¹ * e * g⁻¹⁻¹ = e := by
    calc g⁻¹ * e * g⁻¹⁻¹ = g⁻¹ * (e * g) := by group
      _ = g⁻¹ * (g * e) := by rw [hge]
      _ = e := by group
  have h2 : g⁻¹ * u * g⁻¹⁻¹ = t * e := by
    calc g⁻¹ * u * g⁻¹⁻¹ = (g⁻¹ * (u * e) * g⁻¹⁻¹) * (g⁻¹ * e⁻¹ * g⁻¹⁻¹) := by group
      _ = t * e := by rw [h1, he2, hge']
  exact ct_le_normalizer_alpha_of_quiet hα hc (Or.inr (Or.inr (Or.inr hX.ae5)))
    (fun heC => e_quiet_at_t_of_zdata hX.zdata heC)
    (fun htC => p23E8Z_t_quiet_at_e hc hX.ae6 htC)
    h2 h1 hd.hu1 hue1 hu_ne hueC (ue_quiet_at_u hc hX.ae5 hueC) hX.zdata

theorem l7_alpha_eq_bot (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) {Z : Subgroup Y} {f : Y}
    (hX : L7Ctx n Y R S t K' W u e g Z f) :
    alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥ := by
  have hc := hX.cfg
  exact p23_alpha_eq_bot hc (p23Two_of_thmEQ8 hE hcit hP Y R S t K' W u e g hc)
    (hα Y R S t K' W u e g hc (Or.inr (Or.inr (Or.inr hX.ae5)))).1
    ⟨cu_le_normalizer_alpha hT hα hcit hP hc hX.noExit hX.ae5 hX.ae6, ct_le_normalizer_alpha hα hX⟩

theorem l7_members_isPGroup (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) {Z : Subgroup Y} {f : Y}
    (hX : L7Ctx n Y R S t K' W u e g Z f) :
    ∀ J ∈ Om R, IsPGroup 2 ↥J :=
  p23E8A_members_isPGroup hE hcit hP hX.cfg hX.ae5 (l7_alpha_eq_bot hE hT hα hcit hP hX)

theorem l7CoreTwo_proved (hE : TwinThmEW.ThmEQ8) (hD4 : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12) (hT4 : TwinThmE.T4Supply) : L7CoreTwo n := by
  intro hcit hP Y _ _ R S t K' W u e g Z f hX
  exact LemL.secCoresTwoGroup_of_isPGroup
    (l7_members_isPGroup hE (hT4 n hcit hP) (p23Alpha_proved hD4 hM12 hT4 hcit hP) hcit hP hX)

end L7

end Cert

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
