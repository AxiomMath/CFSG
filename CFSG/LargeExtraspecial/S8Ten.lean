module

public import CFSG.LargeExtraspecial.S8Three
public import CFSG.LargeExtraspecial.S8Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem Std.finrank_WV (D : Std H C ht ht1 hVQ) :
    finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) + 4 * D.m = 2 * S.width := by
  have h1 := finrank_WV_add_finrank_Vt H ht1 (g := g)
  have h2 := finrank_Wt (S := S) (g := g) (t := t)
  rw [S.finrank_Qt_eq_two_mul_width] at h2
  have := D.hdim
  omega

theorem Std.pos_finrank_WV (D : Std H C ht ht1 hVQ)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    0 < finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) := by
  by_contra h0
  push Not at h0
  have hw := D.finrank_WV
  have hn : S.width = 2 * D.m := by omega
  have hA := D.hA
  rw [D.hdim, hn] at hA
  have hm := D.hm
  have hcard : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) = 2 := by
    have e : 2 ^ (2 * D.m) = 2 * 2 ^ (2 * D.m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e] at hA
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hA
  apply hA7
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hle : zpowers t ≤ S.Lbar g ⊓ Nbar S g t := by
    rw [zpowers_le]; exact ⟨ht, self_mem_Nbar H ht⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, Nat.card_zpowers, hto]

theorem comm_mem_Nbar_of_transvection (D : Std H C ht ht1 hVQ) {τ r : S.O} (hτM : τ ∈ S.Mbar)
    (hτt : τ * t = t * τ) (hττ : τ * τ = 1) {d : Vt S g t}
    (hτd : ∀ v : Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + polar D.Q v d • (d : S.Qt))
    (hr : r ∈ Rbar S g t) (hrd : resV H.conj_mem t ⟨r, hr⟩ d = d) :
    τ * r * τ⁻¹ * r⁻¹ ∈ Nbar S g t := by
  obtain ⟨k₀, rfl⟩ := MonoidHom.mem_range.mp hτM
  have h1 : S.ρ k₀ * r * (S.ρ k₀)⁻¹ ∈ Rbar S g t := conj_mem_Rbar hτt hr
  have h2 : S.ρ k₀ * r * (S.ρ k₀)⁻¹ * r⁻¹ ∈ Rbar S g t := mul_mem h1 (inv_mem hr)
  refine mem_Nbar.mpr ⟨h2, fun v hv => ?_⟩
  have hτinv : (S.ρ k₀)⁻¹ = S.ρ k₀ := inv_eq_of_mul_eq_one_right hττ
  have hreO : resV H.conj_mem t ⟨r, hr⟩ ∈ TauCeti.QuadraticMap.orthogonalGroup D.Q := by
    have : resV H.conj_mem t ⟨r, hr⟩ ∈ omegaGroup D.Q D.hQ := by
      rw [← D.hX, ← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
    exact (mem_omegaGroup.mp this).1
  set u : Vt S g t := resV H.conj_mem t ⟨r, hr⟩⁻¹ ⟨v, hv⟩ with hu
  have hru : resV H.conj_mem t ⟨r, hr⟩ u = ⟨v, hv⟩ := by
    rw [hu, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hpu : polar D.Q u d = polar D.Q (⟨v, hv⟩ : Vt S g t) d := by
    rw [← hru, ← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hreO u d, hrd]
  have hru' : ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt)) = v := by
    have := congrArg Subtype.val hru
    rwa [coe_resV_apply] at this
  have hrinv : (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = (u : S.Qt) := by
    rw [← hru', inv_apply_apply_O]
  have hrd' : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (d : S.Qt) = d := by
    have := congrArg Subtype.val hrd
    rwa [coe_resV_apply] at this
  have hτdd : (S.ρ k₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (d : S.Qt) = d := by
    rw [hτd d, polar_self_eq_zero, zero_smul, add_zero]
  change (S.ρ k₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt)
    ((((S.ρ k₀)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v))) = v
  rw [hrinv, hτinv, hτd u, map_add, map_smul, hru', hrd', map_add, map_smul, hτdd,
    hτd ⟨v, hv⟩, hpu]
  change v + polar D.Q (⟨v, hv⟩ : Vt S g t) d • (d : S.Qt) +
    polar D.Q (⟨v, hv⟩ : Vt S g t) d • (d : S.Qt) = v
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem false_of_transvection_ten (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) (hm5 : D.m = 5) (hplus : ¬ D.IsMinus)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    {d : Vt S g t} (hd : D.Q d = 1)
    (hτd : ∀ v : Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + polar D.Q v d • (d : S.Qt)) :
    False := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hττ : τ * τ = 1 := by
    rw [hxτ]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have hdim10 : finrank (ZMod 2) (Vt S g t) = 10 := by rw [D.hdim, hm5]
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact zero_ne_one hd
  have hlow := finrank_WV_le_two_mul_finrank_commWV D hfus hxM hxτ hτt hd hτd
  obtain ⟨y, hy⟩ : ∃ y : Vt S g t, polar D.Q y d = 1 := by
    obtain ⟨y, hy⟩ := (exists_mem_perp_polar_eq_one D.hQ (F := ⊥) (bot_inf_eq _)
      (by rw [perp_bot]; exact Submodule.mem_top) hd0)
    exact ⟨y, hy.2⟩
  have hτy : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (y : S.Qt) ≠ y := by
    rw [hτd y, hy, one_smul]
    intro h
    apply hd0
    have : (d : S.Qt) = 0 := by
      have h' := congrArg (· - (y : S.Qt)) h
      simpa using h'
    exact Subtype.ext this
  have hup := finrank_commWV_add_one_le H C ht ht1 hVQ hxτ hτt y.2 hτy
  rw [hdim10] at hup
  have hdvd := timmesfeld_6_1_two_dvd hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE D.hQa
    D.polar_aV_bV (m := D.m) (by have := D.hm; omega) D.hdim
  rw [hm5] at hdvd
  have hpos := D.pos_finrank_WV hA7
  have hWV16 : finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 16 := by
    obtain ⟨c, hc⟩ := hdvd
    norm_num at hc
    omega
  set F'' := (fixWV S g t τ).map (Vt S g t).mkQ with hF''
  have hVfix : Vt S g t ≤ fixWV S g t τ := fun v hv =>
    ⟨Vt_le_Wt H ht1 hv, (Vt S g t).sub_mem
      (apply_mem_Vt_of_mem_CMt haQ (mem_CMt.mpr ⟨hτM, hτt⟩) hv) hv⟩
  have hfF := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ (fixWV S g t τ)
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hVfix, ← hF''] at hfF
  have hcf := finrank_commWV_add_finrank_fixWV (S := S) (g := g) t τ
  have hwv := finrank_WV_add_finrank_Vt H ht1 (g := g) (t := t)
  have hF''W : F'' ≤ (Wt S g t).map (Vt S g t).mkQ :=
    Submodule.map_mono (inf_le_left : fixWV S g t τ ≤ Wt S g t)
  obtain ⟨e, he, hde⟩ := exists_aniso_partner D.hQ hd (by rw [hdim10]; norm_num)
  set E : Submodule (ZMod 2) (Vt S g t) := Submodule.span (ZMod 2) {d, e} with hEdef
  have hF : (⊥ : Submodule (ZMod 2) (Vt S g t)) ⊓ perp D.Q ⊥ = ⊥ := bot_inf_eq _
  have hmemP : ∀ v : Vt S g t, v ∈ perp D.Q (⊥ : Submodule (ZMod 2) (Vt S g t)) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hE : E ⊓ perp D.Q E = ⊥ := by
    have := sup_span_pair_inf_perp_eq_bot hF (hmemP d) (hmemP e) hde
    rwa [bot_sup_eq] at this
  have hEdim : finrank (ZMod 2) (perp D.Q E) = 2 * 4 := by
    have := finrank_perp_sup_span_pair D.hQ hF (hmemP d) (hmemP e) hde
    rw [bot_sup_eq, perp_bot, finrank_top, hdim10, ← hEdef] at this
    omega
  have hE2 : finrank (ZMod 2) E = 2 := finrank_span_pair (linearIndependent_of_polar_eq_one hde)
  have hEa : ∀ v ∈ E, D.Q v = 0 → v = 0 := by
    intro v hv hQv
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
    have h0 : D.Q (a • d + b • e) = a * a * D.Q d + b * b * D.Q e + a * b * polar D.Q d e := by
      rw [show D.Q (a • d + b • e) = D.Q (a • d) + D.Q (b • e) + polar D.Q (a • d) (b • e) by
        rw [polar]; abel, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
        polar_smul_right, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      ring
    rw [h0, hd, he, hde] at hQv
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
      rcases zmod2_eq_zero_or_eq_one b with rfl | rfl
    · simp
    · exact absurd hQv (by decide)
    · exact absurd hQv (by decide)
    · exact absurd hQv (by decide)
  have hdE : d ∈ E := Submodule.subset_span (by simp)
  have hmin : IsMinusType D.Q E 4 := by
    unfold Std.IsMinus at hplus
    push Not at hplus
    obtain ⟨T, hT, hTm⟩ := hplus
    exact isMinusType_of_aniso D.hQ hE hE2 hEa (by rw [hdim10]) hT (by omega)
  obtain ⟨-, hdvd'⟩ := dvd_finrank_of_invariant hCE hNo hΩ D hE (by norm_num) hEdim hF''W
    (fun r hrE w hw hwF => by
      obtain ⟨w₁, hw₁, hw₁w⟩ := Submodule.mem_map.mp hwF
      have hrd : resV H.conj_mem t r d = d := hrE d hdE
      have hcomm := comm_mem_Nbar_of_transvection D hτM hτt hττ hτd r.2 hrd
      have h1 := apply_mem_fixWV H C ht ht1 hVQ D.hN hτt r.2 hcomm hw₁
      refine ⟨_, h1, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← map_sub]
      have : w₁ - w ∈ Vt S g t := by
        rw [← Submodule.Quotient.eq]
        exact hw₁w
      exact apply_mem_Vt_of_mem_Rbar haQ r.2 this)
  have h16 := hdvd' hmin
  have hlo : 7 ≤ finrank (ZMod 2) F'' := by omega
  have hhi : finrank (ZMod 2) F'' ≤ 8 := by omega
  obtain ⟨c, hc⟩ := h16
  norm_num at hc
  omega

end CFSG.LargeExtraspecial.S8
