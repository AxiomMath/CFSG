module

public import CFSG.LargeExtraspecial.S8Mod
public import CFSG.LargeExtraspecial.S8Std

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

theorem dvd_finrank_of_invariant (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    {E : Submodule (ZMod 2) (Vt S g t)} (hE : E ⊓ perp D.Q E = ⊥) {k : ℕ} (hk : 2 ≤ k)
    (hEdim : finrank (ZMod 2) (perp D.Q E) = 2 * k)
    {U : Submodule (ZMod 2) (S.Qt ⧸ Vt S g t)} (hUW : U ≤ (Wt S g t).map (Vt S g t).mkQ)
    (hU : ∀ r : Rbar S g t, resV H.conj_mem t r ∈ fixGroup E → ∀ w ∈ Wt S g t,
      (Vt S g t).mkQ w ∈ U → (Vt S g t).mkQ (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ U) :
    2 ^ (k - 1) ∣ finrank (ZMod 2) U ∧
      (IsMinusType D.Q E k → 2 ^ k ∣ finrank (ZMod 2) U) := by
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_1_two hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
  obtain ⟨N', hN'⟩ : ∃ N' : Submodule (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ),
      N' = U.comap ((Wt S g t).map (Vt S g t).mkQ).subtype := ⟨_, rfl⟩
  have hfin : finrank (ZMod 2) N' = finrank (ZMod 2) U := by
    rw [hN']
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hUW)
  have hN'inv : OmegaInvariant ρ E N' := by
    intro e he v hv
    have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV H.conj_mem t).range := by
      rw [range_resV, D.hX]; exact e.2
    obtain ⟨r, hr⟩ := heR
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp v.2
    have hv' : v = secMk (Vt S g t) hw := Subtype.ext hwv.symm
    have h1 := hρ e r hr.symm w hw
    rw [← hv'] at h1
    rw [hN'] at hv ⊢
    change ((ρ e v : (Wt S g t).map (Vt S g t).mkQ) : S.Qt ⧸ Vt S g t) ∈ U
    rw [h1]
    refine hU r (hr ▸ he) w hw ?_
    change (v : S.Qt ⧸ Vt S g t) ∈ U at hv
    rw [← hwv] at hv
    exact hv
  have hF : (⊥ : Submodule (ZMod 2) (Vt S g t)) ⊓ perp D.Q ⊥ = ⊥ := bot_inf_eq _
  have hdimV : finrank (ZMod 2) (perp D.Q (⊥ : Submodule (ZMod 2) (Vt S g t))) = 2 * D.m := by
    rw [perp_bot, finrank_top]; exact D.hdim
  have h3V : 3 ≤ finrank (ZMod 2) (perp D.Q (⊥ : Submodule (ZMod 2) (Vt S g t))) := by
    rw [hdimV]; have := D.hm; omega
  have h3E : 3 ≤ finrank (ZMod 2) (perp D.Q E) := by omega
  obtain ⟨p, hpE, hp0, hp⟩ := exists_singular_mem_perp (q := D.Q) (F := E) h3E
  obtain ⟨p₁, hp₁E, hp₁, hpp₁⟩ := exists_hyperbolic_partner D.hQ hE hpE hp0 hp
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hpp₁' : polar D.Q p₁ p = 1 := by rw [polar_comm]; exact hpp₁
  have htop : OmegaInvariant ρ ⊥ (⊤ : Submodule (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ)) :=
    fun _ _ _ _ => Submodule.mem_top
  have hmem : ∀ v : Vt S g t, v ∈ perp D.Q (⊥ : Submodule (ZMod 2) (Vt S g t)) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hD' : RadDecomp ρ ⊥ ⊤ p p₁ :=
    radDecomp_of_pair ρ hF h3V htop (hmem _) (hmem _) (hmem _) (hmem _) (aV_ne_zero H ht) hp0
      D.hQa D.Q_bV hp hp₁ D.polar_aV_bV hpp₁ hD
  obtain ⟨c, -, -, hcR, hc1, hca⟩ := exists_mem_radFix_not_isTypeA D.hQ hE h3E hpE hp₁E hp0 hp
    hpp₁
  obtain ⟨c₁, -, -, hc₁R, hc₁1, hc₁a⟩ := exists_mem_radFix_not_isTypeA D.hQ hE h3E hp₁E hpE
    hp₁0 hp₁ hpp₁'
  have hD'' : RadDecomp ρ E N' p p₁ :=
    radDecomp_mono ρ hF D.hm hdimV htop (hmem _) (hmem _) hp0 hp hp₁ hpp₁ hD' bot_le le_top
      (x := ⟨_, (radFix_le_omegaFix D.hQ hp₁0 hp₁ hc₁R).1⟩)
      (y := ⟨_, (radFix_le_omegaFix D.hQ hp0 hp hcR).1⟩) hc₁R hc₁1 hc₁a hcR hc1 hca
      (fun v hv => hN'inv _ hc₁R.2 v hv) (fun v hv => hN'inv _ hcR.2 v hv)
  refine ⟨?_, fun hmin => ?_⟩
  · rw [← hfin]
    exact timmesfeld_2_1_b_dvd ρ k hE (by omega) hEdim hN'inv hpE hp₁E hp0 hp hp₁ hpp₁ hD''
  · rw [← hfin]
    exact timmesfeld_2_1_b_dvd_minus ρ k hE hk hEdim hmin hN'inv hpE hp₁E hp0 hp hp₁ hpp₁ hD''

theorem comm_mem_Nbar_of_fix (H : Hyp4 S g) {τ r : S.O} (hτM : τ ∈ S.Mbar) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hr : r ∈ Rbar S g t) :
    r * τ * r⁻¹ * τ⁻¹ ∈ Nbar S g t := by
  obtain ⟨k₀, rfl⟩ := MonoidHom.mem_range.mp hτM
  have h1 : S.ρ k₀ * r⁻¹ * (S.ρ k₀)⁻¹ ∈ Rbar S g t := conj_mem_Rbar hτt (inv_mem hr)
  have h2 : r * S.ρ k₀ * r⁻¹ * (S.ρ k₀)⁻¹ ∈ Rbar S g t := by
    have := (Rbar S g t).mul_mem hr h1
    rwa [← mul_assoc, ← mul_assoc] at this
  refine mem_Nbar.mpr ⟨h2, fun v hv => ?_⟩
  have hτinv : ((S.ρ k₀)⁻¹ : S.O) • v = v := by
    change (((S.ρ k₀)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    conv_lhs => rw [← hτV v hv]
    exact inv_apply_apply_O _ v
  have hrv : ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t :=
    apply_mem_Vt_of_mem_Rbar H.conj_mem (inv_mem hr) hv
  change (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ k₀ : S.Qt ≃ₗ[ZMod 2] S.Qt)
    (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((((S.ρ k₀)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v))) = v
  change (((S.ρ k₀)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v at hτinv
  rw [hτinv, hτV _ hrv, apply_inv_apply_O]

theorem fix_Wt_of_fix_Vt (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) {x τ : S.O} (hxM : x ∈ S.Mbar)
    (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hbig : 2 * D.m < 2 ^ (D.m - 1) ∨ (D.IsMinus ∧ 2 * D.m < 2 ^ D.m)) :
    ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have hF : (⊥ : Submodule (ZMod 2) (Vt S g t)) ⊓ perp D.Q ⊥ = ⊥ := bot_inf_eq _
  have hdimV : finrank (ZMod 2) (perp D.Q (⊥ : Submodule (ZMod 2) (Vt S g t))) = 2 * D.m := by
    rw [perp_bot, finrank_top]; exact D.hdim
  obtain ⟨hdvd, hdvd'⟩ := dvd_finrank_of_invariant hCE hNo hΩ D hF D.hm hdimV
    (commWV_le H C ht ht1 hVQ hτt) (fun r _ w _ hw => mkQ_apply_mem_commWV H C ht ht1 hVQ D.hN
      hτt r.2 (comm_mem_Nbar_of_fix H hτM hτt hτV r.2) hw)
  have hle := finrank_commWV_le H C ht ht1 hVQ hxτ
  rw [D.hdim] at hle
  have h0 : finrank (ZMod 2) (commWV S g t τ) = 0 := by
    rcases hbig with h | ⟨hmin, h⟩
    · exact Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    · refine Nat.eq_zero_of_dvd_of_lt (hdvd' fun T _ hT => hmin T hT) (by omega)
  have hbot := Submodule.finrank_eq_zero.mp h0
  intro w hw
  have hmem : (Vt S g t).mkQ ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) ∈ commWV S g t τ :=
    mem_commWV.mpr ⟨w, hw, rfl⟩
  rw [hbot, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
  exact hmem

end CFSG.LargeExtraspecial.S8
