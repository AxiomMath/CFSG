module

public import CFSG.LargeExtraspecial.S10SixD
public import CFSG.LargeExtraspecial.S10FiveB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem clSub_inf_fixSub_Bbar (X : Hyp10 S g t) {k : S.M} (hk : S.ρ k ∈ Rbar S g t) :
    S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ fixSub S (S.Lbar ((k : G) * g) ⊓ Nbar S g t) =
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vt S g t := by
  have hle : S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vt S g t ≤
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ fixSub S (S.Lbar ((k : G) * g) ⊓ Nbar S g t) :=
    fun v hv => ⟨hv.1, fun x hx => (mem_Nbar.mp hx.2).2 v hv.2⟩
  have hcard := card_mul_two_pow_finrank_fix (X.H.mul k) (X.C.mul k)
    (inf_le_left : S.Lbar ((k : G) * g) ⊓ Nbar S g t ≤ _)
  rw [card_Abar_mul X hk, X.card_Abar] at hcard
  have h5 := X.five_le_width
  have hdim : finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓
      fixSub S (S.Lbar ((k : G) * g) ⊓ Nbar S g t)) = 3 := by
    have h1 : 2 ^ S.width = 2 ^ (S.width - 3) * 2 ^ 3 := by
      rw [← pow_add]
      congr 1
      omega
    rw [h1] at hcard
    exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left (by positivity) hcard)
  have hth := mem_Lbar_mul_of_mem_Rbar X.H X.ht hk
  have hVQk := not_V_le_Qa_mul X.H X.hVQ hk
  have h2 := finrank_clSub_inf_Vt (X.H.mul k) (X.C.mul k) hth X.ht1 hVQk
  rw [Vt_mul, X.h4] at h2
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  omega

theorem Vt_inf_Vt_le_clSub (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {τ : S.O}
    (Y : Hyp10 S g τ) (hτN : τ ∈ Nbar S g t) (hτt : τ ≠ t) :
    Vt S g t ⊓ Vt S g τ ≤ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨x, hx, hxN⟩ := exists_mem_Abar_tau_not_mem hCE X Y hτN hτt
  obtain ⟨k, hk, -, hb⟩ := Y.exists_pair
  have hNY := (timmesfeld_10_1_two hCE Y hk hb).2.2.2.2
  have hVW := Vt_le_Wt_of_mem_Nbar Y hτN
  have hD : (Vt S g t).map (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤
      Vt S g t ⊓ Vt S g τ := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨sub_mem (apply_mem_Vt_of_mem_Rbar X.haQ (Lbar_le_Rbar X.ht hx.1) hv) hv,
      hNY x hx.2 v (hVW hv)⟩
  have hDeq : (Vt S g t).map (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) =
      Vt S g t ⊓ Vt S g τ := by
    refine Submodule.eq_of_le_of_finrank_le hD ?_
    rw [finrank_map_Vt_of_Lbar X hx.1 hxN]
    exact finrank_Vt_inf_Vt_le hCE X Y hτN hτt
  rw [← hDeq]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨w, hwQ, rfl⟩ := S.exists_cl v
  have hwa : w * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * w := by
    rw [← S.polar_cl_eq_zero_iff hwQ X.haQ]
    exact (mem_Wt.mp (Vt_le_Wt X.H X.ht1 (cl_a_mem_Vt X.ht))) _ hv
  exact X.C.comm_le w ⟨hwQ, mem_centralizer_singleton_iff.mpr hwa⟩ x hx.1

theorem Vt_le_Wt_symm {τ : S.O} (h : Vt S g t ≤ Wt S g τ) : Vt S g τ ≤ Wt S g t := by
  intro v hv
  rw [mem_Wt]
  intro u hu
  rw [polar_comm]
  exact mem_Wt.mp (h hu) v hv

theorem exists_conj_eq_mul_t (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {k : S.M}
    (hk : S.ρ k ∈ normalizer (S.Lbar g : Set S.O)) {τ : S.O}
    (hτ : τ = S.ρ k * t * (S.ρ k)⁻¹) (hτN : τ ∈ Nbar S g t) (hτt : τ ≠ t) :
    ∃ h ∈ Nbar S g t, h * τ * h⁻¹ = τ * t := by
  have Y := X.conj' hk hτ
  have := X.nqHyp hCE
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ y ∈ Nbar S g t, (y : S.O) * τ = τ * y := by
    intro y hy
    rcases eq_one_or_eq_t X (NQHyp.comm y hy τ hτN) with h | h
    · calc y * τ = (y * τ * y⁻¹ * τ⁻¹) * (τ * y) := by group
        _ = τ * y := by rw [h, one_mul]
    · exfalso
      apply hcon y hy
      calc y * τ * y⁻¹ = (y * τ * y⁻¹ * τ⁻¹) * τ := by group
        _ = τ * t := by rw [h, S4.Lbar_comm S X.haQ X.ht Y.ht]
  obtain ⟨x₁, hx₁, hx₁N⟩ := exists_mem_Abar_tau_not_mem hCE X Y hτN hτt
  have hline := Vt_inf_Vt_le_clSub hCE X Y hτN hτt
  obtain ⟨k', hk', hβ', hb'⟩ := X.exists_pair
  obtain ⟨hdec, -, -, -, hN⟩ := timmesfeld_10_1_two hCE X hk' hb'
  have hVτW := Vt_le_Wt_symm (Vt_le_Wt_of_mem_Nbar Y hτN)
  have hcτ := (commSpace_t_eq Y.H Y.C Y.ht Y.ht1 Y.hVQ).1
  have hbP : S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [← ρ_cl_conj_z S k' X.haQ, ← coe_orbV X.haQ X.ht hk',
      ← beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ, hβ']
    exact one_ne_zero
  have hBfix := clSub_inf_fixSub_Bbar X hk'
  have hsub : Vt S g τ ≤ (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t := by
    intro v hv
    have hvW := hVτW hv
    rw [← hdec] at hvW
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hvW
    by_cases hqV : q ∈ Vt S g t
    · exact add_mem (Submodule.mem_sup_left hp) (Submodule.mem_sup_right hqV)
    exfalso
    have hqfix : q ∉ fixSub S (S.Lbar ((k' : G) * g) ⊓ Nbar S g t) := fun h => hqV (by
      have : q ∈ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓
          fixSub S (S.Lbar ((k' : G) * g) ⊓ Nbar S g t) := ⟨hq.1, h⟩
      rw [hBfix] at this
      exact this.2)
    simp only [fixSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, not_forall] at hqfix
    obtain ⟨y, hy, hyq⟩ := hqfix
    have h1 := Lbar_apply_sub_mem_span' (conj_mem_QG' S k'.2 X.haQ) hq.1 hy.1
    have hqb : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q = S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) := by
      rcases mem_span_cl_iff.mp h1 with h | h
      · exact absurd (sub_eq_zero.mp h) hyq
      · exact h
    have hpP : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ S.clSub (S.QG ⊓ S.Qa g) :=
      sub_mem (Nbar_apply_mem_clSub X.haQ X.H.conj_ne (cl_a_mem_Vt X.ht) hy.2 hp.1) hp.1
    have hyv : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (p + q) - (p + q) ∈ Vt S g t ⊓ Vt S g τ := by
      refine ⟨hN y hy.2 _ (add_mem hp.2 hq.2), ?_⟩
      refine sub_mem ?_ hv
      rw [← hcτ] at hv ⊢
      obtain ⟨w, hw⟩ := mem_commSpace.mp hv
      rw [← hw]
      refine mem_commSpace.mpr ⟨(y : S.Qt ≃ₗ[ZMod 2] S.Qt) w, ?_⟩
      rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, hcomm y hy.2]
    have h2 := hline hyv
    have e : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (p + q) - (p + q) =
        ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) +
          S.cl ((k' : G) * g * S.z * ((k' : G) * g)⁻¹) := by
      rw [← hqb, map_add]
      abel
    rw [e] at h2
    apply hbP
    have := sub_mem h2 hpP
    rwa [add_sub_cancel_left] at this
  have hAτ : ∀ a ∈ S.Lbar g ⊓ Nbar S g t, a ∈ Nbar S g τ := by
    intro a ha
    by_contra haN
    have h1 := finrank_map_Vt_of_Lbar Y ha.1 haN
    have hle : (Vt S g τ).map (((a : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) ≤
        (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨p, hp, v₀, hv₀, rfl⟩ := Submodule.mem_sup.mp (hsub hv)
      have e : (((a : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) (p + v₀) =
          (a : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p := by
        simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_add,
          (mem_Nbar.mp ha.2).2 v₀ hv₀]
        abel
      rw [e]
      exact Lbar_apply_sub_mem_span' X.haQ hp.1 ha.1
    have h2 := Submodule.finrank_mono hle
    rw [h1, finrank_span_singleton (cl_conj_z_ne_zero S X.H.conj_mem X.H.conj_ne)] at h2
    omega
  have heq : S.Lbar g ⊓ Nbar S g t = S.Lbar g ⊓ Nbar S g τ :=
    Subgroup.eq_of_le_of_card_ge (fun a ha => ⟨ha.1, hAτ a ha⟩) (by rw [X.card_Abar, Y.card_Abar])
  exact hx₁N (by rw [← heq] at hx₁; exact hx₁.2)

end CFSG.LargeExtraspecial.S10
