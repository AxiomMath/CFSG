module

public import CFSG.LargeExtraspecial.S11Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

theorem Conf.Vt_le_clSub {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u) :
    Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa k) :=
  (Vt_le_Tt hy.hyp4 hy.noA2' K.ne_one K.lin).trans
    (Tt_le_clSub hy.hyp4 hy.cons K.lin (K.QG_inf_Qa_le_V hy hk))

theorem Conf.clSub_le_Wt {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u) :
    S.clSub (S.QG ⊓ S.Qa k) ≤ Wt S g t := fun _ hp => mem_Wt.mpr fun _ hv =>
  polar_eq_zero_of_mem_clSub (K.base_of_mem hk).1 (K.Vt_le_clSub hy hk hv) hp

theorem Conf.exists_sub_eq_cl {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u) :
    ∃ p ∈ S.clSub (S.QG ⊓ S.Qa k),
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p = S.cl (k * S.z * k⁻¹) := by
  obtain ⟨hkz, htk⟩ := K.base_of_mem hk
  have hyk := hy.of_conj hk.1 hkz
  by_contra h
  push Not at h
  apply K.ne_one
  refine hyk.cons.faithful t htk fun v hv => ?_
  rcases mem_span_cl_iff.mp (Lbar_apply_sub_mem_span' hk.1 hv htk) with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 (h v hv)

variable (hCE : CentralExtInput.{u_G})
include hCE

theorem Conf.mem_Wt_of_sub_mem_Vt {w : S.Qt}
    (hw : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) : w ∈ Wt S g t := by
  rw [← K.timmesfeld_11_7 hy hCE] at hw
  obtain ⟨w', hw', he⟩ := mem_Tt.mp hw
  have h1 : w - w' ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [mem_fixSpace, map_sub, sub_eq_sub_iff_sub_eq_sub]
    exact he.symm
  have := add_mem (fixSpace_le_Wt hy.hyp4 K.mem_Lbar K.ne_one h1) hw'
  rwa [sub_add_cancel] at this

theorem Conf.Wt_le {W : Submodule (ZMod 2) S.Qt}
    (hfix : fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ W)
    (hP : ∀ k : G, k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u → S.clSub (S.QG ⊓ S.Qa k) ≤ W) :
    Wt S g t ≤ W := by
  intro w hw
  have h1 : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ S.clSub (S.QG ⊓ S.Qa u) := by
    rw [K.timmesfeld_11_3 hy, ← K.timmesfeld_11_7 hy hCE]
    exact sub_mem_Tt hw
  obtain ⟨e, he, -, hee⟩ := S.mem_clSub_iff.mp h1
  by_cases he1 : e = 1
  · subst he1
    rw [S.cl_one] at hee
    exact hfix (mem_fixSpace.mpr (sub_eq_zero.mp hee.symm))
  · obtain ⟨k, hk⟩ := K.exists_conj hy he he1
    have hkE : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u := hk ▸ he
    obtain ⟨p, hp, hpe⟩ := K.exists_sub_eq_cl hy hkE
    have h2 : w - p ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [mem_fixSpace, map_sub, sub_eq_sub_iff_sub_eq_sub, hpe, hk, hee]
    have := add_mem (hfix h2) (hP k hkE hp)
    rwa [sub_add_cancel] at this

variable (hn : 6 ≤ S.width)
include hn

theorem Conf.fixSpace_eq :
    fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) := by
  refine le_antisymm (fun w hw => ?_) K.clSub_centralizer_le_fixSpace
  obtain ⟨c, hc, rfl⟩ := S.exists_cl w
  have h1 : S.cl ((τ : G) * c * (τ : G)⁻¹) = S.cl c := by
    rw [← S.ρ_cl τ hc, K.rho_eq]
    exact mem_fixSpace.mp hw
  rcases (S.cl_eq_cl_iff hc (S.conj_mem_QG τ.2 hc)).mp h1.symm with h2 | h2
  · refine S.cl_mem_clSub (mem_inf.mpr ⟨hc, mem_centralizer_singleton_iff.mpr ?_⟩) hc
    calc c * τ = (τ : G) * c * (τ : G)⁻¹ * τ := by rw [h2]
      _ = τ * c := by group
  · exfalso
    refine K.timmesfeld_11_6_of_mem_QG hy hCE hn (S.QG.inv_mem hc) ?_
    calc c⁻¹ * τ * c⁻¹⁻¹ = c⁻¹ * ((τ : G) * c * (τ : G)⁻¹) * τ := by group
      _ = c⁻¹ * (c * S.z) * τ := by rw [h2]
      _ = S.z * τ := by group
      _ = τ * S.z := (S.z_comm τ.2).symm

theorem Conf.apply_sub_mem_Vt_of_mem_fixSpace {x : S.O} (hx : x ∈ Nbar S g t) {w : S.Qt}
    (hw : w ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  rw [K.fixSpace_eq hy hCE hn] at hw
  obtain ⟨c, hcX, hcQ, rfl⟩ := S.mem_clSub_iff.mp hw
  obtain ⟨x0, hx0, rfl⟩ := (S4.mem_Lbar S).mp (K.timmesfeld_11_5 hy hCE hx)
  have hx0u : (x0 : G) ∈ S.Qa u := (mem_inf.mp hx0).1
  have hcτ : c * (u * S.z * u⁻¹) = u * S.z * u⁻¹ * c := by
    rw [← K.conj_eq]
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp hcX).2
  have h1 := S.cl_commutator x0.2 hcQ
  rw [← h1, ← K.timmesfeld_11_3 hy]
  refine S.cl_mem_clSub (mem_inf.mpr ⟨?_, ?_⟩) ?_
  · exact S.QG.mul_mem (S.conj_mem_QG x0.2 hcQ) (S.QG.inv_mem hcQ)
  · rw [show (x0 : G) * c * (x0 : G)⁻¹ * c⁻¹ = x0 * (c * (x0 : G)⁻¹ * c⁻¹) by group]
    exact mul_mem hx0u (conj_mem_Qa_of_commute' (inv_mem hx0u) hcτ)
  · exact S.QG.mul_mem (S.conj_mem_QG x0.2 hcQ) (S.QG.inv_mem hcQ)

theorem Conf.apply_sub_mem_Vt_of_forall {x : S.O} (hx : x ∈ Nbar S g t)
    (hxL : ∀ k : G, k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u → x ∈ S.Lbar k) {w : S.Qt}
    (hw : w ∈ Wt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  set W := (Vt S g t).comap (((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) with hW
  have hmem : ∀ v, v ∈ W ↔ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t := fun v => by
    rw [hW, Submodule.mem_comap, LinearMap.sub_apply]
    rfl
  refine (hmem w).mp (K.Wt_le hy hCE (fun v hv => (hmem v).mpr ?_) (fun k hk v hv => ?_) hw)
  · exact K.apply_sub_mem_Vt_of_mem_fixSpace hy hCE hn hx hv
  · refine (hmem v).mpr ?_
    have h1 := Lbar_apply_sub_mem_span' hk.1 hv (hxL k hk)
    refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_ h1
    rw [← K.timmesfeld_11_3 hy]
    exact S.cl_mem_clSub hk hk.1

omit hn hCE in
theorem Conf.exists_apply_sub_eq {x : S.O} {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa u)
    (hxc : ∀ ℓ ∈ S.Lbar k ⊓ Nbar S g t, ℓ * x = x * ℓ) {p : S.Qt}
    (hp : p ∈ S.clSub (S.QG ⊓ S.Qa k))
    (hxp : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ S.clSub (S.QG ⊓ S.Qa k))
    (hxV : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∉ Vt S g t) :
    ∃ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = S.cl (k * S.z * k⁻¹) := by
  obtain ⟨hkz, htk⟩ := K.base_of_mem hk
  have hyk := hy.of_conj hk.1 hkz
  set P := S.clSub (S.QG ⊓ S.Qa k) with hP
  set X := S.Lbar k ⊓ Nbar S g t with hX
  set σ := (x : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p with hσ
  have h1 : Nat.card X * 2 ^ finrank (ZMod 2) ↥(P ⊓ fixSub S X) = 2 ^ S.width :=
    card_mul_two_pow_finrank_fix hyk.hyp4 hyk.cons inf_le_left
  have h2 := card_Lbar_inf_Nbar hyk.hyp4 hyk.cons (K.linCase_of hy hk htk)
  rw [hy.Nbar_eq hk.1 hkz t, hy.Vt_eq hk.1 hkz t] at h2
  have hVP : Vt S g t ≤ P ⊓ fixSub S X := fun v hv =>
    ⟨K.Vt_le_clSub hy hk hv, fun ℓ hℓ => (mem_Nbar.mp hℓ.2).2 v hv⟩
  have hm := K.lin.two_le_finrank
  have hw := hy.hyp4.two_lt_width
  have h3 := Submodule.finrank_mono hVP
  have hd : finrank (ZMod 2) ↥(P ⊓ fixSub S X) = finrank (ZMod 2) (Vt S g t) := by
    have h4 : Nat.card X * 2 ^ (finrank (ZMod 2) ↥(P ⊓ fixSub S X) + (S.width - 1)) =
        Nat.card X * 2 ^ (finrank (ZMod 2) (Vt S g t) - 1 + S.width) := by
      rw [pow_add, pow_add, ← mul_assoc, ← mul_assoc, h1, h2, ← pow_add, ← pow_add]
      congr 1
      omega
    have h5 := Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left Nat.card_pos h4)
    omega
  have heq : P ⊓ fixSub S X = Vt S g t :=
    (Submodule.eq_of_le_of_finrank_eq hVP hd.symm).symm
  have hσfix : σ ∉ fixSub S X := fun h => hxV (heq ▸ ⟨hxp, h⟩)
  rw [mem_fixSub] at hσfix
  push Not at hσfix
  obtain ⟨ℓ, hℓ, hℓσ⟩ := hσfix
  rcases mem_span_cl_iff.mp (Lbar_apply_sub_mem_span' hk.1 hxp hℓ.1) with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hℓσ
  · have hpW : p ∈ Wt S g t := K.clSub_le_Wt hy hk hp
    refine ⟨(ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p,
      sub_mem (apply_mem_Wt hy.hyp4 (Nbar_le_Rbar hℓ.2) hpW) hpW, ?_⟩
    have hc : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) p) =
        (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) p) := by
      rw [← coe_mul_apply, ← coe_mul_apply, hxc ℓ hℓ]
    rw [← h0, hσ, map_sub, map_sub, hc]
    abel

end CFSG.LargeExtraspecial.S11
