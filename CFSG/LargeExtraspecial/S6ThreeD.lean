module

public import CFSG.LargeExtraspecial.S6ThreeC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem pairInt_of_inf_le (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ) {k k' : S.M}
    (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g))
    (hP : S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ≤
      Vt S g t) : PairInt S g t := by
  intro k₃ k₄ h3 h4 h34
  obtain ⟨j, hj, hj1, hj2⟩ := exists_mem_Rbar_pair H C ht ht1 hVQ hSp hk hk' h3 h4 hkk' h34
  have e1 : S.clSub (S.QG ⊓ S.Qa ((k₃ : G) * g)) =
      S.clSub (S.QG ⊓ S.Qa ((j : G) * ((k : G) * g))) :=
    clSub_eq_of_cl_eq (H.mul k₃).conj_mem (H.mul k₃).conj_ne
      (conj_mem_QG' S j.2 (H.mul k).conj_mem) hj1.symm
  have e2 : S.clSub (S.QG ⊓ S.Qa ((k₄ : G) * g)) =
      S.clSub (S.QG ⊓ S.Qa ((j : G) * ((k' : G) * g))) :=
    clSub_eq_of_cl_eq (H.mul k₄).conj_mem (H.mul k₄).conj_ne
      (conj_mem_QG' S j.2 (H.mul k').conj_mem) hj2.symm
  rw [e1, e2]
  intro v hv
  have hw : (((S.ρ j)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) :=
    ⟨(mem_clSub_Qa_mul_iff j).mp hv.1, (mem_clSub_Qa_mul_iff j).mp hv.2⟩
  have := apply_mem_Vt_of_mem_Rbar H.conj_mem hj (hP hw)
  rwa [apply_inv_apply_O] at this

theorem not_pairInt_sp (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) : ¬ PairInt S g t := by
  intro hPI
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hP := pairInt_ab hh hb hPI
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hN : ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
    intro x hx w hw
    rw [hN0] at hx
    exact apply_sub_mem_Vt_of_mem_N0bar H
      (fun k hk w hw => apply_sub_mem_Vt_a H C ht ht1 hVQ hh hb hP hk hw) hx hw
  have hc := isCompl_fixOf_wvRep H hNo C ht ht1 hVQ hh hb hPI hN hSp.eq_sp
  rw [hSp.LmodN_eq, LhmodN_eq_spPointRadical H C ht ht1 hVQ hSp hh] at hc
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  have hdvd := S2.sp_timmesfeld_2_1_b_dvd_sp (wvRep S g H t hN hSp.eq_sp)
    (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ) (m := m) (by omega)
    (by omega) (beta_aV_bV H C ht ht1 hVQ hh hb) hc
  have hwv := finrank_wv H ht1
  obtain ⟨r, hr⟩ := odd_width_sp hCE H hNo C ht ht1 hVQ hSp
  have h4m : 4 ∣ 2 ^ m := by
    obtain ⟨k, hk⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [hk, pow_add]
    exact Dvd.intro_left _ rfl
  obtain ⟨c, hc'⟩ := h4m.trans hdvd
  omega

theorem Vone_eq_sup_inf {t : S.O} (g₁ g₂ : G) :
    Vone S g t g₁ g₂ = Vt S g t ⊔ (S.clSub (S.QG ⊓ S.Qa g₁) ⊓ Vone S g t g₁ g₂) := by
  have hle : Vone S g t g₁ g₂ ≤ S.clSub (S.QG ⊓ S.Qa g₁) ⊔ Vt S g t := inf_le_left
  rw [← sup_inf_assoc_of_le _ (Vt_le_Vone _ _), sup_comm, inf_eq_right.mpr hle]

section Base

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {k : S.M} (hk : S.ρ k ∈ Rbar S g t)
include H C ht ht1 hVQ hk

theorem finrank_clSub_inf_Vone (g₂ : G) :
    finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vone S g t ((k : G) * g) g₂) + 1 =
      finrank (ZMod 2) (Vone S g t ((k : G) * g) g₂) := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have h2 := finrank_clSub_inf_Vt (H.mul k) (C.mul k) htk ht1 (not_V_le_Qa_mul H hVQ hk)
  rw [Vt_mul] at h2
  have hmod := Vone_eq_sup_inf (g := g) (t := t) ((k : G) * g) g₂
  set P := S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) with hP
  set X := Vone S g t ((k : G) * g) g₂ with hX
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t) (P ⊓ X)
  rw [← hmod] at h1
  have e : Vt S g t ⊓ (P ⊓ X) = P ⊓ Vt S g t := by
    rw [inf_comm P X, ← inf_assoc, inf_eq_left.mpr (Vt_le_Vone _ _), inf_comm]
  rw [e] at h1
  omega

end Base

theorem not_mem_Qa_symm {g₁ g₂ : G} (h : g₂ * S.z * g₂⁻¹ ∉ S.Qa g₁) :
    g₁ * S.z * g₁⁻¹ ∉ S.Qa g₂ := by
  intro hmem
  have hne : g₂ * S.z * g₂⁻¹ ≠ g₁ * S.z * g₁⁻¹ := fun e => h (e ▸ S.conj_z_mem_Qa _)
  exact h (S.mem_Qa_symm hne.symm hmem)

theorem exists_common_partner (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hSp : SpCase H C ht ht1 hVQ) {k k'' : S.M}
    (hk : S.ρ k ∈ Rbar S g t) (hk'' : S.ρ k'' ∈ Rbar S g t) :
    ∃ j : S.M, S.ρ j ∈ Rbar S g t ∧
      (j : G) * g * S.z * ((j : G) * g)⁻¹ ∉ S.Qa ((k : G) * g) ∧
      (j : G) * g * S.z * ((j : G) * g)⁻¹ ∉ S.Qa ((k'' : G) * g) := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk'' := mem_Lbar_mul_of_mem_Rbar H ht hk''
  obtain ⟨w, hw1, hw2⟩ := exists_apply_eq_one_both (beta_nondegenerate H C ht ht1 hVQ)
    (bV_ne_zero H htk) (bV_ne_zero H htk'')
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw1
    exact zero_ne_one hw1
  obtain ⟨x, hx, hxw⟩ := hSp.transitive w hw0
  rw [← range_resV H.conj_mem t] at hx
  obtain ⟨⟨r, hr⟩, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  have hjQ := conj_mem_QG' S j.2 H.conj_mem
  have hw : (w : S.Qt) = S.cl ((j : G) * g * S.z * ((j : G) * g)⁻¹) := by
    rw [← hxw, coe_resV_apply]
    exact ρ_cl_conj_z S j H.conj_mem
  have key : ∀ {k₀ : S.M} (hk₀ : S.ρ k₀ ∈ Rbar S g t)
      (htk₀ : t ∈ S.Lbar ((k₀ : G) * g)), beta H C ht ht1 hVQ (bV htk₀) w = 1 →
      (j : G) * g * S.z * ((j : G) * g)⁻¹ ∉ S.Qa ((k₀ : G) * g) := by
    intro k₀ hk₀ htk₀ h1 hmem
    have hwP : (w : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa ((k₀ : G) * g)) := by
      rw [hw]
      exact S.cl_mem_clSub (Subgroup.mem_inf.mpr ⟨hjQ, hmem⟩) hjQ
    rw [(beta_bV_eq_zero_iff H C ht ht1 hVQ hk₀ htk₀ w).mpr hwP] at h1
    exact zero_ne_one h1
  exact ⟨j, hr, key hk htk hw1, key hk'' htk'' hw2⟩

section Sp

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ)
include hCE H hNo C ht ht1 hVQ hSp

section Pair

variable {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
  (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g))
include hk hk' hkk'

theorem Vone_ne_Vt : Vone S g t ((k : G) * g) ((k' : G) * g) ≠ Vt S g t := fun he =>
  not_pairInt_sp hCE H hNo C ht ht1 hVQ hSp
    (pairInt_of_inf_le H C ht ht1 hVQ hSp hk hk' hkk' ((inf_le_Vone _ _).trans he.le))

theorem finrank_Vone_eq :
    finrank (ZMod 2) (Vone S g t ((k : G) * g) ((k' : G) * g)) =
      finrank (ZMod 2) (Vt S g t) + 1 := by
  have h1 := finrank_Vone_le H C ht ht1 hVQ hSp hk hk' hkk'
  have h2 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (Vt_le_Vone (t := t) _ _)
    (Vone_ne_Vt hCE H hNo C ht ht1 hVQ hSp hk hk' hkk').symm)
  omega

theorem clSub_inf_Vone_eq :
    S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Vone S g t ((k : G) * g) ((k' : G) * g) =
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ fixSub S (S.Lbar ((k : G) * g) ⊓ Nbar S g t) := by
  have hle := Vone_inf_le_fixSub H C ht ht1 hVQ hk hk' hkk'
  have d1 := finrank_fixSub_sp H C ht ht1 hVQ hSp hk
  have d2 := finrank_clSub_inf_Vone H C ht ht1 hVQ hk ((k' : G) * g)
  have d3 := finrank_Vone_eq hCE H hNo C ht ht1 hVQ hSp hk hk' hkk'
  refine Submodule.eq_of_le_of_finrank_le (by rw [inf_comm]; exact hle) ?_
  omega

theorem Vone_eq_fix :
    Vone S g t ((k : G) * g) ((k' : G) * g) =
      Vt S g t ⊔ (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓
        fixSub S (S.Lbar ((k : G) * g) ⊓ Nbar S g t)) := by
  rw [← clSub_inf_Vone_eq hCE H hNo C ht ht1 hVQ hSp hk hk' hkk']
  exact Vone_eq_sup_inf _ _

theorem Vone_eq_fix' :
    Vone S g t ((k : G) * g) ((k' : G) * g) =
      Vt S g t ⊔ (S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓
        fixSub S (S.Lbar ((k' : G) * g) ⊓ Nbar S g t)) := by
  rw [Vone_comm]
  exact Vone_eq_fix hCE H hNo C ht ht1 hVQ hSp hk' hk (not_mem_Qa_symm hkk')

end Pair

omit hCE hNo in
theorem fix_eq_fix (hCE : CentralExtInput.{u}) (hNo : NoA2 S g) {k k'' : S.M}
    (hk : S.ρ k ∈ Rbar S g t) (hk'' : S.ρ k'' ∈ Rbar S g t) :
    Vt S g t ⊔ (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓
        fixSub S (S.Lbar ((k : G) * g) ⊓ Nbar S g t)) =
      Vt S g t ⊔ (S.clSub (S.QG ⊓ S.Qa ((k'' : G) * g)) ⊓
        fixSub S (S.Lbar ((k'' : G) * g) ⊓ Nbar S g t)) := by
  obtain ⟨j, hj, hjk, hjk''⟩ := exists_common_partner H C ht ht1 hVQ hSp hk hk''
  rw [← Vone_eq_fix hCE H hNo C ht ht1 hVQ hSp hk hj hjk,
    Vone_eq_fix' hCE H hNo C ht ht1 hVQ hSp hk hj hjk,
    ← Vone_eq_fix' hCE H hNo C ht ht1 hVQ hSp hk'' hj hjk'',
    Vone_eq_fix hCE H hNo C ht ht1 hVQ hSp hk'' hj hjk'']

theorem Vone_eq_Vone {k₁ k₂ k₃ k₄ : S.M} (h1 : S.ρ k₁ ∈ Rbar S g t)
    (h2 : S.ρ k₂ ∈ Rbar S g t) (h3 : S.ρ k₃ ∈ Rbar S g t) (h4 : S.ρ k₄ ∈ Rbar S g t)
    (h12 : (k₂ : G) * g * S.z * ((k₂ : G) * g)⁻¹ ∉ S.Qa ((k₁ : G) * g))
    (h34 : (k₄ : G) * g * S.z * ((k₄ : G) * g)⁻¹ ∉ S.Qa ((k₃ : G) * g)) :
    Vone S g t ((k₁ : G) * g) ((k₂ : G) * g) = Vone S g t ((k₃ : G) * g) ((k₄ : G) * g) := by
  rw [Vone_eq_fix hCE H hNo C ht ht1 hVQ hSp h1 h2 h12,
    Vone_eq_fix hCE H hNo C ht ht1 hVQ hSp h3 h4 h34]
  exact fix_eq_fix H C ht ht1 hVQ hSp hCE hNo h1 h3

theorem apply_mem_Vone {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
    (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) {x : S.O} (hx : x ∈ Rbar S g t)
    {v : S.Qt} (hv : v ∈ Vone S g t g ((h : G) * g)) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vone S g t g ((h : G) * g) := by
  obtain ⟨j, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hx)
  have h1 := pair_one (t := t) hb
  have hm : ((S.ρ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈
      (Vone S g t g ((h : G) * g)).map ((S.ρ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap :=
    Submodule.mem_map_of_mem hv
  rw [map_Vone H hx] at hm
  have hcoe : (j : G) * ((h : G) * g) = ((j * h : S.M) : G) * g := by simp [mul_assoc]
  have hjh : S.ρ (j * h) ∈ Rbar S g t := by rw [map_mul]; exact mul_mem hx hh
  have hjb : ((j * h : S.M) : G) * g * S.z * (((j * h : S.M) : G) * g)⁻¹ ∉
      S.Qa ((j : G) * g) := by
    rw [mem_Qa_mul_iff]
    simpa [mul_assoc] using hb
  rw [hcoe, Vone_eq_Vone hCE H hNo C ht ht1 hVQ hSp hx hjh h1.1 hh hjb h1.2] at hm
  simpa using hm

end Sp

end CFSG.LargeExtraspecial.S6
