module

public import CFSG.LargeExtraspecial.S10Basic
public import CFSG.LargeExtraspecial.S4SevenB3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem timmesfeld_10_1_two (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) :
    (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ (S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) =
      Wt S g t ∧
    ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t) ⊓
      ((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) = Vt S g t ∧
    finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t) ⊔ Vt S g t) = S.width ∧
    finrank (ZMod 2) ↥((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Wt S g t) ⊔ Vt S g t) =
      S.width ∧
    ∀ x ∈ Nbar S g t, ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  have hP := clSub_inf_clSub_le_Vt X.H X.C X.ht X.ht1 X.hVQ hh hb
    (radBound_of_omegaCase X.H X.C X.ht X.ht1 X.hVQ X.hΩ)
  have hth := mem_Lbar_of_pair X.H X.ht hh
  have d2 := finrank_sup_Vt (X.H.mul h) (X.C.mul h) hth X.ht1 (not_V_le_Qa_mul X.H X.hVQ hh)
  rw [Wt_mul, Vt_mul] at d2
  exact ⟨sup_eq_Wt X.H X.C X.ht X.ht1 X.hVQ hh hb hP,
    sup_Vt_inf_sup_Vt X.H X.C X.ht X.ht1 X.hVQ hh hb hP,
    finrank_sup_Vt X.H X.C X.ht X.ht1 X.hVQ, d2,
    fun x hx w hw => timmesfeld_6_1_one X.H X.C X.ht X.ht1 X.hVQ hh hb hCE X.hNo X.hΩ hx hw⟩

theorem Hyp10.exists_pair (X : Hyp10 S g t) : ∃ k : S.M, ∃ hk : S.ρ k ∈ Rbar S g t,
    beta X.H X.C X.ht X.ht1 X.hVQ (aV X.ht) (orbV X.haQ X.ht hk) = 1 ∧
      (k : G) * g * S.z * ((k : G) * g)⁻¹ ∉ S.Qa g := by
  obtain ⟨k, hk, hβ⟩ := exists_mem_Rbar_beta_eq_one X.H X.C X.ht X.ht1 X.hVQ
  refine ⟨k, hk, hβ, fun hbQa => ?_⟩
  have hbQ := conj_mem_QG' S k.2 X.haQ
  have hmem : (orbV X.haQ X.ht hk : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [coe_orbV, ρ_cl_conj_z S k X.haQ]
    exact S.cl_mem_clSub ⟨hbQ, hbQa⟩ hbQ
  rw [← beta_aV_eq_zero_iff X.H X.C X.ht X.ht1 X.hVQ] at hmem
  rw [hmem] at hβ
  exact zero_ne_one hβ

@[expose] noncomputable def fixModV (X : Hyp10 S g t) (x : S.Qt) : Subgroup S.O where
  carrier := {r | r ∈ Rbar S g t ∧ (r : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t}
  mul_mem' := by
    rintro r s ⟨hr, hrx⟩ ⟨hs, hsx⟩
    refine ⟨mul_mem hr hs, ?_⟩
    have e : ((r * s : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x =
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) +
          ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, map_sub]
      abel
    rw [e]
    exact add_mem (apply_mem_Vt_of_mem_Rbar X.haQ hr hsx) hrx
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' := by
    rintro r ⟨hr, hrx⟩
    refine ⟨inv_mem hr, ?_⟩
    have e : ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x =
        -((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) := by
      rw [map_sub, inv_apply_apply_O]
      abel
    rw [e]
    exact neg_mem (apply_mem_Vt_of_mem_Rbar X.haQ (inv_mem hr) hrx)

theorem mem_Vt_of_fix_Wstar (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {w : S.Qt}
    (hw : w ∈ Wt S g t)
    (hfix : ∀ r ∈ Rbar S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) :
    w ∈ Vt S g t := by
  obtain ⟨k, hk, hβ, hb⟩ := X.exists_pair
  obtain ⟨hdec, hint, -, -, -⟩ := timmesfeld_10_1_two hCE X hk hb
  have hR := (timmesfeld_4_7_b hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ (Or.inr X.hΩ) hk hβ).1
  have htk := mem_Lbar_mul_of_mem_Rbar X.H X.ht hk
  set Pa := S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t with hPa
  set Pb := S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t with hPb
  rw [← hdec] at hw
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
  have hspan_a : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt X.ht)
  have hspan_b : (ZMod 2) ∙ S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≤ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_mem_Vt htk)
  have hpa : ∀ l ∈ S.Lbar g, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ Vt S g t := fun l hl =>
    hspan_a (Lbar_apply_sub_mem_span' X.haQ hp.1 hl)
  have hqb : ∀ l ∈ S.Lbar ((k : G) * g), (l : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ Vt S g t :=
    fun l hl => hspan_b (Lbar_apply_sub_mem_span' (conj_mem_QG' S k.2 X.haQ) hq.1 hl)
  have hsplit : ∀ r ∈ Rbar S g t,
      ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) + ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q) ∈ Vt S g t :=
    fun r hr => by
      have := hfix r hr
      rwa [map_add, show (r : S.Qt ≃ₗ[ZMod 2] S.Qt) p + (r : S.Qt ≃ₗ[ZMod 2] S.Qt) q -
        (p + q) = ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) +
          ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q) by abel] at this
  have hqR : Rbar S g t ≤ fixModV X q := by
    rw [hR]
    refine sup_le (fun l hl => ⟨Lbar_le_Rbar X.ht hl, ?_⟩) (fun l hl => ⟨?_, hqb l hl⟩)
    · have h1 := hsplit l (Lbar_le_Rbar X.ht hl)
      have h2 := hpa l hl
      have := sub_mem h1 h2
      rwa [add_sub_cancel_left] at this
    · exact Lbar_mul_le_Rbar htk hl
  have hpR : Rbar S g t ≤ fixModV X p := by
    rw [hR]
    refine sup_le (fun l hl => ⟨Lbar_le_Rbar X.ht hl, hpa l hl⟩) (fun l hl => ⟨?_, ?_⟩)
    · exact Lbar_mul_le_Rbar htk hl
    · have h1 := hsplit l (Lbar_mul_le_Rbar htk hl)
      have h2 := hqb l hl
      have := sub_mem h1 h2
      rwa [add_sub_cancel_right] at this
  have hq' : q ∈ Pa ⊔ Vt S g t := by
    have hkinv : (S.ρ k)⁻¹ ∈ Rbar S g t := inv_mem hk
    have h1 := (hqR hkinv).2
    have h2 : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) q ∈ Pa :=
      ⟨(mem_clSub_Qa_mul_iff k).mp hq.1, apply_mem_Wt X.H hkinv hq.2⟩
    have e : q = (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) q -
        ((((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q) := by abel
    rw [e]
    exact sub_mem (Submodule.mem_sup_left h2) (Submodule.mem_sup_right h1)
  have hp' : p ∈ Pb ⊔ Vt S g t := by
    have h1 := (hpR hk).2
    have h2 : ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ Pb :=
      ⟨apply_mem_clSub_Qa_mul k hp.1, apply_mem_Wt X.H hk hp.2⟩
    have e : p = ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p -
        (((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) := by abel
    rw [e]
    exact sub_mem (Submodule.mem_sup_left h2) (Submodule.mem_sup_right h1)
  have hqV : q ∈ Vt S g t := by
    rw [← hint]
    exact ⟨hq', Submodule.mem_sup_left hq⟩
  have hpV : p ∈ Vt S g t := by
    rw [← hint]
    exact ⟨Submodule.mem_sup_left hp, hp'⟩
  exact add_mem hpV hqV

end CFSG.LargeExtraspecial.S10
