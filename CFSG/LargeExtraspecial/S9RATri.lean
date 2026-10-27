module

public import CFSG.LargeExtraspecial.S9IIb
public import CFSG.LargeExtraspecial.S9RAY
public import CFSG.LargeExtraspecial.S9RALin
public import CFSG.LargeExtraspecial.S2Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem comm_mem_Nbar_of_fix (haQ : g * S.z * g⁻¹ ∈ S.QG) {t σ : S.O} (hσM : σ ∈ S.Mbar)
    (hσt : σ * t = t * σ) (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {r : S.O}
    (hr : r ∈ Rbar S g t) : σ * r * σ⁻¹ * r⁻¹ ∈ Nbar S g t := by
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hσM
  have hσR : σ * r * σ⁻¹ ∈ Rbar S g t := by
    have := conj_mem_Rbar (k := k) (by rw [hk]; exact hσt) hr
    rwa [hk] at this
  refine mem_Nbar.mpr ⟨mul_mem hσR (inv_mem hr), fun v hv => ?_⟩
  have hv' := apply_mem_Vt_of_mem_Rbar haQ (inv_mem hr) hv
  have hσinv : ((σ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    conv_lhs => rw [← hσV _ hv']
    exact inv_apply_apply_O σ _
  rw [coe_mul_apply, coe_mul_apply, coe_mul_apply, hσinv, apply_inv_apply_O, hσV v hv]

section Tri

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem CMt_apply_mem_Vone : ∀ x ∈ S8.CMt S t, ∀ v ∈ Vone S g t g ((h : G) * g),
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vone S g t g ((h : G) * g) := fun _ hx _ hv =>
  apply_mem_Vone_of_commute hCE H hNo C ht ht1 hVQ hSp hh hb (S8.mem_CMt.mp hx).1
    (S8.mem_CMt.mp hx).2 hv

theorem CMt_apply_mem_Wone : ∀ x ∈ S8.CMt S t, ∀ w ∈ Wone S g t g ((h : G) * g),
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wone S g t g ((h : G) * g) := fun _ hx _ hw =>
  apply_mem_Wone_of_commute hCE H hNo C ht ht1 hVQ hSp hh hb (S8.mem_CMt.mp hx).1
    (S8.mem_CMt.mp hx).2 hw

theorem secHomK_comm_rho
    (ρ : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) →*
      (↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ) ≃ₗ[ZMod 2]
        ↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ)))
    (hρ : ∀ (e : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)) (x : Rbar S g t),
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t x →
      ∀ w (hw : w ∈ Wone S g t g ((h : G) * g)),
        ((ρ e (secMk (Vone S g t g ((h : G) * g)) hw) :
          ↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ)) :
            S.Qt ⧸ Vone S g t g ((h : G) * g)) =
          (Vone S g t g ((h : G) * g)).mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w))
    (hX : ∀ x ∈ S8.CMt S t, ∀ v ∈ Vone S g t g ((h : G) * g),
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vone S g t g ((h : G) * g))
    (hW : ∀ x ∈ S8.CMt S t, ∀ w ∈ Wone S g t g ((h : G) * g),
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wone S g t g ((h : G) * g))
    (σ : S8.CMt S t) (hσV : ∀ v ∈ Vt S g t, ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (e : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ))
    (m : ↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ)) :
    secHomK _ _ _ hX hW σ (ρ e m) = ρ e (secHomK _ _ _ hX hW σ m) := by
  have haQ := H.conj_mem
  obtain ⟨w, hw, hm⟩ := exists_secMk (Vone S g t g ((h : G) * g)) m
  rw [hm]
  have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
    rw [hSp.eq_sp]
    exact e.2
  rw [← range_resV haQ t] at heR
  obtain ⟨r, hr⟩ := heR
  have hRW : ∀ (y : Rbar S g t) (v : S.Qt), v ∈ Wone S g t g ((h : G) * g) →
      ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Wone S g t g ((h : G) * g) :=
    fun y v hv => apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb y.2 hv
  have hσW := hW σ σ.2 w hw
  have h1 : ρ e (secMk _ hw) = secMk _ (hRW r w hw) :=
    Subtype.ext (by rw [hρ e r hr.symm w hw, coe_secMk])
  have h2 : ρ e (secMk _ hσW) = secMk _ (hRW r _ hσW) :=
    Subtype.ext (by rw [hρ e r hr.symm _ hσW, coe_secMk])
  rw [h1, secHomK_secMk, secHomK_secMk, h2]
  apply Subtype.ext
  rw [coe_secMk, coe_secMk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  obtain ⟨hσM, hσt⟩ := S8.mem_CMt.mp σ.2
  have hn := comm_mem_Nbar_of_fix haQ hσM hσt hσV r.2
  have h3 := Nbar_apply_sub_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hn (hRW r _ hσW)
  have e1 : ((((σ : S.O) * r * (σ : S.O)⁻¹ * (r : S.O)⁻¹ : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) =
      ((σ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
    rw [coe_mul_apply, coe_mul_apply, coe_mul_apply, inv_apply_apply_O, inv_apply_apply_O]
  rw [e1] at h3
  exact h3

theorem finrank_commSpace_secHomK_typeII
    (ρ : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) →*
      (↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ) ≃ₗ[ZMod 2]
        ↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ)))
    (hρ : ∀ (e : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)) (x : Rbar S g t),
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t x →
      ∀ w (hw : w ∈ Wone S g t g ((h : G) * g)),
        ((ρ e (secMk (Vone S g t g ((h : G) * g)) hw) :
          ↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ)) :
            S.Qt ⧸ Vone S g t g ((h : G) * g)) =
          (Vone S g t g ((h : G) * g)).mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w))
    (hD : S2.SpRadDecomp ρ ⊥ ⊤ (aV ht) (bV (mem_Lbar_of_pair H ht hh)))
    (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    (hX : ∀ x ∈ S8.CMt S t, ∀ v ∈ Vone S g t g ((h : G) * g),
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vone S g t g ((h : G) * g))
    (hW : ∀ x ∈ S8.CMt S t, ∀ w ∈ Wone S g t g ((h : G) * g),
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ Wone S g t g ((h : G) * g))
    {x : S.O} (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t)
    (hτK : x * t * x⁻¹ ∈ S8.CMt S t) :
    finrank (ZMod 2) (commSpace (secHomK _ _ _ hX hW ⟨x * t * x⁻¹, hτK⟩)) = 4 := by
  have hτM : x * t * x⁻¹ ∈ S.Mbar := (S8.mem_CMt.mp hτK).1
  have hinf := inf_commSpace_eq_bot H C ht ht1 hVQ hSp.transitive hL hxM hβ
  have hτV := fix_Vt_of_inf_eq_bot H hτM hτt hinf
  have hg := secHomK_comm_rho hCE H hNo C ht ht1 hVQ hSp hh hb ρ hρ hX hW ⟨_, hτK⟩ hτV
  have hUinv := commSpace_invariant ρ (u := secHomK _ _ _ hX hW ⟨x * t * x⁻¹, hτK⟩) hg
  have hdvd := pow_dvd_finrank_of_invariant ρ (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) (m := 2) (by norm_num) (by rw [h4])
    (beta_aV_bV H C ht ht1 hVQ hh hb) hD hUinv
  have hle := finrank_commSpace_secHomK_le hX hW (⟨x * t * x⁻¹, hτK⟩ : S8.CMt S t)
  have hτdim : finrank (ZMod 2) (commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      4 := by
    rw [S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1, LinearEquiv.finrank_map_eq, h4]
  have hne : commSpace (secHomK _ _ _ hX hW ⟨x * t * x⁻¹, hτK⟩) ≠ ⊥ := fun hbot =>
    not_forall_apply_sub_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hL hxM hτt hβ
      fun w hw => apply_sub_mem_of_commSpace_eq_bot hX hW ⟨_, hτK⟩ hbot hw
  have hpos : 0 < finrank (ZMod 2) (commSpace (secHomK _ _ _ hX hW ⟨x * t * x⁻¹, hτK⟩)) :=
    Nat.pos_of_ne_zero fun h0 => hne (Submodule.finrank_eq_zero.mp h0)
  obtain ⟨k, hk⟩ := hdvd
  simp only [Subtype.coe_mk] at hle
  omega

theorem false_of_triple (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x₁ x₂ x₃ : S.O} (hx₁ : x₁ ∈ S.Mbar) (hx₂ : x₂ ∈ S.Mbar) (hx₃ : x₃ ∈ S.Mbar)
    (h₁ : x₁ * t * x₁⁻¹ * t = t * (x₁ * t * x₁⁻¹))
    (h₂ : x₂ * t * x₂⁻¹ * t = t * (x₂ * t * x₂⁻¹))
    (h₃ : x₃ * t * x₃⁻¹ * t = t * (x₃ * t * x₃⁻¹))
    (hβ₁ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x₁ * t * x₁⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t)
    (hβ₂ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x₂ * t * x₂⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t)
    (hβ₃ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x₃ * t * x₃⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t)
    (h₁₂ : x₁ * t * x₁⁻¹ * (x₂ * t * x₂⁻¹) = x₂ * t * x₂⁻¹ * (x₁ * t * x₁⁻¹))
    (h₁₂₃ : ∀ w ∈ Wone S g t g ((h : G) * g), ((x₃ * t * x₃⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w -
      ((x₁ * t * x₁⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((x₂ * t * x₂⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ Vone S g t g ((h : G) * g)) :
    False := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_3_three hCE H hNo C ht ht1 hVQ hSp hh hb
  have hX := CMt_apply_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb
  have hW := CMt_apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb
  have hτK : ∀ {x : S.O}, x ∈ S.Mbar → x * t * x⁻¹ * t = t * (x * t * x⁻¹) →
      x * t * x⁻¹ ∈ S8.CMt S t := fun hxM hxt => S8.mem_CMt.mpr
    ⟨S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM), hxt⟩
  have htK : t ∈ S8.CMt S t := S8.mem_CMt.mpr ⟨S.Lbar_le_Mbar g ht, rfl⟩
  have hXW := Vone_le_Wone H C ht ht1 hVQ hh hb
  have hperp : ∀ v ∈ Vone S g t g ((h : G) * g), ∀ w ∈ Wone S g t g ((h : G) * g),
      polar S.q v w = 0 := fun v hv w hw => mem_Wone.mp hw v hv
  have hrad : ∀ w ∈ Wone S g t g ((h : G) * g),
      (∀ w' ∈ Wone S g t g ((h : G) * g), polar S.q w w' = 0) →
        w ∈ Vone S g t g ((h : G) * g) := by
    intro w _ hw'
    have hrefl : S.q.polarBilin.IsRefl := fun x y hxy => by
      rw [polarBilin_apply_apply] at hxy ⊢
      rw [polar_comm]
      exact hxy
    rw [← LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate hrefl
      (Vone S g t g ((h : G) * g))]
    intro n hn
    rw [polarBilin_apply_apply, polar_comm]
    exact hw' n hn
  have hnd := secForm_nondegenerate hXW hperp hrad
  have hf := beta_isAlt H C ht ht1 hVQ
  have hnd' := beta_nondegenerate H C ht ht1 hVQ
  have hpp₁ := beta_aV_bV H C ht ht1 hVQ hh hb
  have h4' : finrank (ZMod 2) (Vt S g t) = 2 * 2 := by rw [h4]
  have hdiv : ∀ Z : Submodule (ZMod 2) ↥((Wone S g t g ((h : G) * g)).map
      (Vone S g t g ((h : G) * g)).mkQ), (∀ γ, ∀ z ∈ Z, ρ γ z ∈ Z) →
        4 ∣ finrank (ZMod 2) Z := fun Z hZ =>
    pow_dvd_finrank_of_invariant ρ hf hnd' (m := 2) (by norm_num) h4' hpp₁ hD hZ
  have hend : ∀ Z : Submodule (ZMod 2) ↥((Wone S g t g ((h : G) * g)).map
      (Vone S g t g ((h : G) * g)).mkQ), (∀ γ, ∀ z ∈ Z, ρ γ z ∈ Z) →
      finrank (ZMod 2) Z = 4 → ∀ φ : _ →ₗ[ZMod 2] _, (∀ z ∈ Z, φ z ∈ Z) →
      (∀ γ, ∀ z ∈ Z, φ (ρ γ z) = ρ γ (φ z)) → ∃ c : ZMod 2, ∀ z ∈ Z, φ z = c • z := by
    intro Z hZ hZ4 φ hφZ hφc
    exact S2.timmesfeld_2_6_1_sp ρ hf hnd' 2 (bot_inf_eq _) (by norm_num)
      (by rw [S2.spPerp_bot, finrank_top]; exact h4') (fun γ _ v hv => hZ γ v hv)
      (by rw [S2.spPerp_bot]; exact Submodule.mem_top)
      (by rw [S2.spPerp_bot]; exact Submodule.mem_top) hpp₁
      (spRadDecomp_of_invariant ρ hf hnd' h4' hpp₁ hD hZ) (by rw [hZ4]; norm_num) φ hφZ
      (fun γ _ v hv => hφc γ v hv)
  have hconj : ∀ {x : S.O}, x * t * x⁻¹ * (x * t * x⁻¹) = 1 := fun {x} => by
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have hsq := secHomK_comp_eq_self hX hW ⟨_, hτK hx₁ h₁⟩ ⟨_, hτK hx₁ h₁⟩ fun w _ => by
    rw [← coe_mul_apply, hconj, Subgroup.coe_one, LinearEquiv.coe_one, id, sub_self]
    exact zero_mem _
  have hc := secHomK_comp_eq_comp hX hW ⟨_, hτK hx₁ h₁⟩ ⟨_, hτK hx₂ h₂⟩ ⟨_, hτK hx₁ h₁⟩
    ⟨_, hτK hx₂ h₂⟩ fun w _ => by
      rw [← coe_mul_apply, ← coe_mul_apply, h₁₂, sub_self]
      exact zero_mem _
  have h₃' := secHomK_eq_comp hX hW ⟨_, hτK hx₁ h₁⟩ ⟨_, hτK hx₂ h₂⟩ ⟨_, hτK hx₃ h₃⟩ h₁₂₃
  have hV₁ := fix_Vt_of_inf_eq_bot H (S8.mem_CMt.mp (hτK hx₁ h₁)).1 h₁
    (inf_commSpace_eq_bot H C ht ht1 hVQ hSp.transitive hL hx₁ hβ₁)
  have hV₂ := fix_Vt_of_inf_eq_bot H (S8.mem_CMt.mp (hτK hx₂ h₂)).1 h₂
    (inf_commSpace_eq_bot H C ht ht1 hVQ hSp.transitive hL hx₂ hβ₂)
  have hd₁ := finrank_commSpace_secHomK_typeII hCE H hNo C ht ht1 hVQ hSp hh hb ρ hρ hD h4 hL
    hX hW hx₁ h₁ hβ₁ (hτK hx₁ h₁)
  have hd₂ := finrank_commSpace_secHomK_typeII hCE H hNo C ht ht1 hVQ hSp hh hb ρ hρ hD h4 hL
    hX hW hx₂ h₂ hβ₂ (hτK hx₂ h₂)
  have hd₃ := finrank_commSpace_secHomK_typeII hCE H hNo C ht ht1 hVQ hSp hh hb ρ hρ hD h4 hL
    hX hW hx₃ h₃ hβ₃ (hτK hx₃ h₃)
  exact finrank_commSpace_mul_ne_four ρ hnd hdiv hend hsq (secForm_secHomK hX hW hXW hperp _)
    (secForm_secHomK hX hW hXW hperp _)
    (secHomK_comm_rho hCE H hNo C ht ht1 hVQ hSp hh hb ρ hρ hX hW _ hV₁)
    (secHomK_comm_rho hCE H hNo C ht ht1 hVQ hSp hh hb ρ hρ hX hW _ hV₂) hd₁ hd₂ hc h₃' hd₃

theorem false_of_triangle (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x₁ x₂ x₃ : S.O} (hx₁ : x₁ ∈ S.Mbar) (hx₂ : x₂ ∈ S.Mbar) (hx₃ : x₃ ∈ S.Mbar)
    (h₁ : x₁ * t * x₁⁻¹ * t = t * (x₁ * t * x₁⁻¹))
    (h₂ : x₂ * t * x₂⁻¹ * t = t * (x₂ * t * x₂⁻¹))
    (h₃ : x₃ * t * x₃⁻¹ * t = t * (x₃ * t * x₃⁻¹))
    (hβ₁ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x₁ * t * x₁⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t)
    (hβ₂ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x₂ * t * x₂⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t)
    (hβ₃ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x₃ * t * x₃⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t)
    (h₁₂ : x₁ * t * x₁⁻¹ * (x₂ * t * x₂⁻¹) = x₂ * t * x₂⁻¹ * (x₁ * t * x₁⁻¹))
    (h₁₂₃ : x₃ * t * x₃⁻¹ = t * (x₁ * t * x₁⁻¹) * (x₂ * t * x₂⁻¹)) : False :=
  false_of_triple hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL hx₁ hx₂ hx₃ h₁ h₂ h₃ hβ₁ hβ₂ hβ₃ h₁₂
    fun w _ => by
      rw [h₁₂₃, coe_mul_apply, coe_mul_apply]
      exact Vt_le_Vone _ _ ((commSpace_t_eq H C ht ht1 hVQ).1 ▸ sub_mem_commSpace _ _)

theorem commSpace_inf_Vone_eq_bot (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x : S.O} (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ Vone S g t g ((h : G) * g) = ⊥ := by
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_3_three hCE H hNo C ht ht1 hVQ hSp hh hb
  have hX := CMt_apply_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb
  have hW := CMt_apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb
  have hτK : x * t * x⁻¹ ∈ S8.CMt S t := S8.mem_CMt.mpr
    ⟨S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM), hτt⟩
  have h1 := finrank_commSpace_secHomK_typeII hCE H hNo C ht ht1 hVQ hSp hh hb ρ hρ hD h4 hL
    hX hW hxM hτt hβ hτK
  have h2 := finrank_commSpace_secHomK_add_le hX hW (⟨_, hτK⟩ : S8.CMt S t)
  have h3 : finrank (ZMod 2) (commSpace ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4 := by
    rw [S8.commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1, LinearEquiv.finrank_map_eq, h4]
  simp only [Subtype.coe_mk] at h2
  exact Submodule.finrank_eq_zero.mp (by omega)

end Tri

end CFSG.LargeExtraspecial.S9
