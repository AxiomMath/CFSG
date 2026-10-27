module

public import CFSG.GF2Type.Smith1979.W4FiveQ
public import CFSG.LargeExtraspecial.S4SevenA6
public import CFSG.LargeExtraspecial.S5OneMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Five

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S5 CFSG.Open CFSG.ComponentClassification

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Nbar_le_Lbar_of_factor (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g) {X : Subgroup S.O}
    (hfac : ∀ x ∈ RmodN S g t, ∃ k ∈ imgR H.conj_mem t X, ∃ e ∈ LmodN S g t, x = k * e)
    (hcomm : ∀ n ∈ Nbar S g t, ∀ x ∈ X, n * x = x * n)
    (hsup : Nbar S g t = ⨆ Y ∈ Dset S g t, Y ⊓ Nbar S g t) : Nbar S g t ≤ S.Lbar g := by
  have haQ := H.conj_mem
  refine hsup.le.trans (iSup₂_le fun Y hY => ?_)
  obtain ⟨h, rfl, hth⟩ := hY
  intro y hy
  obtain ⟨k, hkR, hk⟩ := dtEqConj_of_ne H hNo C ht ht1 hR h hth
  have hyL : y ∈ S.Lbar ((k : G) * g) := hk ▸ hy.1
  rw [mem_Lbar_mul_iff] at hyL
  obtain ⟨x, hxX, -, s, hs, n, hnN, hkr⟩ := exists_mul_mul_of_factor H ht hfac hkR
  rw [hkr] at hyL
  have hxy : x * y = y * x := (hcomm y hy.2 x hxX).symm
  have hnL := Nbar_le_normalizer haQ H.conj_ne (Lbar_mem_Dset ht) hnN
  have e : (x * s * n)⁻¹ * y * (x * s * n) = n⁻¹ * (s⁻¹ * y * s) * n⁻¹⁻¹ := by
    calc (x * s * n)⁻¹ * y * (x * s * n) = n⁻¹ * s⁻¹ * (x⁻¹ * (y * x)) * s * n := by group
      _ = n⁻¹ * s⁻¹ * (x⁻¹ * (x * y)) * s * n := by rw [hxy]
      _ = n⁻¹ * (s⁻¹ * y * s) * n⁻¹⁻¹ := by group
  rw [e] at hyL
  have h1 : s⁻¹ * y * s ∈ S.Lbar g :=
    (mem_normalizer_iff.mp (inv_mem hnL) (s⁻¹ * y * s)).mpr hyL
  have e2 : y = s * (s⁻¹ * y * s) * s⁻¹ := by group
  rw [e2]
  exact mul_mem (mul_mem hs h1) (inv_mem hs)

theorem Nbar_le_Lbar_w4 (A : CompAt S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4) :
    IsPGroup 2 (Nbar S g A.t) ∧ Nbar S g A.t ≤ S.Lbar g := by
  have hR := A.Rbar_ne hIrr H
  have hfac := (A.hyp45q hIrr H hNo C Q).1.1
  obtain ⟨h2, -, hsup⟩ := timmesfeld_4_7_a_of_not_a6 hCE H hNo C A.mem_Lbar A.ne_one hR
    (fun hVQ => W4ThmA.not_pgl25Case hw H C A.mem_Lbar A.ne_one hVQ)
    (fun hVQ => W4ThmA.not_a6Case hw H C A.mem_Lbar A.ne_one hVQ)
  exact ⟨h2, Nbar_le_Lbar_of_factor H hNo C A.mem_Lbar A.ne_one hR hfac
    (fun n hn x hx => A.commute_of_mem_Nbar_of_isPGroup hIrr H C h2 hn hx) hsup⟩

theorem card_LmodN_inf_le_w4 (A : CompAt S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4) :
    Nat.card (LmodN S g A.t ⊓ imgR H.conj_mem A.t A.X : Subgroup _) ≤
      Nat.card (S.Lbar g ⊓ A.X : Subgroup S.O) := by
  have hNL := (Nbar_le_Lbar_w4 A hCE hIrr H hNo C Q hw).2
  let f : (S.Lbar g ⊓ A.X : Subgroup S.O) →
      (LmodN S g A.t ⊓ imgR H.conj_mem A.t A.X : Subgroup _) := fun y =>
    ⟨resV H.conj_mem A.t ⟨y, Lbar_le_Rbar A.mem_Lbar y.2.1⟩,
      resV_mem_LmodN H.conj_mem y.2.1 _, mem_imgR.mpr ⟨_, y.2.2, rfl⟩⟩
  refine Nat.card_le_card_of_surjective f fun e => ?_
  obtain ⟨⟨s, hs, hse⟩, hK⟩ := e.2
  obtain ⟨y, hyX, hye⟩ := mem_imgR.mp hK
  have hsR : s ∈ Rbar S g A.t := Lbar_le_Rbar A.mem_Lbar hs
  have hres : resV H.conj_mem A.t ⟨s, hsR⟩ = e :=
    LinearEquiv.ext fun v => Subtype.ext (hse v).symm
  have hN : ((y⁻¹ * ⟨s, hsR⟩ : Rbar S g A.t) : S.O) ∈ Nbar S g A.t := by
    rw [← resV_eq_one_iff H.conj_mem, map_mul, map_inv, hres, hye, inv_mul_cancel]
  have hyL : (y : S.O) ∈ S.Lbar g := by
    have := mul_mem hs (inv_mem (hNL hN))
    simpa using this
  refine ⟨⟨y, hyL, hyX⟩, Subtype.ext ?_⟩
  change resV H.conj_mem A.t ⟨y, _⟩ = (e : Vt S g A.t ≃ₗ[ZMod 2] Vt S g A.t)
  rw [← hye]

theorem false_of_not_le_w4 (P : PairData S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4)
    (hVQ : ¬ V S g P.τ ≤ S.Qa g) : False := by
  have h2 := P.card_Lbar_inf_le_two hIrr H hNo C Q hVQ
  have hK : Nat.card (LmodN S g P.t ⊓ imgR H.conj_mem P.t P.X₂ : Subgroup _) ≤
      Nat.card (S.Lbar g ⊓ P.X₂ : Subgroup S.O) :=
    card_LmodN_inf_le_w4 P.A₁ hCE hIrr H hNo C Q hw
  have : Finite (Vt S g P.t ≃ₗ[ZMod 2] Vt S g P.t) := finite_linearEquiv_of_finite
  by_cases hVt : V S g P.t ≤ S.Qa g
  · have h4 : 4 ≤ Nat.card (LmodN S g P.t) := P.A₁.four_le_card_LmodN hIrr H hNo C Q hVt
    have hKR : imgR H.conj_mem P.t P.X₂ = RmodN S g P.t :=
      ((P.A₁.hyp45q hIrr H hNo C Q).2 hVt).1
    have hle : LmodN S g P.t ≤ LmodN S g P.t ⊓ imgR H.conj_mem P.t P.X₂ :=
      le_inf le_rfl (by rw [hKR]; exact LmodN_le_RmodN P.t_mem_Lbar)
    have := card_le_of_le hle
    omega
  · obtain ⟨hKR, h4⟩ := quasisimple_w4 Q hNo hw P.t_mem_Lbar P.t_ne_one (P.A₁.Rbar_ne hIrr H)
      hVt (P.A₁.isSubnormal_img hIrr H) (P.A₁.isQuasisimple_img hIrr H C)
    have hKR : imgR H.conj_mem P.t P.X₂ = RmodN S g P.t := hKR
    have hle : LmodN S g P.t ≤ LmodN S g P.t ⊓ imgR H.conj_mem P.t P.X₂ :=
      le_inf le_rfl (by rw [hKR]; exact LmodN_le_RmodN P.t_mem_Lbar)
    have := card_le_of_le hle
    omega

theorem card_Lbar_le_w4 (P : PairData S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4)
    (hVt : V S g P.t ≤ S.Qa g) :
    Nat.card (S.Lbar g) ≤ Nat.card (S.Lbar g ⊓ Nbar S g P.t : Subgroup S.O) *
      Nat.card (S.Lbar g ⊓ P.X₂ : Subgroup S.O) := by
  have hK : Nat.card (LmodN S g P.t ⊓ imgR H.conj_mem P.t P.X₂ : Subgroup _) ≤
      Nat.card (S.Lbar g ⊓ P.X₂ : Subgroup S.O) :=
    card_LmodN_inf_le_w4 P.A₁ hCE hIrr H hNo C Q hw
  have hKR : imgR H.conj_mem P.t P.X₂ = RmodN S g P.t :=
    ((P.A₁.hyp45q hIrr H hNo C Q).2 hVt).1
  have hle : LmodN S g P.t ≤ LmodN S g P.t ⊓ imgR H.conj_mem P.t P.X₂ :=
    le_inf le_rfl (by rw [hKR]; exact LmodN_le_RmodN P.t_mem_Lbar)
  have : Finite (Vt S g P.t ≃ₗ[ZMod 2] Vt S g P.t) := finite_linearEquiv_of_finite
  rw [card_Lbar_eq H.conj_mem P.t_mem_Lbar]
  exact Nat.mul_le_mul_left _ ((card_le_of_le hle).trans hK)

theorem exists_mul_w4 (P : PairData S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) {s : S.O} (hs : s ∈ S.Lbar g) :
    ∃ s₁ ∈ S.Lbar g ⊓ P.X₁, ∃ s₂ ∈ S.Lbar g ⊓ P.X₂, s = s₁ * s₂ := by
  have h1 := card_Lbar_le_w4 P hCE hIrr H hNo C Q hw hVt
  have h2 : Nat.card (S.Lbar g) ≤ Nat.card (S.Lbar g ⊓ Nbar S g P.τ : Subgroup S.O) *
      Nat.card (S.Lbar g ⊓ P.X₁ : Subgroup S.O) :=
    card_Lbar_le_w4 P.swap hCE hIrr H hNo C Q hw hVτ
  have h3 := card_mul_card_le_of_inf_eq_bot inf_le_left inf_le_left
    (P.Lbar_inf_Nbar_inf_eq_bot hIrr H hNo C Q)
  have h4 := card_mul_card_le_of_inf_eq_bot inf_le_left inf_le_left (P.Lbar_inf_inf_eq_bot H)
  have hpos : 0 < Nat.card (S.Lbar g) := Nat.card_pos
  set L := Nat.card (S.Lbar g)
  set a := Nat.card (S.Lbar g ⊓ Nbar S g P.t : Subgroup S.O)
  set b := Nat.card (S.Lbar g ⊓ Nbar S g P.τ : Subgroup S.O)
  set c := Nat.card (S.Lbar g ⊓ P.X₁ : Subgroup S.O)
  set d := Nat.card (S.Lbar g ⊓ P.X₂ : Subgroup S.O)
  have h5 : L * L ≤ L * (c * d) := by
    calc L * L ≤ (a * d) * (b * c) := Nat.mul_le_mul h1 h2
      _ = (a * b) * (c * d) := by ring
      _ ≤ L * (c * d) := Nat.mul_le_mul_right _ h3
  exact exists_mul_of_card_le inf_le_left inf_le_left (P.Lbar_inf_inf_eq_bot H)
    (Nat.le_of_mul_le_mul_left h5 hpos) hs

theorem exists_conj_fix_w4 (P : PairData S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) {x : S.O} (hx : x ∈ P.X₁) :
    ∃ s ∈ S.Lbar g ⊓ P.X₁, x * s * x⁻¹ ≠ 1 ∧
      ((x * s * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl (g * S.z * g⁻¹) := by
  classical
  have haQ := H.conj_mem
  have hL : LinCase S g P.τ_mem_Lbar := P.A₂.linCase hIrr H hNo C hVτ
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g P.τ) := ((P.A₂.hyp45q hIrr H hNo C Q).2 hVτ).2
  have hxR : x ∈ Rbar S g P.τ := P.A₂.le_Rbar hIrr H hx
  obtain ⟨c, hc⟩ : ∃ c, c = resV haQ P.τ ⟨x, hxR⟩ := ⟨_, rfl⟩
  obtain ⟨w, hw'⟩ : ∃ w, w = c⁻¹ (aV P.τ_mem_Lbar) := ⟨_, rfl⟩
  obtain ⟨φ, hφ0, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (Vt S g P.τ), φ ≠ 0 ∧
      Submodule.span (ZMod 2) ({aV P.τ_mem_Lbar, w} : Set (Vt S g P.τ)) ≤ LinearMap.ker φ := by
    apply Submodule.exists_le_ker_of_lt_top
    rw [lt_top_iff_ne_top]
    intro htop
    have h1 := finrank_span_finset_le_card (R := ZMod 2)
      ({aV P.τ_mem_Lbar, w} : Finset (Vt S g P.τ))
    rw [Finset.coe_insert, Finset.coe_singleton] at h1
    change finrank (ZMod 2) (Submodule.span (ZMod 2) _) ≤ _ at h1
    rw [htop, finrank_top] at h1
    have h2 := Finset.card_le_two (a := aV P.τ_mem_Lbar) (b := w)
    omega
  have hφa : φ (aV P.τ_mem_Lbar) = 0 := hφ (Submodule.subset_span (Set.mem_insert _ _))
  have hφw : φ w = 0 := hφ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have heL : LinearEquiv.transvection hφa ∈ LmodN S g P.τ := by
    rw [hL.LmodN_eq]
    exact transvection_mem_centreGroup hφa
  obtain ⟨s, hs, hse⟩ := heL
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := exists_mul_w4 P hCE hIrr H hNo C Q hw hVt hVτ hs
  have hs₂N : s₂ ∈ Nbar S g P.τ :=
    P.A₂.mem_Nbar_of_commute hIrr H hNo C Q hs₂.1 fun y hy => (P.comm hy hs₂.2).symm
  have hs₁v : ∀ v : Vt S g P.τ, ((LinearEquiv.transvection hφa v : Vt S g P.τ) : S.Qt) =
      (s₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro v
    rw [hse v, coe_mul_apply, hs₂N.2 v v.2]
  have hxw : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = (w : S.Qt) := by
    rw [hw', hc, ← map_inv, coe_resV_apply]
    rfl
  refine ⟨s₁, hs₁, ?_, ?_⟩
  · intro h1
    have hs1 : s₁ = 1 := by
      have e : s₁ = x⁻¹ * (x * s₁ * x⁻¹) * x := by group
      rw [e, h1, mul_one, inv_mul_cancel]
    obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hφ0 (LinearMap.ext hcon)
    have hv1 : φ v = 1 :=
      (CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_zero_or_eq_one _).resolve_left hv
    have := hs₁v v
    rw [hs1, LinearEquiv.transvection.apply, hv1, one_smul] at this
    have h0 : ((aV P.τ_mem_Lbar : Vt S g P.τ) : S.Qt) = 0 := by
      have h2 : ((v : S.Qt) + (aV P.τ_mem_Lbar : S.Qt)) = v := this
      calc ((aV P.τ_mem_Lbar : Vt S g P.τ) : S.Qt) = (v + aV P.τ_mem_Lbar : S.Qt) - v := by abel
        _ = 0 := by rw [h2, sub_self]
    exact aV_ne_zero H P.τ_mem_Lbar (Subtype.ext h0)
  · calc ((x * s₁ * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))
        = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))) := by
          rw [coe_mul_apply, coe_mul_apply]
      _ = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((LinearEquiv.transvection hφa w : Vt S g P.τ) : S.Qt) := by
          rw [hxw, hs₁v w]
      _ = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (S.cl (g * S.z * g⁻¹))) := by
          rw [LinearEquiv.transvection.apply, hφw, zero_smul, add_zero, hxw]
      _ = S.cl (g * S.z * g⁻¹) := apply_inv_apply_O x _

theorem commute_of_mem_sup_w4 (P : PairData S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) (k : S.M)
    (hk : S.ρ k ∈ P.X₁ ⊔ P.X₂) :
    (g * S.z * g⁻¹) * ((k : G) * g * S.z * ((k : G) * g)⁻¹) =
      ((k : G) * g * S.z * ((k : G) * g)⁻¹) * (g * S.z * g⁻¹) := by
  have hN : P.X₁ ≤ normalizer (P.X₂ : Set S.O) := fun x hx =>
    mem_normalizer_of_forall_commute fun y hy => P.comm hx hy
  obtain ⟨x₁, hx₁, x₂, hx₂, hk'⟩ := exists_mul_of_mem_sup hN hk
  obtain ⟨s, hs, hs1, hfix⟩ := exists_conj_fix_w4 P hCE hIrr H hNo C Q hw hVt hVτ hx₁
  have he : S.ρ k * s * (S.ρ k)⁻¹ = x₁ * s * x₁⁻¹ := by
    rw [hk']
    have h2 : x₂ * s = s * x₂ := (P.comm hs.2 hx₂).symm
    calc x₁ * x₂ * s * (x₁ * x₂)⁻¹ = x₁ * (x₂ * s) * x₂⁻¹ * x₁⁻¹ := by group
      _ = x₁ * (s * x₂) * x₂⁻¹ * x₁⁻¹ := by rw [h2]
      _ = x₁ * s * x₁⁻¹ := by group
  have hmem : x₁ * s * x₁⁻¹ ∈ S.Lbar ((k : G) * g) := he ▸ conj_mem_Lbar_mul S k hs.1
  have hM : x₁ * s * x₁⁻¹ ∈ S.Mbar :=
    P.comp₁.1 (P.X₁.mul_mem (P.X₁.mul_mem hx₁ hs.2) (P.X₁.inv_mem hx₁))
  have hnorm : x₁ * s * x₁⁻¹ ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix H.conj_mem H.conj_ne (h := 1) hM (by simpa using hfix)
    simpa using this
  exact S4.lemma_4_1 H k ⟨_, hmem, hnorm, hs1⟩

theorem eq_or_eq_of_norm_w4 (P : PairData S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) {X₃ : Subgroup S.O}
    (h₃ : IsComponentOf X₃ S.Mbar)
    (hn₃ : ∀ h : S.M, S.Lbar ((h : G) * g) ≤ normalizer (X₃ : Set S.O)) :
    X₃ = P.X₁ ∨ X₃ = P.X₂ := by
  by_contra hne
  push Not at hne
  obtain ⟨hne₁, hne₂⟩ := hne
  obtain ⟨⟨s, hs⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Lbar_inf_ne_bot hIrr H C h₃ hn₃)
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hsL : s ∈ S.Lbar g := (Subgroup.mem_inf.mp hs).1
  have hsX : s ∈ X₃ := (Subgroup.mem_inf.mp hs).2
  obtain ⟨s₁, hs₁, s₂, hs₂, hss⟩ := exists_mul_w4 P hCE hIrr H hNo C Q hw hVt hVτ hsL
  have hcomm : ∀ z ∈ X₃, s * z = z * s := by
    intro z hz
    have c₁ : s₁ * z = z * s₁ := mul_comm_of_isComponentOf_ne P.comp₁ h₃ (Ne.symm hne₁) hs₁.2 hz
    have c₂ : s₂ * z = z * s₂ := mul_comm_of_isComponentOf_ne P.comp₂ h₃ (Ne.symm hne₂) hs₂.2 hz
    rw [hss]
    calc s₁ * s₂ * z = s₁ * (s₂ * z) := mul_assoc _ _ _
      _ = s₁ * (z * s₂) := by rw [c₂]
      _ = (s₁ * z) * s₂ := (mul_assoc _ _ _).symm
      _ = z * s₁ * s₂ := by rw [c₁]
      _ = z * (s₁ * s₂) := mul_assoc _ _ _
  have hss2 : s ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    exact S4.mul_self_of_mem_Lbar S H.conj_mem hsL
  exact hs1' (eq_one_of_mem_center_of_pow S h₃.2.1 hsX hcomm hss2)

theorem map_sup_eq_w4 (P : PairData S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) (k : S.M) :
    (P.X₁ ⊔ P.X₂).map (MulAut.conj (S.ρ k)).toMonoidHom = P.X₁ ⊔ P.X₂ := by
  have hkM : (S.ρ k : S.O) ∈ S.Mbar := ⟨k, rfl⟩
  have hinj : Function.Injective (Subgroup.map (MulAut.conj (S.ρ k)).toMonoidHom) :=
    map_injective fun _ _ h => (MulAut.conj (S.ρ k)).injective h
  have hne : P.X₁.map (MulAut.conj (S.ρ k)).toMonoidHom ≠
      P.X₂.map (MulAut.conj (S.ρ k)).toMonoidHom := fun h => P.ne (hinj h)
  rw [Subgroup.map_sup]
  rcases eq_or_eq_of_norm_w4 P hCE hIrr H hNo C Q hw hVt hVτ
      (isComponentOf_map_conj P.comp₁ hkM) (norm_map_conj P.norm₁ k) with h₁ | h₁ <;>
    rcases eq_or_eq_of_norm_w4 P hCE hIrr H hNo C Q hw hVt hVτ
      (isComponentOf_map_conj P.comp₂ hkM) (norm_map_conj P.norm₂ k) with h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hne
  · rw [h₁, h₂]
  · rw [h₁, h₂, sup_comm]
  · exact absurd (h₁.trans h₂.symm) hne

theorem exists_cl_eq_w4 (P : PairData S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) (k : S.M) :
    ∃ j : S.M, S.ρ j ∈ P.X₁ ⊔ P.X₂ ∧
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) = S.cl ((j : G) * g * S.z * ((j : G) * g)⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haQ := H.conj_mem
  have hYM : P.X₁ ⊔ P.X₂ ≤ S.Mbar := sup_le P.comp₁.1 P.comp₂.1
  have hLY : S.Lbar g ≤ P.X₁ ⊔ P.X₂ := by
    intro s hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := exists_mul_w4 P hCE hIrr H hNo C Q hw hVt hVτ hs
    exact mul_mem (mem_sup_left hs₁.2) (mem_sup_right hs₂.2)
  obtain ⟨T, hT, hLT⟩ := exists_isSylowTwoIn_ge hLY (S4.isPGroup_Lbar S haQ)
  have hTN : T ≤ normalizer (S.Lbar g : Set S.O) :=
    S4.le_normalizer_of_weaklyClosed C.weaklyClosed hT.isPGroup (hT.le.trans hYM) hLT
  have hT' : IsSylowTwoIn (T.map (MulAut.conj (S.ρ k)).toMonoidHom) (P.X₁ ⊔ P.X₂) := by
    have := hT.map (MulAut.conj (S.ρ k)).toMonoidHom
    rwa [map_sup_eq_w4 P hCE hIrr H hNo C Q hw hVt hVτ k] at this
  obtain ⟨c, hcY, hc⟩ := hT.exists_conj hT'
  obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp (hYM hcY)
  have hjk : S.Lbar (((j⁻¹ * k : S.M) : G) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    intro l hl
    apply hTN
    have hl' : (S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k) ∈ S.Lbar g := (mem_Lbar_mul_iff S _ g).mp hl
    have hmem : S.ρ k * ((S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k)) * (S.ρ k)⁻¹ ∈
        T.map (MulAut.conj (S.ρ k)).toMonoidHom := by
      rw [mem_map_conj_iff]
      have e : (S.ρ k)⁻¹ * (S.ρ k * ((S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k)) * (S.ρ k)⁻¹) *
          S.ρ k = (S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k) := by group
      rw [e]
      exact hLT hl'
    have h2 := (hc _).mp hmem
    rw [← hj] at h2
    have e : (S.ρ j)⁻¹ * (S.ρ k * ((S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k)) * (S.ρ k)⁻¹) *
        S.ρ j = l := by
      simp only [map_mul, map_inv]
      group
    rwa [e] at h2
  have heq := C.weaklyClosed _ (j⁻¹ * k).2 hjk
  have hnorm : S.ρ (j⁻¹ * k) ∈ normalizer (S.Lbar g : Set S.O) := by
    rw [Lbar_mul S (j⁻¹ * k)] at heq
    exact mem_normalizer_of_map_conj_eq heq
  have hfix := fix_of_mem_normalizer H hnorm
  refine ⟨j, hj ▸ hcY, ?_⟩
  rw [← ρ_cl_conj_z S k haQ, ← ρ_cl_conj_z S j haQ]
  have e : S.ρ k = S.ρ j * S.ρ (j⁻¹ * k) := by
    rw [map_mul, map_inv, mul_inv_cancel_left]
  rw [e, coe_mul_apply, hfix]

theorem pairData_false_w4 (P : PairData S g) (hCE : CentralExtInput.{u}) (hIrr : Irr S)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4) :
    False := by
  have hVτ : V S g P.τ ≤ S.Qa g := by
    by_contra h
    exact false_of_not_le_w4 P hCE hIrr H hNo C Q hw h
  have hVt : V S g P.t ≤ S.Qa g := by
    by_contra h
    exact false_of_not_le_w4 P.swap hCE hIrr H hNo C Q hw h
  have hpol : ∀ v ∈ conjCl S g, QuadraticMap.polar S.q (S.cl (g * S.z * g⁻¹)) v = 0 := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨j, hjY, hj⟩ := exists_cl_eq_w4 P hCE hIrr H hNo C Q hw hVt hVτ k
    rw [hj, S.polar_cl_eq_zero_iff H.conj_mem (conj_mem_QG' S j.2 H.conj_mem)]
    exact commute_of_mem_sup_w4 P hCE hIrr H hNo C Q hw hVt hVτ j hjY
  apply cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  refine S.q_nondegenerate.1 _ fun v => ?_
  rw [QuadraticMap.polarBilin_apply_apply]
  have hv : v ∈ Submodule.span (ZMod 2) (conjCl S g) := by
    rw [span_conjCl_eq_top hIrr H]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem v hv => exact hpol v hv
  | zero => exact QuadraticMap.polar_zero_right _ _
  | add u w _ _ hu hw => rw [QuadraticMap.polar_add_right, hu, hw, add_zero]
  | smul c u _ hu => rw [QuadraticMap.polar_smul_right, hu, smul_zero]

theorem timmesfeld_5_1_w4 (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4)
    {X₁ X₂ : Subgroup S.O} (h₁ : IsComponentOf X₁ S.Mbar) (h₂ : IsComponentOf X₂ S.Mbar)
    (hN₁ : Mbar0 S g ≤ normalizer (X₁ : Set S.O))
    (hN₂ : Mbar0 S g ≤ normalizer (X₂ : Set S.O)) : X₁ = X₂ := by
  rw [Mbar0_le_normalizer_iff] at hN₁ hN₂
  by_contra hne
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Lbar_inf_ne_bot hIrr H C h₁ hN₁)
  obtain ⟨⟨τ, hτ⟩, hτ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Lbar_inf_ne_bot hIrr H C h₂ hN₂)
  exact pairData_false_w4 ⟨X₁, X₂, t, τ, h₁, h₂, hN₁, hN₂, hne, (mem_inf.mp ht).1,
    (mem_inf.mp ht).2, fun h => ht1 (Subtype.ext h), (mem_inf.mp hτ).1, (mem_inf.mp hτ).2,
    fun h => hτ1 (Subtype.ext h)⟩ hCE hIrr H hNo C Q hw

end CFSG.GF2Type.Smith1979.W4Five
