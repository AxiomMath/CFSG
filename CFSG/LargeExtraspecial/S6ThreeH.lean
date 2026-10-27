module

public import CFSG.LargeExtraspecial.S6ThreeG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Three

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

omit hCE hNo hSp in
theorem finrank_w1v1 :
    finrank (ZMod 2) ↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ) +
      2 * finrank (ZMod 2) (Vone S g t g ((h : G) * g)) = 2 * S.width := by
  have h1 := S2.finrank_map_add_finrank_inf_ker (Vone S g t g ((h : G) * g)).mkQ
    (Wone S g t g ((h : G) * g))
  rw [Submodule.ker_mkQ, inf_eq_right.mpr (Vone_le_Wone H C ht ht1 hVQ hh hb)] at h1
  have h2 := finrank_Wone (S := S) (g := g) (t := t) g ((h : G) * g)
  have h3 := S.finrank_Qt_eq_two_mul_width
  omega

theorem timmesfeld_6_3_three :
    ∃ ρ : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ) →*
        (↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ) ≃ₗ[ZMod 2]
          ↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ)),
      (∀ (e : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)) (x : Rbar S g t),
        (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t x →
        ∀ w (hw : w ∈ Wone S g t g ((h : G) * g)),
          ((ρ e (secMk (Vone S g t g ((h : G) * g)) hw) :
            ↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ)) :
              S.Qt ⧸ Vone S g t g ((h : G) * g)) =
            (Vone S g t g ((h : G) * g)).mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) ∧
      S2.SpRadDecomp ρ ⊥ ⊤ (aV ht) (bV (mem_Lbar_of_pair H ht hh)) := by
  have hth := mem_Lbar_of_pair H ht hh
  have h1 := pair_one (t := t) hb
  have hba : ((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹ ∉ S.Qa ((h : G) * g) :=
    not_mem_Qa_symm h1.2
  have hdec := sup_clSub_inf_Wone hCE H hNo C ht ht1 hVQ hSp hh hb h1.1 hh h1.2
  have hint := sup_Vone_inf_sup_Vone hCE H hNo C ht ht1 hVQ hSp hh hb h1.1 hh h1.2
  simp only [OneMemClass.coe_one, one_mul] at hdec hint
  set X := Vone S g t g ((h : G) * g) with hXdef
  set Y := Wone S g t g ((h : G) * g) with hYdef
  have hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X :=
    fun x hx v hv => apply_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hx hv
  have hY : ∀ x ∈ Rbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Y :=
    fun x hx v hv => apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hx hv
  have hN : ∀ x ∈ Nbar S g t, ∀ v ∈ Y, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ X :=
    fun x hx v hv => Nbar_apply_sub_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hx hv
  refine ⟨secRepZ S g H.conj_mem t X Y hX hY hN hSp.eq_sp,
    fun e x hex w hw => secRepZ_apply H.conj_mem hX hY hN hSp.eq_sp hex hw, ?_⟩
  have hVW : X ≤ Y := Vone_le_Wone H C ht ht1 hVQ hh hb
  have hfa : S2.fixOf (secRepZ S g H.conj_mem t X Y hX hY hN hSp.eq_sp)
      (LmodN S g t : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      (((S.clSub (S.QG ⊓ S.Qa g) ⊓ Y) ⊔ X).map X.mkQ).comap (Y.map X.mkQ).subtype := by
    refine eq_comap_map_of_iff le_sup_right fun w hw => ?_
    rw [mem_fixOf_secRepZ_iff H.conj_mem hX hY hN hSp.eq_sp (K := (S.Lbar g : Set S.O))
      (fun x hx => Lbar_le_Rbar ht hx) (fun e he => ?_) hw]
    · have := forall_apply_sub_mem_Vone_iff hCE H hNo C ht ht1 hVQ hSp hh hb h1.1 hh h1.2 hw
      simpa using this
    · rw [SetLike.mem_coe, ← map_subgroupOf_resV H.conj_mem ht]
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l, hl, rfl⟩
      · rintro ⟨l, hl, rfl⟩
        exact ⟨_, hl, rfl⟩
  have hfb : S2.fixOf (secRepZ S g H.conj_mem t X Y hX hY hN hSp.eq_sp)
      (LhmodN S g t h : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      (((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Y) ⊔ X).map X.mkQ).comap
        (Y.map X.mkQ).subtype := by
    refine eq_comap_map_of_iff le_sup_right fun w hw => ?_
    rw [mem_fixOf_secRepZ_iff H.conj_mem hX hY hN hSp.eq_sp
      (K := (S.Lbar ((h : G) * g) : Set S.O)) (fun x hx => Lbar_mul_le_Rbar hth hx)
      (fun e he => ?_) hw]
    · exact forall_apply_sub_mem_Vone_iff hCE H hNo C ht ht1 hVQ hSp hh hb hh h1.1 hba hw
    · rw [SetLike.mem_coe, ← map_subgroupOf_resV_mul H.conj_mem hth]
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨l, hl, rfl⟩
      · rintro ⟨l, hl, rfl⟩
        exact ⟨_, hl, rfl⟩
  have hsup : ((S.clSub (S.QG ⊓ S.Qa g) ⊓ Y) ⊔ X) ⊔
      ((S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) ⊓ Y) ⊔ X) = Y := by
    refine le_antisymm (sup_le (sup_le inf_le_right hVW) (sup_le inf_le_right hVW)) ?_
    conv_lhs => rw [← hdec]
    exact sup_le_sup le_sup_left le_sup_left
  have hc := isCompl_comap_map le_sup_right hsup hint
  rw [← hfa, ← hfb, hSp.LmodN_eq, LhmodN_eq_spPointRadical H C ht ht1 hVQ hSp hh] at hc
  exact spRadDecomp_bot_of_isCompl hc

theorem timmesfeld_6_3_three_dvd {m : ℕ} (hm : finrank (ZMod 2) (Vt S g t) = 2 * m) :
    2 ^ m ∣ finrank (ZMod 2)
      ↥((Wone S g t g ((h : G) * g)).map (Vone S g t g ((h : G) * g)).mkQ) := by
  obtain ⟨ρ, -, hD⟩ := timmesfeld_6_3_three hCE H hNo C ht ht1 hVQ hSp hh hb
  have h4 := four_le_finrank_Vt H C ht ht1 hVQ hNo
  have hdvd := S2.sp_timmesfeld_2_1_b_dvd ρ (beta_isAlt H C ht ht1 hVQ)
    (beta_nondegenerate H C ht ht1 hVQ) m (bot_inf_eq _) (by omega)
    (by rw [S2.spPerp_bot, finrank_top]; omega) (fun _ _ v _ => Submodule.mem_top)
    (by rw [S2.spPerp_bot]; exact Submodule.mem_top)
    (by rw [S2.spPerp_bot]; exact Submodule.mem_top) (beta_aV_bV H C ht ht1 hVQ hh hb) hD
  rwa [finrank_top] at hdvd

end Three

end CFSG.LargeExtraspecial.S6
