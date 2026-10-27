module

public import CFSG.LargeExtraspecial.S14NQSixPre
public import CFSG.LargeExtraspecial.S14NQSixModA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}
  {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem fixOf_radFix_bV_eq (hNo : NoA2 S g) (D : S8.Std H C ht ht1 hVQ) [NQHyp S g t] :
    S2.fixOf (nqRep S g t D.hX)
        (radFix D.Q ⊥ (bV (mem_Lbar_of_pair H ht D.hh)) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
      nqSub S g t (S.Lbar ((D.h : G) * g)) := by
  have hL : ((radFix D.Q ⊥ (bV (mem_Lbar_of_pair H ht D.hh)) : Subgroup _) :
      Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) = LhmodN S g t D.h := by
    rw [radFix_bot, LhmodN_eq_pointRadical H ht D.hh (mem_Lbar_of_pair H ht D.hh) D.hX D.hE]
  exact fixOf_nqRep_eq H hNo C ht ht1 hVQ D.hgen D.hN0 D.hh D.hb D.hX D.hh hL

theorem comm_mem_zpowers_of_comm_mem (haQ : g * S.z * g⁻¹ ∈ S.QG) [hN : NQHyp S g t]
    (hext : IsExtraspecialPGroup 2 (Nbar S g t)) (htN : t ∈ Nbar S g t) (ht1 : t ≠ 1)
    {L₁ L₂ : Subgroup S.O} (hL₂ : ∀ a ∈ L₂, ∀ b ∈ L₂, a * b = b * a)
    (hprod : ∀ n ∈ Nbar S g t, ∃ x ∈ L₁ ⊓ Nbar S g t, ∃ w ∈ L₂ ⊓ Nbar S g t, n = x * w)
    {r : S.O} (hr : r ∈ Rbar S g t)
    (hA : ∀ x ∈ L₁ ⊓ Nbar S g t, r * x * r⁻¹ * x⁻¹ ∈ zpowers t)
    (hB : ∀ w ∈ L₂ ⊓ Nbar S g t, r * w * r⁻¹ ∈ L₂) :
    ∀ w ∈ L₂ ⊓ Nbar S g t, r * w * r⁻¹ * w⁻¹ ∈ zpowers t := by
  intro w hw
  have hrt : Commute r t := commute_of_mem_Rbar haQ hr
  have hwt : Commute w t := commute_of_mem_Rbar haQ (Nbar_le_Rbar hw.2)
  have hrw : r * w * r⁻¹ ∈ Nbar S g t := by
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
    have := conj_mem_Nbar haQ (k := k) (by rw [hk]; exact hrt.eq) hw.2
    rwa [hk] at this
  have hdN : r * w * r⁻¹ * w⁻¹ ∈ Nbar S g t := mul_mem hrw (inv_mem hw.2)
  have hdL : r * w * r⁻¹ * w⁻¹ ∈ L₂ := mul_mem (hB w hw) (inv_mem hw.1)
  have hcen : ∀ n ∈ Nbar S g t, Commute (r * w * r⁻¹ * w⁻¹) n := by
    intro n hn
    obtain ⟨x, hx, x', hx', rfl⟩ := hprod n hn
    have c1 : Commute (r * w * r⁻¹ * w⁻¹) x :=
      commute_of_comm_mem_zpowers hwt hrt (hN.comm _ hw.2 _ hx.2) (hA x hx)
    have c2 : Commute (r * w * r⁻¹ * w⁻¹) x' := hL₂ _ hdL _ hx'.1
    exact c1.mul_right c2
  have hdc : (⟨_, hdN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
    rw [mem_center_iff]
    intro n
    exact Subtype.ext (hcen n n.2).symm.eq
  by_cases hd1 : (⟨_, hdN⟩ : Nbar S g t) = 1
  · rw [show r * w * r⁻¹ * w⁻¹ = 1 from congrArg Subtype.val hd1]
    exact one_mem _
  · have htc : (⟨t, htN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
      rw [mem_center_iff]
      intro n
      exact Subtype.ext (commute_of_mem_Rbar haQ (Nbar_le_Rbar n.2))
    have := CFSG.RankThree.Literature.FSmith.eq_of_mem_center hext hdc htc hd1
      (fun e => ht1 (congrArg Subtype.val e))
    rw [show r * w * r⁻¹ * w⁻¹ = t from congrArg Subtype.val this]
    exact mem_zpowers t

theorem rho_eq_one_of_fix_A0 (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : S8.Std H C ht ht1 hVQ) [hN : NQHyp S g t] (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (y : omegaGroup D.Q D.hQ)
    (hyb : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) (bV (mem_Lbar_of_pair H ht D.hh)) =
      bV (mem_Lbar_of_pair H ht D.hh))
    (hyA : ∀ v ∈ A0 (nqRep S g t D.hX) (aV ht), nqRep S g t D.hX y v = v) (v : NQ S g t) :
    nqRep S g t D.hX y v = v := by
  have haQ := H.conj_mem
  have htN := self_mem_Nbar H ht
  have hthb : t ∈ S.Lbar ((D.h : G) * g) := mem_Lbar_of_pair H ht D.hh
  have hb0 : bV (mem_Lbar_of_pair H ht D.hh) ≠ 0 := by
    intro h0
    have := D.polar_aV_bV
    rw [h0, polar_zero_right] at this
    exact zero_ne_one this
  have hyR : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV haQ t).range := by
    rw [range_resV, D.hX]; exact y.2
  obtain ⟨r, hr⟩ := hyR
  have hrapp : ∀ n : Nbar S g t, nqRep S g t D.hX y (nqMk n) = nqMk (nConj r n) := fun n =>
    nqRep_apply D.hX (e := y) hr.symm n
  have hA0 : A0 (nqRep S g t D.hX) (aV ht) = nqSub S g t (S.Lbar g) :=
    S8.fixOf_nqRep_radFix_eq hNo D
  have hB0 : A0 (nqRep S g t D.hX) (bV (mem_Lbar_of_pair H ht D.hh)) =
      nqSub S g t (S.Lbar ((D.h : G) * g)) := fixOf_radFix_bV_eq hNo D
  have hA : ∀ x ∈ S.Lbar g ⊓ Nbar S g t, (r : S.O) * x * (r : S.O)⁻¹ * x⁻¹ ∈ zpowers t := by
    intro x hx
    have h1 := hyA (nqMk (⟨x, hx.2⟩ : Nbar S g t)) (by rw [hA0]; exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩)
    rw [hrapp, nqMk_nConj_eq_iff] at h1
    exact h1
  have hB : ∀ w ∈ S.Lbar ((D.h : G) * g) ⊓ Nbar S g t,
      (r : S.O) * w * (r : S.O)⁻¹ ∈ S.Lbar ((D.h : G) * g) := by
    intro w hw
    have hwB : nqMk (⟨w, hw.2⟩ : Nbar S g t) ∈
        A0 (nqRep S g t D.hX) (bV (mem_Lbar_of_pair H ht D.hh)) := by
      rw [hB0]; exact ⟨⟨w, hw.2⟩, hw.1, rfl⟩
    have h1 := mapsTo_A0 (nqRep S g t D.hX) hb0 D.Q_bV y hyb hwB
    rw [hB0, hrapp, mem_nqSub hthb, coe_nConj] at h1
    exact h1
  have hprod : ∀ n ∈ Nbar S g t, ∃ x ∈ S.Lbar g ⊓ Nbar S g t,
      ∃ w ∈ S.Lbar ((D.h : G) * g) ⊓ Nbar S g t, n = x * w := by
    intro n hn
    have h1R : S.ρ 1 ∈ Rbar S g t := by rw [map_one]; exact one_mem _
    have hgen' := D.hgen 1 D.h h1R D.hh (by rw [OneMemClass.coe_one, one_mul]; exact D.hb)
    obtain ⟨x, hx, x', hx', hxx'⟩ := exists_mul_of_pair H ht h1R D.hh hgen' D.hN0 hn
    rw [OneMemClass.coe_one, one_mul] at hx
    exact ⟨x, hx, x', hx', hxx'⟩
  have hcore := comm_mem_zpowers_of_comm_mem haQ hext htN ht1
    (fun a ha b hb => Lbar_comm S (H.mul D.h).conj_mem ha hb) hprod r.2 hA hB
  have hRD := timmesfeld_6_5_omega H hNo C ht ht1 hVQ hΩ D.hN0 D.hh D.hb D.hX D.hE
  have h1 : A0 (nqRep S g t D.hX) (aV ht) ≤ fixSpace (nqRep S g t D.hX y) := fun u hu =>
    mem_fixSpace.mpr (hyA u hu)
  have h2 : A0 (nqRep S g t D.hX) (bV (mem_Lbar_of_pair H ht D.hh)) ≤
      fixSpace (nqRep S g t D.hX y) := by
    intro u hu
    rw [hB0] at hu
    obtain ⟨w, hwL, rfl⟩ := hu
    rw [mem_fixSpace, hrapp, nqMk_nConj_eq_iff]
    exact hcore w ⟨hwL, w.2⟩
  have htop : (⊤ : Submodule (ZMod 2) (NQ S g t)) ≤ fixSpace (nqRep S g t D.hX y) :=
    hRD.1.ge.trans (sup_le (inf_le_right.trans h1) (inf_le_right.trans h2))
  exact mem_fixSpace.mp (htop Submodule.mem_top)

theorem eq_one_of_fix_A0 (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : S8.Std H C ht ht1 hVQ) [hN : NQHyp S g t] (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (h7 : ∀ x ∈ S.Mbar, (∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t) → x ∈ Nbar S g t)
    (y : omegaGroup D.Q D.hQ)
    (hyF : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈
      fixGroup (⊥ ⊔ Submodule.span (ZMod 2) {aV ht, bV (mem_Lbar_of_pair H ht D.hh)}))
    (hyA : ∀ v ∈ A0 (nqRep S g t D.hX) (aV ht), nqRep S g t D.hX y v = v) :
    (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = 1 := by
  have haQ := H.conj_mem
  have h1 := rho_eq_one_of_fix_A0 hNo hΩ D hext y (apply_p₁_of_mem_fixGroup hyF) hyA
  have hyR : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV haQ t).range := by
    rw [range_resV, D.hX]; exact y.2
  obtain ⟨r, hr⟩ := hyR
  have hrN : (r : S.O) ∈ Nbar S g t := by
    refine h7 _ (Rbar_le_Mbar r.2) fun n hn => ?_
    have h2 := h1 (nqMk (⟨n, hn⟩ : Nbar S g t))
    rw [nqRep_apply D.hX (e := y) hr.symm, nqMk_nConj_eq_iff] at h2
    exact h2
  rw [← hr]
  exact (resV_eq_one_iff haQ r).mpr hrN

end CFSG.LargeExtraspecial.S14
