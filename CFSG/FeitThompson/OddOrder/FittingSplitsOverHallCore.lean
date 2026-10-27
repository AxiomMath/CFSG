module

public import CFSG.FeitThompson.Foundations.SubgroupProductQuotient
public import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct
public import CFSG.FeitThompson.OddOrder.CoprimeNilpotentSubgroupsCommute

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise
open scoped commutatorElement

variable {M : Type*} [Group M]

theorem natCard_dvd_index_of_disjoint (H N : Subgroup M) [H.Normal] (hd : Disjoint H N) :
    Nat.card N ∣ H.index := by
  have hr : H.relIndex N = Nat.card N := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.2 hd, Subgroup.index_bot]
  exact hr ▸ Subgroup.relIndex_dvd_index_of_normal H N

theorem sup_inf_eq_of_normal_of_le {H U F : Subgroup M} [H.Normal] (hHF : H ≤ F)
    (hFK : F ≤ H ⊔ U) : H ⊔ (U ⊓ F) = F := by
  refine le_antisymm (sup_le hHF inf_le_right) fun x hx => ?_
  have hmem : x ∈ (H : Set M) * (U : Set M) := by rw [← Subgroup.normal_mul]; exact hFK hx
  obtain ⟨a, ha, u, hu, rfl⟩ := hmem
  exact Subgroup.mul_mem_sup ha (Subgroup.mem_inf.2 ⟨hu, by
    simpa using F.mul_mem (F.inv_mem (hHF ha)) hx⟩)

noncomputable def quotientSubgroupOfCongr {A B : Subgroup M} (hAB : A = B) (N : Subgroup M)
    [N.Normal] : A ⧸ N.subgroupOf A ≃* B ⧸ N.subgroupOf B := by
  subst hAB; exact MulEquiv.refl _

theorem quotientSubgroupOfCongr_symm_mk {A B : Subgroup M} (hAB : A = B) (N : Subgroup M)
    [N.Normal] (x : M) (hx : x ∈ B) :
    (quotientSubgroupOfCongr hAB N).symm (QuotientGroup.mk ⟨x, hx⟩) =
      QuotientGroup.mk ⟨x, hAB ▸ hx⟩ := by
  subst hAB; rfl

noncomputable def quotientMulEquivOfSupOfInf {J H H0 F : Subgroup M} [J.Normal] [H0.Normal]
    (hinf : J ⊓ H = H0) (hsup : J ⊔ H = F) :
    F ⧸ J.subgroupOf F ≃* H ⧸ H0.subgroupOf H :=
  (quotientSubgroupOfCongr hsup J).symm.trans
    ((quotientInfEquivSupQuotient J H).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (congrArg (fun X : Subgroup M => X.subgroupOf H) hinf)))

theorem quotientMulEquivOfSupOfInf_mk {J H H0 F : Subgroup M} [J.Normal] [H0.Normal]
    (hinf : J ⊓ H = H0) (hsup : J ⊔ H = F) (x : M) (hx : x ∈ H) :
    quotientMulEquivOfSupOfInf hinf hsup
        (QuotientGroup.mk ⟨x, hsup ▸ (le_sup_right : H ≤ J ⊔ H) hx⟩) =
      QuotientGroup.mk ⟨x, hx⟩ := by
  rw [quotientMulEquivOfSupOfInf, MulEquiv.trans_apply, MulEquiv.trans_apply,
    quotientSubgroupOfCongr_symm_mk]
  rw [show (⟨x, hsup ▸ (le_sup_right : H ≤ J ⊔ H) hx⟩ : (J ⊔ H : Subgroup M)) =
      Subgroup.inclusion (le_sup_right : H ≤ J ⊔ H) ⟨x, hx⟩ from rfl,
    quotientInfEquivSupQuotient_symm_mk]
  subst hinf
  rfl

structure IsPrescribedFitting (H U K F C : Subgroup M) : Prop where
  normal_H : H.Normal
  coprime_index_H : (Nat.card H).Coprime H.index
  sup_H_U : H ⊔ U = K
  disjoint_H_U : Disjoint H U
  normal_F : F.Normal
  nilpotent_F : Group.IsNilpotent F
  le_H_F : H ≤ F
  eq_F : F = H ⊔ Subgroup.centralizer (H : Set M)
  le_F_K : F ≤ K
  eq_C : C = U ⊓ Subgroup.centralizer (H : Set M)

namespace IsPrescribedFitting

variable {H U K F C : Subgroup M} (h : IsPrescribedFitting H U K F C)

include h

theorem coprime_natCard_U : (Nat.card ↥H).Coprime (Nat.card ↥U) := by
  have := h.normal_H
  exact h.coprime_index_H.coprime_dvd_right (natCard_dvd_index_of_disjoint H U h.disjoint_H_U)

theorem centralizer_le_F : Subgroup.centralizer (H : Set M) ≤ F := by
  rw [h.eq_F]; exact le_sup_right

theorem sup_inf_F_eq : H ⊔ (U ⊓ F) = F := by
  have := h.normal_H
  exact sup_inf_eq_of_normal_of_le h.le_H_F (h.sup_H_U ▸ h.le_F_K)

theorem inf_F_le_centralizer : U ⊓ F ≤ Subgroup.centralizer (H : Set M) := by
  have := h.nilpotent_F
  have hle : U ⊓ F ≤ F := inf_le_right
  have h1 : Nat.card ↥(H.subgroupOf F) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_H_F).toEquiv
  have h2 : Nat.card ↥((U ⊓ F).subgroupOf F) = Nat.card ↥(U ⊓ F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hcop : (Nat.card ↥(H.subgroupOf F)).Coprime (Nat.card ↥((U ⊓ F).subgroupOf F)) := by
    rw [h1, h2]
    exact h.coprime_natCard_U.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact congrArg Subtype.val (commute_of_coprime_natCard (X := F) (R := H.subgroupOf F)
    (S := (U ⊓ F).subgroupOf F) hcop (r := ⟨g, h.le_H_F hg⟩)
    (s := ⟨x, (Subgroup.mem_inf.1 hx).2⟩)
    (Subgroup.mem_subgroupOf.2 hg) (Subgroup.mem_subgroupOf.2 hx))

theorem eq_inf_F : C = U ⊓ F := by
  rw [h.eq_C]
  exact le_antisymm (le_inf inf_le_left (inf_le_right.trans h.centralizer_le_F))
    (le_inf inf_le_left h.inf_F_le_centralizer)

theorem C_le_centralizer : C ≤ Subgroup.centralizer (H : Set M) := by
  rw [h.eq_C]; exact inf_le_right

theorem C_le_U : C ≤ U := by rw [h.eq_C]; exact inf_le_left

theorem C_le_F : C ≤ F := h.eq_inf_F ▸ inf_le_right

theorem commute_of_mem {x y : M} (hx : x ∈ H) (hy : y ∈ C) : Commute x y :=
  Subgroup.mem_centralizer_iff.1 (h.C_le_centralizer hy) x hx

theorem sup_C_eq_F : H ⊔ C = F := by rw [h.eq_inf_F]; exact h.sup_inf_F_eq

theorem commutator_eq_bot : ⁅H, C⁆ = ⊥ :=
  eq_bot_iff.mpr <| Subgroup.commutator_le.mpr fun _ hx _ hy =>
    Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_commute.mpr (h.commute_of_mem hx hy))

theorem disjoint_H_C : Disjoint H C := h.disjoint_H_U.mono_right h.C_le_U

theorem inf_H_C : H ⊓ C = ⊥ := disjoint_iff.1 h.disjoint_H_C

theorem coe_F_eq_mul : (F : Set M) = (H : Set M) * (C : Set M) := by
  rw [← h.sup_C_eq_F]
  exact coe_sup_eq_mul_of_commute fun _ hx _ hy => h.commute_of_mem hx hy

noncomputable def prodMulEquivF : (H × C) ≃* F :=
  mulEquivProdOfCoeEqMul h.coe_F_eq_mul h.inf_H_C fun _ hx _ hy => h.commute_of_mem hx hy

@[simp]
theorem coe_prodMulEquivF_apply (x : H × C) :
    ((h.prodMulEquivF x : F) : M) = (x.1 : M) * (x.2 : M) :=
  coe_mulEquivProdOfCoeEqMul_apply _ _ _ x

theorem coprime_natCard_C : (Nat.card ↥H).Coprime (Nat.card ↥C) :=
  h.coprime_natCard_U.coprime_dvd_right (Subgroup.card_dvd_of_le h.C_le_U)

theorem mem_C_iff {x : M} : x ∈ C ↔ x ∈ F ∧ x ^ Nat.card ↥C = 1 := by
  constructor
  · intro hx
    exact ⟨h.C_le_F hx, congrArg Subtype.val (pow_card_eq_one' (G := C) (x := ⟨x, hx⟩))⟩
  · rintro ⟨hxF, hpow⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := (h.coe_F_eq_mul ▸ hxF : x ∈ (H : Set M) * (C : Set M))
    have hcpow : c ^ Nat.card ↥C = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := C) (x := ⟨c, hc⟩))
    have ha1 : a ^ Nat.card ↥C = 1 := by
      have hmp := (h.commute_of_mem ha hc).mul_pow (Nat.card ↥C)
      rw [hpow, hcpow, mul_one] at hmp
      exact hmp.symm
    have : a = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h.coprime_natCard_C
      (Subgroup.orderOf_dvd_natCard _ ha) (orderOf_dvd_of_pow_eq_one ha1))
    simpa [this] using hc

theorem normal_C : C.Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨hxF, hpow⟩ := h.mem_C_iff.1 hx
  refine h.mem_C_iff.2 ⟨h.normal_F.conj_mem x hxF g, ?_⟩
  rw [conj_pow, hpow, mul_one, mul_inv_cancel]

section Core

variable {H0 : Subgroup M} [H0.Normal] (hH0H : H0 ≤ H)

theorem normal_sup_C : (H0 ⊔ C).Normal :=
  haveI := h.normal_C; Subgroup.sup_normal H0 C

include hH0H

theorem commutator_H0_C : ⁅H0, C⁆ = ⊥ :=
  eq_bot_iff.mpr <| Subgroup.commutator_le.mpr fun _ hx _ hy =>
    Subgroup.mem_bot.mpr
      (commutatorElement_eq_one_iff_commute.mpr (h.commute_of_mem (hH0H hx) hy))

theorem disjoint_H0_C : Disjoint H0 C := h.disjoint_H_C.mono_left hH0H

theorem inf_H0_C : H0 ⊓ C = ⊥ := disjoint_iff.1 (h.disjoint_H0_C hH0H)

theorem coe_sup_C_eq_mul : ((H0 ⊔ C : Subgroup M) : Set M) = (H0 : Set M) * (C : Set M) :=
  coe_sup_eq_mul_of_commute fun _ hx _ hy => h.commute_of_mem (hH0H hx) hy

noncomputable def prodMulEquivSupC : (H0 × C) ≃* (H0 ⊔ C : Subgroup M) :=
  mulEquivProdOfCoeEqMul (h.coe_sup_C_eq_mul hH0H) (h.inf_H0_C hH0H)
    fun _ hx _ hy => h.commute_of_mem (hH0H hx) hy

@[simp]
theorem coe_prodMulEquivSupC_apply (x : H0 × C) :
    ((h.prodMulEquivSupC hH0H x : (H0 ⊔ C : Subgroup M)) : M) = (x.1 : M) * (x.2 : M) :=
  coe_mulEquivProdOfCoeEqMul_apply _ _ _ x

theorem inf_sup_C_H : (H0 ⊔ C) ⊓ H = H0 := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hH0H)
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨a, ha, c, hc, rfl⟩ :=
    ((h.coe_sup_C_eq_mul hH0H) ▸ hx1 : x ∈ (H0 : Set M) * (C : Set M))
  have hcH : c ∈ H := by simpa using H.mul_mem (H.inv_mem (hH0H ha)) hx2
  have : c = 1 := by simpa [h.inf_H_C] using Subgroup.mem_inf.2 ⟨hcH, hc⟩
  simpa [this] using ha

theorem sup_sup_C_H : (H0 ⊔ C) ⊔ H = F := by
  rw [sup_assoc, sup_comm C H, ← sup_assoc, sup_eq_right.2 hH0H, h.sup_C_eq_F]

noncomputable def quotientSupCMulEquiv :
    letI : ((H0 ⊔ C).subgroupOf F).Normal := (h.normal_sup_C (H0 := H0)).subgroupOf F
    F ⧸ (H0 ⊔ C).subgroupOf F ≃* H ⧸ H0.subgroupOf H :=
  letI := h.normal_sup_C (H0 := H0)
  quotientMulEquivOfSupOfInf (h.inf_sup_C_H hH0H) (h.sup_sup_C_H hH0H)

theorem quotientSupCMulEquiv_mk (x : M) (hx : x ∈ H) :
    letI : ((H0 ⊔ C).subgroupOf F).Normal := (h.normal_sup_C (H0 := H0)).subgroupOf F
    h.quotientSupCMulEquiv hH0H (QuotientGroup.mk ⟨x, h.le_H_F hx⟩) =
      QuotientGroup.mk ⟨x, hx⟩ := by
  letI := h.normal_sup_C (H0 := H0)
  exact quotientMulEquivOfSupOfInf_mk (h.inf_sup_C_H hH0H) (h.sup_sup_C_H hH0H) x hx

end Core

end IsPrescribedFitting

end

end CFSG.FeitThompson
