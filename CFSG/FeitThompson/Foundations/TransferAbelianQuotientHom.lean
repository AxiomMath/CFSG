module

public import CFSG.FeitThompson.Foundations.CosetRepresentativeMultiplication
public import Mathlib.GroupTheory.Transfer

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {G : Type*} [Group G] {P : Subgroup G} {T : Set G} {Q : Type*} [CommGroup Q]

theorem isComplement_inv {S T : Set G} (h : IsComplement S T) : IsComplement T⁻¹ S⁻¹ := by
  rw [isComplement_iff_existsUnique] at h ⊢
  intro g
  obtain ⟨⟨s, t⟩, h1, h2⟩ := h g⁻¹
  refine ⟨⟨⟨(t : G)⁻¹, Set.inv_mem_inv.2 t.2⟩, ⟨(s : G)⁻¹, Set.inv_mem_inv.2 s.2⟩⟩, ?_, ?_⟩
  · change (t : G)⁻¹ * (s : G)⁻¹ = g
    rw [← mul_inv_rev, h1, inv_inv]
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hab
    change a * b = g at hab
    have key : (⟨⟨b⁻¹, Set.mem_inv.1 hb⟩, ⟨a⁻¹, Set.mem_inv.1 ha⟩⟩ : S × T) = (s, t) := by
      refine h2 _ ?_
      change b⁻¹ * a⁻¹ = g⁻¹
      rw [← mul_inv_rev, hab]
    have hb' : b⁻¹ = (s : G) := congrArg Subtype.val (congrArg Prod.fst key)
    have ha' : a⁻¹ = (t : G) := congrArg Subtype.val (congrArg Prod.snd key)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change a = (t : G)⁻¹; rw [← ha', inv_inv]
    · change b = (s : G)⁻¹; rw [← hb', inv_inv]

theorem isComplement_inv_left (hT : IsComplement (P : Set G) T) :
    IsComplement T⁻¹ (P : Set G) := by
  have h := isComplement_inv hT
  rwa [inv_coe_set] at h

theorem coe_leftQuotientEquiv_eq_of {S : Set G} (hS : IsComplement S (P : Set G)) {q : G ⧸ P}
    {s : S} (h : (QuotientGroup.mk (s : G) : G ⧸ P) = q) :
    (hS.leftQuotientEquiv q : G) = (s : G) :=
  congrArg Subtype.val (h ▸ hS.leftQuotientEquiv.eq_symm_apply.1 (rfl))

noncomputable def transversalQuotientEquiv (hT : IsComplement (P : Set G) T) : T ≃ G ⧸ P where
  toFun t := QuotientGroup.mk (t : G)⁻¹
  invFun q := ⟨((isComplement_inv_left hT).leftQuotientEquiv q : G)⁻¹,
    Set.mem_inv.1 ((isComplement_inv_left hT).leftQuotientEquiv q).2⟩
  left_inv t := Subtype.ext (by
    change (((isComplement_inv_left hT).leftQuotientEquiv
      (QuotientGroup.mk (t : G)⁻¹) : G))⁻¹ = (t : G)
    rw [coe_leftQuotientEquiv_eq_of (s := ⟨(t : G)⁻¹, Set.inv_mem_inv.2 t.2⟩) _ (rfl), inv_inv])
  right_inv q := by
    simp only [inv_inv]
    exact (isComplement_inv_left hT).quotientGroupMk_leftQuotientEquiv q

@[simp]
theorem transversalQuotientEquiv_apply (hT : IsComplement (P : Set G) T) (t : T) :
    transversalQuotientEquiv hT t = QuotientGroup.mk (t : G)⁻¹ := (rfl)

@[simp]
theorem coe_transversalQuotientEquiv_symm (hT : IsComplement (P : Set G) T) (q : G ⧸ P) :
    (((transversalQuotientEquiv hT).symm q : T) : G)
      = ((isComplement_inv_left hT).leftQuotientEquiv q : G)⁻¹ := (rfl)

theorem transversalTransfer_eq_transfer [P.FiniteIndex] (hT : IsComplement (P : Set G) T)
    (f : P →* Q) (g : G) : transversalTransfer hT f g = f.transfer g := by
  have hTinv := isComplement_inv_left hT
  have hfin : Finite T := Nat.finite_of_card_ne_zero
    (by rw [hT.card_right]; exact P.index_ne_zero_of_finite)
  have : Fintype T := Fintype.ofFinite T
  let _ : Fintype (G ⧸ P) := Subgroup.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_def f ⟨T⁻¹, hTinv⟩, Subgroup.leftTransversals.diff,
    transversalTransfer_eq_prod]
  refine Fintype.prod_equiv (transversalQuotientEquiv hT)
    (fun t => f (transversalCocycle hT t g)) _ ?_
  intro t
  congr 1
  apply Subtype.ext
  have h1 : (((⟨T⁻¹, hTinv⟩ : P.LeftTransversal).2.leftQuotientEquiv
      (QuotientGroup.mk (t : G)⁻¹) : G)) = (t : G)⁻¹ :=
    coe_leftQuotientEquiv_eq_of (s := ⟨(t : G)⁻¹, Set.inv_mem_inv.2 t.2⟩) _ (rfl)
  have hmem : g * (transversalAct hT t g : G)⁻¹ ∈ g • T⁻¹ :=
    ⟨(transversalAct hT t g : G)⁻¹, Set.inv_mem_inv.2 (transversalAct hT t g).2, rfl⟩
  have h2 : (((g • (⟨T⁻¹, hTinv⟩ : P.LeftTransversal)).2.leftQuotientEquiv
      (QuotientGroup.mk (t : G)⁻¹) : G)) = g * (transversalAct hT t g : G)⁻¹ := by
    refine coe_leftQuotientEquiv_eq_of (s := ⟨g * (transversalAct hT t g : G)⁻¹, hmem⟩) _ ?_
    rw [QuotientGroup.eq]
    have hmem2 := mul_mul_transversalAct_inv_mem hT t g
    simpa [mul_assoc] using P.inv_mem hmem2
  simp only [coe_transversalCocycle, transversalQuotientEquiv_apply, h1, h2]
  group

theorem transversalTransferHom_eq_transfer [P.FiniteIndex] [Finite T]
    (hT : IsComplement (P : Set G) T) (f : P →* Q) : transversalTransferHom hT f = f.transfer :=
  MonoidHom.ext fun g => by
    rw [transversalTransferHom_apply, transversalTransfer_eq_transfer]

end CFSG.FeitThompson
