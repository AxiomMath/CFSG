module

public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup

variable {L : Type*} [Group L]

theorem le_normalizer_of_forall_map_conj_le {A S : Subgroup L}
    (h : ∀ a ∈ A, Subgroup.map (MulAut.conj a) S ≤ S) : A ≤ normalizer (S : Set L) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (h a ha) fun s hs => ⟨a⁻¹ * s * a, h a⁻¹ (A.inv_mem ha) ⟨s, hs, ?_⟩, ?_⟩
  · change a⁻¹ * s * a⁻¹⁻¹ = a⁻¹ * s * a; group
  · change a * (a⁻¹ * s * a) * a⁻¹ = s; group

theorem le_normalizer_of_normal (A : Subgroup L) (N : Subgroup L) [N.Normal] :
    A ≤ normalizer (N : Set L) := by rw [Subgroup.normalizer_eq_top]; exact le_top

theorem le_normalizer_sup {A X Y : Subgroup L} (hX : A ≤ normalizer (X : Set L))
    (hY : A ≤ normalizer (Y : Set L)) : A ≤ normalizer ((X ⊔ Y : Subgroup L) : Set L) := by
  refine le_normalizer_of_forall_map_conj_le fun a ha => ?_
  rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hX ha),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hY ha)]

theorem le_normalizer_inf {A X Y : Subgroup L} (hX : A ≤ normalizer (X : Set L))
    (hY : A ≤ normalizer (Y : Set L)) : A ≤ normalizer ((X ⊓ Y : Subgroup L) : Set L) :=
  Subgroup.le_normalizer_iff.mpr fun _ ha _ hc =>
    ⟨Subgroup.le_normalizer_iff.mp hX _ ha _ hc.1, Subgroup.le_normalizer_iff.mp hY _ ha _ hc.2⟩

theorem le_normalizer_commutator_self {A S : Subgroup L} (h : A ≤ normalizer (S : Set L)) :
    A ≤ normalizer ((⁅S, S⁆ : Subgroup L) : Set L) := by
  refine le_normalizer_of_forall_map_conj_le fun a ha => ?_
  rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp (h ha)]

theorem commutator_self_le (X : Subgroup L) : ⁅X, X⁆ ≤ X :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    simpa [commutatorElement_def] using
      mul_mem (mul_mem (mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)

theorem normal_subgroupOf_of_le_normalizer_set {A S : Subgroup L} (hSA : S ≤ A)
    (h : A ≤ normalizer (S : Set L)) : (S.subgroupOf A).Normal :=
  (Subgroup.normal_subgroupOf_iff hSA).mpr fun s a hs ha =>
    Subgroup.le_normalizer_iff.mp h a ha s hs

def quotSubgroupOfMap {A B X Y : Subgroup L} [(X.subgroupOf A).Normal] [(Y.subgroupOf B).Normal]
    (hAB : A ≤ B) (hXY : X ≤ Y) : ↥A ⧸ X.subgroupOf A →* ↥B ⧸ Y.subgroupOf B :=
  QuotientGroup.map _ _ (Subgroup.inclusion hAB) fun _ hx => hXY (Subgroup.mem_subgroupOf.mp hx)

@[simp]
theorem quotSubgroupOfMap_mk {A B X Y : Subgroup L} [(X.subgroupOf A).Normal]
    [(Y.subgroupOf B).Normal] (hAB : A ≤ B) (hXY : X ≤ Y) (a : ↥A) :
    quotSubgroupOfMap hAB hXY (QuotientGroup.mk a) =
      QuotientGroup.mk (Subgroup.inclusion hAB a) := (rfl)

theorem quotSubgroupOfMap_injective {A B X Y : Subgroup L} [(X.subgroupOf A).Normal]
    [(Y.subgroupOf B).Normal] (hAB : A ≤ B) (hXY : X ≤ Y) (h : Y ⊓ A ≤ X) :
    Function.Injective (quotSubgroupOfMap hAB hXY) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  induction z using QuotientGroup.induction_on with
  | _ a =>
    rw [quotSubgroupOfMap_mk] at hz
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hz ⊢
    exact h ⟨hz, a.2⟩

theorem range_quotSubgroupOfMap {A B X Y : Subgroup L} [(X.subgroupOf A).Normal]
    [(Y.subgroupOf B).Normal] (hAB : A ≤ B) (hXY : X ≤ Y) :
    (quotSubgroupOfMap hAB hXY).range =
      (A.subgroupOf B).map (QuotientGroup.mk' (Y.subgroupOf B)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    induction w using QuotientGroup.induction_on with
    | _ a => exact ⟨Subgroup.inclusion hAB a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact ⟨QuotientGroup.mk ⟨(b : L), Subgroup.mem_subgroupOf.mp hb⟩, rfl⟩

section Lift
variable {N V Q : Type*} [Group N] [Group V] [Group Q] {φ : V →* MulAut N}

theorem semidirectLift_apply (fn : N →* Q) (fg : V →* Q)
    (hc : ∀ g : V, fn.comp (φ g).toMonoidHom = (MulAut.conj (fg g)).toMonoidHom.comp fn)
    (x : N ⋊[φ] V) : SemidirectProduct.lift fn fg hc x = fn x.left * fg x.right := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
  rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]

theorem semidirectLift_range (fn : N →* Q) (fg : V →* Q)
    (hc : ∀ g : V, fn.comp (φ g).toMonoidHom = (MulAut.conj (fg g)).toMonoidHom.comp fn) :
    (SemidirectProduct.lift fn fg hc).range = fn.range ⊔ fg.range := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨x, rfl⟩
    rw [semidirectLift_apply]
    exact mul_mem (le_sup_left (α := Subgroup Q) ⟨x.left, rfl⟩)
      (le_sup_right (α := Subgroup Q) ⟨x.right, rfl⟩)
  · rintro _ ⟨n, rfl⟩; exact ⟨SemidirectProduct.inl n, SemidirectProduct.lift_inl _ _ _ n⟩
  · rintro _ ⟨g, rfl⟩; exact ⟨SemidirectProduct.inr g, SemidirectProduct.lift_inr _ _ _ g⟩

theorem semidirectLift_bijective (fn : N →* Q) (fg : V →* Q)
    (hc : ∀ g : V, fn.comp (φ g).toMonoidHom = (MulAut.conj (fg g)).toMonoidHom.comp fn)
    (hn : Function.Injective fn) (hg : Function.Injective fg)
    (hdisj : Disjoint fn.range fg.range) (hsup : fn.range ⊔ fg.range = ⊤) :
    Function.Bijective (SemidirectProduct.lift fn fg hc) := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun x hx => ?_, ?_⟩
  · rw [semidirectLift_apply] at hx
    have h1 : fn x.left ∈ fn.range ⊓ fg.range :=
      ⟨⟨x.left, rfl⟩, ⟨x.right⁻¹, by rw [map_inv, ← mul_eq_one_iff_eq_inv.mp hx]⟩⟩
    rw [hdisj.eq_bot] at h1
    have hl : x.left = 1 := hn (by simpa using h1)
    have hr : fg x.right = 1 := by rw [hl, map_one, one_mul] at hx; exact hx
    exact SemidirectProduct.ext hl (hg (by simpa using hr))
  · rw [← MonoidHom.range_eq_top, semidirectLift_range, hsup]

end Lift

theorem map_conjNormal_subgroupOf (H H0 : Subgroup L) [H.Normal] [H0.Normal] (x : L) :
    Subgroup.map (↑(MulAut.conjNormal x : MulAut ↥H)) (H0.subgroupOf H) = H0.subgroupOf H := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  refine ⟨?_, fun hy => ⟨⟨x⁻¹ * y * x, by simpa using ‹H.Normal›.conj_mem _ y.2 x⁻¹⟩,
    by simpa using ‹H0.Normal›.conj_mem _ hy x⁻¹,
    by ext; simp [MulAut.conjNormal_apply, mul_assoc]⟩⟩
  rintro ⟨z, hz, rfl⟩
  simpa [MulAut.conjNormal_apply] using ‹H0.Normal›.conj_mem _ hz x

def conjQuotientAut (H H0 : Subgroup L) [H.Normal] [H0.Normal] :
    L →* MulAut (↥H ⧸ H0.subgroupOf H) :=
  MonoidHom.mk' (fun x => QuotientGroup.congr _ _ (MulAut.conjNormal x)
      (map_conjNormal_subgroupOf H H0 x)) <| by
    intro x y
    refine MulEquiv.ext fun z => ?_
    induction z using QuotientGroup.induction_on with
    | _ h =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply]

@[simp]
theorem conjQuotientAut_apply_mk (H H0 : Subgroup L) [H.Normal] [H0.Normal] (x : L) (h : ↥H) :
    conjQuotientAut H H0 x (QuotientGroup.mk h) =
      QuotientGroup.mk (MulAut.conjNormal x h) := (rfl)

variable (H H0 U : Subgroup L) [H.Normal] [H0.Normal]

theorem mem_ker_conjQuotientAut {x : L} :
    x ∈ (conjQuotientAut H H0).ker ↔ ∀ h ∈ H, h⁻¹ * (x⁻¹ * h * x) ∈ H0 := by
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hx h hh
    have := congrArg (fun e : MulAut _ => e (QuotientGroup.mk (⟨h, hh⟩ : ↥H))) hx
    simp only [conjQuotientAut_apply_mk, MulAut.one_apply] at this
    rw [QuotientGroup.eq] at this
    simp only [Subgroup.mem_subgroupOf, InvMemClass.coe_inv, Subgroup.coe_mul,
      MulAut.conjNormal_apply] at this
    simpa [mul_assoc] using ‹H0.Normal›.conj_mem _ this x⁻¹
  · intro hx
    refine MulEquiv.ext fun z => ?_
    induction z using QuotientGroup.induction_on with
    | _ h =>
      rw [conjQuotientAut_apply_mk, MulAut.one_apply, QuotientGroup.eq]
      simp only [Subgroup.mem_subgroupOf, InvMemClass.coe_inv, Subgroup.coe_mul,
        MulAut.conjNormal_apply]
      simpa [mul_assoc] using ‹H0.Normal›.conj_mem _ (hx h h.2) x

theorem conj_mul_inv_mem_H0 {x : L} (hx : x ∈ (conjQuotientAut H H0).ker)
    {h : L} (hh : h ∈ H) : h * x * h⁻¹ * x⁻¹ ∈ H0 := by
  simpa [mul_assoc] using
    (mem_ker_conjQuotientAut H H0).mp ((conjQuotientAut H H0).ker.inv_mem hx) h⁻¹ (H.inv_mem hh)

theorem map_conj_le_sup_of_le_ker {D : Subgroup L} (hD : D ≤ (conjQuotientAut H H0).ker)
    {h : L} (hh : h ∈ H) : Subgroup.map (MulAut.conj h) D ≤ H0 ⊔ D := by
  rintro _ ⟨d, hd, rfl⟩
  have h1 : h * d * h⁻¹ * d⁻¹ ∈ H0 := conj_mul_inv_mem_H0 H H0 (hD hd) hh
  have h2 : (MulAut.conj h : L →* L) d = h * d * h⁻¹ * d⁻¹ * d := by
    change h * d * h⁻¹ = _; group
  rw [h2]
  exact mul_mem (le_sup_left (α := Subgroup L) h1) (le_sup_right (α := Subgroup L) hd)

def chiefActionKer : Subgroup L := U ⊓ (conjQuotientAut H H0).ker

theorem chiefActionKer_eq_inf : chiefActionKer H H0 U = U ⊓ (conjQuotientAut H H0).ker := (rfl)

theorem mem_chiefActionKer_iff {u : L} :
    u ∈ chiefActionKer H H0 U ↔
      u ∈ U ∧ ∀ h ∈ H, ((u⁻¹ * h * u : L) : L ⧸ H0) = (h : L ⧸ H0) := by
  rw [chiefActionKer_eq_inf, Subgroup.mem_inf, mem_ker_conjQuotientAut]
  exact and_congr_right fun _ => forall₂_congr fun _ _ => by rw [eq_comm, QuotientGroup.eq]

theorem mem_chiefActionKer_iff_mem_ker {u : L} :
    u ∈ chiefActionKer H H0 U ↔ u ∈ U ∧ u ∈ (conjQuotientAut H H0).ker := by
  rw [chiefActionKer_eq_inf, Subgroup.mem_inf]

theorem chiefActionKer_le : chiefActionKer H H0 U ≤ U := inf_le_left

theorem chiefActionKer_le_ker :
    chiefActionKer H H0 U ≤ (conjQuotientAut H H0).ker := inf_le_right

theorem commutator_le_chiefActionKer
    (hab : IsMulCommutative (Subgroup.map (conjQuotientAut H H0) U)) :
    ⁅U, U⁆ ≤ chiefActionKer H H0 U := by
  rw [chiefActionKer_eq_inf, le_inf_iff]
  refine ⟨commutator_self_le U, Subgroup.commutator_le.mpr fun a ha b hb => ?_⟩
  have h2 : conjQuotientAut H H0 a * conjQuotientAut H H0 b
      = conjQuotientAut H H0 b * conjQuotientAut H H0 a :=
    congrArg Subtype.val (hab.is_comm.comm (⟨conjQuotientAut H H0 a, ⟨a, ha, rfl⟩⟩ :
      Subgroup.map (conjQuotientAut H H0) U) ⟨conjQuotientAut H H0 b, ⟨b, hb, rfl⟩⟩)
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
    h2, mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]

theorem le_normalizer_chiefActionKer {A : Subgroup L} (hA : A ≤ normalizer (U : Set L)) :
    A ≤ normalizer ((chiefActionKer H H0 U : Subgroup L) : Set L) := by
  rw [chiefActionKer_eq_inf]
  exact le_normalizer_inf hA (le_normalizer_of_normal _ _)

theorem chiefActionKer_normal_subgroupOf_sup (B : Subgroup L)
    (hBU : B ≤ normalizer (U : Set L)) :
    ((chiefActionKer H H0 U).subgroupOf (U ⊔ B)).Normal :=
  normal_subgroupOf_of_le_normalizer_set ((chiefActionKer_le H H0 U).trans le_sup_left)
    (sup_le (le_normalizer_chiefActionKer H H0 U Subgroup.le_normalizer)
      (le_normalizer_chiefActionKer H H0 U hBU))

theorem normal_sup_of_le_ker_of_le_normalizer {A X Y : Subgroup L} [Y.Normal]
    (hH0Y : H0 ≤ Y) (hXker : X ≤ (conjQuotientAut H H0).ker)
    (hAX : A ≤ normalizer (X : Set L)) (hL : H ⊔ A = ⊤) : (Y ⊔ X).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hL]
  refine sup_le (le_normalizer_of_forall_map_conj_le fun h hh => ?_)
    (le_normalizer_sup (le_normalizer_of_normal _ _) hAX)
  rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (le_normalizer_of_normal (⊤ : Subgroup L) Y (Subgroup.mem_top h))]
  exact sup_le le_sup_left ((map_conj_le_sup_of_le_ker H H0 hXker hh).trans
    (sup_le (le_sup_left.trans' hH0Y) le_sup_right))

section Normality

variable (B : Subgroup L)

theorem normal_sup_of_le_ker (hL : H ⊔ (U ⊔ B) = ⊤) {X Y : Subgroup L} [Y.Normal] (hH0Y : H0 ≤ Y)
    (hXker : X ≤ (conjQuotientAut H H0).ker) (hUBX : U ⊔ B ≤ normalizer (X : Set L)) :
    (Y ⊔ X).Normal :=
  normal_sup_of_le_ker_of_le_normalizer H H0 hH0Y hXker hUBX hL

theorem sup_le_normalizer_chiefActionKer (hBU : B ≤ normalizer (U : Set L)) :
    U ⊔ B ≤ normalizer ((chiefActionKer H H0 U : Subgroup L) : Set L) :=
  le_normalizer_chiefActionKer H H0 U (sup_le Subgroup.le_normalizer hBU)

variable (hBU : B ≤ normalizer (U : Set L)) (hL : H ⊔ (U ⊔ B) = ⊤)
include hBU hL

theorem normal_sup_chiefActionKer (hH0H : H0 ≤ H) : (H ⊔ chiefActionKer H H0 U).Normal :=
  normal_sup_of_le_ker H H0 U B hL hH0H (chiefActionKer_le_ker H H0 U)
    (sup_le_normalizer_chiefActionKer H H0 U B hBU)

theorem normal_sup_H0_chiefActionKer : (H0 ⊔ chiefActionKer H H0 U).Normal :=
  normal_sup_of_le_ker H H0 U B hL le_rfl (chiefActionKer_le_ker H H0 U)
    (sup_le_normalizer_chiefActionKer H H0 U B hBU)

theorem normal_sup_H0_commutator_chiefActionKer :
    (H0 ⊔ ⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).Normal :=
  normal_sup_of_le_ker H H0 U B hL le_rfl
    ((commutator_self_le _).trans (chiefActionKer_le_ker H H0 U))
    (le_normalizer_commutator_self (sup_le_normalizer_chiefActionKer H H0 U B hBU))

theorem normal_sup_H0_commutator_U
    (hab : IsMulCommutative (Subgroup.map (conjQuotientAut H H0) U)) :
    (H0 ⊔ ⁅U, U⁆).Normal :=
  normal_sup_of_le_ker H H0 U B hL le_rfl
    ((commutator_le_chiefActionKer H H0 U hab).trans (chiefActionKer_le_ker H H0 U))
    (le_normalizer_commutator_self (sup_le Subgroup.le_normalizer hBU))

end Normality

section Quotient

variable {S K : Subgroup L}

def quotConjAut [(S.subgroupOf U).Normal] (hS : S ≤ (conjQuotientAut H H0).ker) :
    (↥U ⧸ S.subgroupOf U) →* MulAut (↥H ⧸ H0.subgroupOf H) :=
  QuotientGroup.lift _ ((conjQuotientAut H H0).comp U.subtype)
    fun _ hu => hS (Subgroup.mem_subgroupOf.mp hu)

@[simp]
theorem quotConjAut_mk [(S.subgroupOf U).Normal] (hS : S ≤ (conjQuotientAut H H0).ker) (u : ↥U) :
    quotConjAut H H0 U hS (QuotientGroup.mk u) = conjQuotientAut H H0 (u : L) := (rfl)

theorem ker_quotConjAut [(S.subgroupOf U).Normal] (hS : S ≤ (conjQuotientAut H H0).ker) :
    (quotConjAut H H0 U hS).ker = ((chiefActionKer H H0 U).subgroupOf U).map
      (QuotientGroup.mk' (S.subgroupOf U)) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | _ u =>
    constructor
    · intro hz
      refine ⟨u, Subgroup.mem_subgroupOf.mpr
        ((mem_chiefActionKer_iff_mem_ker H H0 U).mpr ⟨u.2, ?_⟩), rfl⟩
      rw [MonoidHom.mem_ker, ← quotConjAut_mk H H0 U hS u]
      exact hz
    · rintro ⟨v, hv, hvz⟩
      have hv' := (mem_chiefActionKer_iff_mem_ker H H0 U).mp (Subgroup.mem_subgroupOf.mp hv)
      have h : QuotientGroup.mk (s := S.subgroupOf U) v = QuotientGroup.mk u := hvz
      rw [MonoidHom.mem_ker, ← h, quotConjAut_mk]
      exact hv'.2

theorem isMulCommutative_map_mk'_of_commutator_le {X S' : Subgroup L}
    [(S'.subgroupOf U).Normal] (h : ⁅X, X⁆ ≤ S') :
    IsMulCommutative ((X.subgroupOf U).map (QuotientGroup.mk' (S'.subgroupOf U))) := by
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨a, ha, hax⟩ := x.2
  obtain ⟨b, hb, hby⟩ := y.2
  have ha' := Subgroup.mem_subgroupOf.mp ha
  have hb' := Subgroup.mem_subgroupOf.mp hb
  have hax' : (QuotientGroup.mk a : ↥U ⧸ S'.subgroupOf U) = (x : _) := hax
  have hby' : (QuotientGroup.mk b : ↥U ⧸ S'.subgroupOf U) = (y : _) := hby
  have hmem := h (Subgroup.commutator_mem_commutator (X.inv_mem hb') (X.inv_mem ha'))
  rw [commutatorElement_def] at hmem
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax', ← hby',
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  push_cast
  convert hmem using 1
  group

theorem isMulCommutative_ker_quotConjAut_commutator
    [((⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf U).Normal]
    (hS : (⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆ : Subgroup L)
      ≤ (conjQuotientAut H H0).ker) :
    IsMulCommutative (quotConjAut H H0 U hS).ker := by
  rw [ker_quotConjAut]
  exact isMulCommutative_map_mk'_of_commutator_le U
    (X := chiefActionKer H H0 U) (S' := ⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆) le_rfl

def toQuotSemidirect [(S.subgroupOf U).Normal] [((H0 ⊔ S).subgroupOf K).Normal]
    (hS : S ≤ (conjQuotientAut H H0).ker) (hHK : H ≤ K) (hUK : U ≤ K) :
    (↥H ⧸ H0.subgroupOf H) ⋊[quotConjAut H H0 U hS] (↥U ⧸ S.subgroupOf U) →*
      ↥K ⧸ (H0 ⊔ S).subgroupOf K :=
  SemidirectProduct.lift (quotSubgroupOfMap hHK (le_sup_left : H0 ≤ H0 ⊔ S))
    (quotSubgroupOfMap hUK (le_sup_right : S ≤ H0 ⊔ S))
    (by
      intro g
      induction g using QuotientGroup.induction_on with
      | _ u =>
        refine MonoidHom.ext fun z => ?_
        induction z using QuotientGroup.induction_on with
        | _ h =>
          simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
            quotConjAut_mk, conjQuotientAut_apply_mk, MulAut.conj_apply, quotSubgroupOfMap_mk,
            ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
          congr 1)

@[simp]
theorem toQuotSemidirect_inl [(S.subgroupOf U).Normal] [((H0 ⊔ S).subgroupOf K).Normal]
    (hS : S ≤ (conjQuotientAut H H0).ker) (hHK : H ≤ K) (hUK : U ≤ K)
    (x : ↥H ⧸ H0.subgroupOf H) :
    toQuotSemidirect H H0 U hS hHK hUK (SemidirectProduct.inl x) =
      quotSubgroupOfMap hHK (le_sup_left : H0 ≤ H0 ⊔ S) x :=
  SemidirectProduct.lift_inl _ _ _ x

@[simp]
theorem toQuotSemidirect_inr [(S.subgroupOf U).Normal] [((H0 ⊔ S).subgroupOf K).Normal]
    (hS : S ≤ (conjQuotientAut H H0).ker) (hHK : H ≤ K) (hUK : U ≤ K)
    (x : ↥U ⧸ S.subgroupOf U) :
    toQuotSemidirect H H0 U hS hHK hUK (SemidirectProduct.inr x) =
      quotSubgroupOfMap hUK (le_sup_right : S ≤ H0 ⊔ S) x :=
  SemidirectProduct.lift_inr _ _ _ x

theorem exists_mul_of_mem_sup_normal {N X : Subgroup L} [N.Normal] {x : L} (hx : x ∈ N ⊔ X) :
    ∃ a ∈ N, ∃ b ∈ X, a * b = x := by
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨a, ha, b, hb, rfl⟩

omit [H.Normal] in
theorem sup_inf_le_left_of_disjoint {H H0 U S : Subgroup L} [H0.Normal]
    (hH0H : H0 ≤ H) (hSU : S ≤ U) (hdisj : Disjoint H U) :
    (H0 ⊔ S) ⊓ H ≤ H0 := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_normal hx1
  have hbH : b ∈ H := by
    have : a⁻¹ * (a * b) ∈ H := mul_mem (H.inv_mem (hH0H ha)) hx2
    simpa [← mul_assoc] using this
  have hb1 : b = 1 := Subgroup.disjoint_def.mp hdisj hbH (hSU hb)
  simpa [hb1] using ha

omit [H.Normal] in
theorem sup_inf_le_right_of_disjoint {H H0 U S : Subgroup L} [H0.Normal]
    (hH0H : H0 ≤ H) (hSU : S ≤ U) (hdisj : Disjoint H U) :
    (H0 ⊔ S) ⊓ U ≤ S := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_normal hx1
  have haU : a ∈ U := by
    have : (a * b) * b⁻¹ ∈ U := mul_mem hx2 (U.inv_mem (hSU hb))
    simpa [mul_assoc] using this
  have ha1 : a = 1 := Subgroup.disjoint_def.mp hdisj (hH0H ha) haU
  simpa [ha1] using hb

omit [H.Normal] in
theorem disjoint_map_mk'_subgroupOf [((H0 ⊔ S).subgroupOf K).Normal]
    (hdisj : Disjoint H U) (hH0H : H0 ≤ H) (hSU : S ≤ U) :
    Disjoint ((H.subgroupOf K).map (QuotientGroup.mk' ((H0 ⊔ S).subgroupOf K)))
      ((U.subgroupOf K).map (QuotientGroup.mk' ((H0 ⊔ S).subgroupOf K))) := by
  rw [Subgroup.disjoint_def]
  intro z hz1 hz2
  induction z using QuotientGroup.induction_on with
  | _ k =>
    obtain ⟨a, ha, hak⟩ := hz1
    obtain ⟨b, hb, hbk⟩ := hz2
    have haH : (a : L) ∈ H := Subgroup.mem_subgroupOf.mp ha
    have hbU : (b : L) ∈ U := Subgroup.mem_subgroupOf.mp hb
    have heq : (a : ↥K)⁻¹ * b ∈ (H0 ⊔ S).subgroupOf K := by
      rw [← QuotientGroup.eq]; exact hak.trans hbk.symm
    have hab : ((a : L))⁻¹ * (b : L) ∈ H0 ⊔ S := by
      have := Subgroup.mem_subgroupOf.mp heq; push_cast at this; exact this
    obtain ⟨p, hp, q, hq, hpq⟩ := exists_mul_of_mem_sup_normal hab
    have hbeq : (b : L) = (a : L) * (p * q) := by rw [hpq]; group
    have h1 : (b : L) * q⁻¹ = (a : L) * p := by rw [hbeq]; group
    have h2 : (b : L) * q⁻¹ ∈ U := mul_mem hbU (U.inv_mem (hSU hq))
    have h3 : (a : L) * p ∈ H := mul_mem haH (hH0H hp)
    have h4 : (b : L) * q⁻¹ = 1 := Subgroup.disjoint_def.mp hdisj (h1 ▸ h3) h2
    have hbq : (b : L) = q := by rw [← mul_inv_eq_one (b := (q : L))]; exact h4
    have hk1 : (QuotientGroup.mk b : ↥K ⧸ (H0 ⊔ S).subgroupOf K) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hbq]
      exact le_sup_right (α := Subgroup L) hq
    rw [← hbk]; exact hk1

omit [H0.Normal] in
theorem sup_map_mk'_subgroupOf_eq_top (S : Subgroup L)
    [((H0 ⊔ S).subgroupOf K).Normal] (hsup : H ⊔ U = K) :
    ((H.subgroupOf K).map (QuotientGroup.mk' ((H0 ⊔ S).subgroupOf K)))
      ⊔ ((U.subgroupOf K).map (QuotientGroup.mk' ((H0 ⊔ S).subgroupOf K))) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  induction z using QuotientGroup.induction_on with
  | _ k =>
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_normal (hsup ▸ k.2 : (k : L) ∈ H ⊔ U)
    have haK : a ∈ K := hsup ▸ (le_sup_left (α := Subgroup L) ha)
    have hbK : b ∈ K := hsup ▸ (le_sup_right (α := Subgroup L) hb)
    have hkeq : k = (⟨a, haK⟩ : ↥K) * ⟨b, hbK⟩ := Subtype.ext (by simpa using hab.symm)
    rw [show (QuotientGroup.mk k : ↥K ⧸ (H0 ⊔ S).subgroupOf K)
        = QuotientGroup.mk (⟨a, haK⟩ : ↥K) * QuotientGroup.mk (⟨b, hbK⟩ : ↥K) by
      rw [← QuotientGroup.mk_mul, ← hkeq]]
    exact mul_mem (le_sup_left (α := Subgroup (↥K ⧸ (H0 ⊔ S).subgroupOf K))
        ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)
      (le_sup_right (α := Subgroup (↥K ⧸ (H0 ⊔ S).subgroupOf K))
        ⟨⟨b, hbK⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩)

theorem toQuotSemidirect_bijective [(S.subgroupOf U).Normal] [((H0 ⊔ S).subgroupOf K).Normal]
    (hS : S ≤ (conjQuotientAut H H0).ker) (hH0H : H0 ≤ H) (hSU : S ≤ U)
    (hsup : H ⊔ U = K) (hdisj : Disjoint H U) (hHK : H ≤ K) (hUK : U ≤ K) :
    Function.Bijective (toQuotSemidirect H H0 U hS hHK hUK) := by
  refine semidirectLift_bijective _ _ _
    (quotSubgroupOfMap_injective hHK (le_sup_left : H0 ≤ H0 ⊔ S)
      (sup_inf_le_left_of_disjoint hH0H hSU hdisj))
    (quotSubgroupOfMap_injective hUK (le_sup_right : S ≤ H0 ⊔ S)
      (sup_inf_le_right_of_disjoint hH0H hSU hdisj)) ?_ ?_
  · rw [range_quotSubgroupOfMap, range_quotSubgroupOfMap]
    exact disjoint_map_mk'_subgroupOf (H := H) (H0 := H0) (U := U) (S := S) (K := K)
      hdisj hH0H hSU
  · rw [range_quotSubgroupOfMap, range_quotSubgroupOfMap]
    exact sup_map_mk'_subgroupOf_eq_top (H := H) (H0 := H0) (U := U) (K := K) S hsup

noncomputable def quotientEquivSemidirectProduct [(S.subgroupOf U).Normal]
    [((H0 ⊔ S).subgroupOf K).Normal]
    (hS : S ≤ (conjQuotientAut H H0).ker) (hH0H : H0 ≤ H) (hSU : S ≤ U)
    (hsup : H ⊔ U = K) (hdisj : Disjoint H U) (hHK : H ≤ K) (hUK : U ≤ K) :
    (↥H ⧸ H0.subgroupOf H) ⋊[quotConjAut H H0 U hS] (↥U ⧸ S.subgroupOf U) ≃*
      ↥K ⧸ (H0 ⊔ S).subgroupOf K :=
  MulEquiv.ofBijective _
    (toQuotSemidirect_bijective H H0 U hS hH0H hSU hsup hdisj hHK hUK)

theorem quotientEquivSemidirectProduct_inl [(S.subgroupOf U).Normal]
    [((H0 ⊔ S).subgroupOf K).Normal]
    (hS : S ≤ (conjQuotientAut H H0).ker) (hH0H : H0 ≤ H) (hSU : S ≤ U)
    (hsup : H ⊔ U = K) (hdisj : Disjoint H U) (hHK : H ≤ K) (hUK : U ≤ K) (h : ↥H) :
    quotientEquivSemidirectProduct H H0 U hS hH0H hSU hsup hdisj hHK hUK
        (SemidirectProduct.inl (QuotientGroup.mk h)) =
      QuotientGroup.mk (Subgroup.inclusion hHK h) :=
  toQuotSemidirect_inl H H0 U hS hHK hUK (QuotientGroup.mk h)

theorem quotientEquivSemidirectProduct_inr [(S.subgroupOf U).Normal]
    [((H0 ⊔ S).subgroupOf K).Normal]
    (hS : S ≤ (conjQuotientAut H H0).ker) (hH0H : H0 ≤ H) (hSU : S ≤ U)
    (hsup : H ⊔ U = K) (hdisj : Disjoint H U) (hHK : H ≤ K) (hUK : U ≤ K) (u : ↥U) :
    quotientEquivSemidirectProduct H H0 U hS hH0H hSU hsup hdisj hHK hUK
        (SemidirectProduct.inr (QuotientGroup.mk u)) =
      QuotientGroup.mk (Subgroup.inclusion hUK u) :=
  toQuotSemidirect_inr H H0 U hS hHK hUK (QuotientGroup.mk u)

theorem quotConjAut_chiefActionKer_eq_one
    [(S.subgroupOf (chiefActionKer H H0 U)).Normal] (hS : S ≤ (conjQuotientAut H H0).ker) :
    quotConjAut H H0 (chiefActionKer H H0 U) hS = 1 := by
  refine MonoidHom.ext fun z => ?_
  induction z using QuotientGroup.induction_on with
  | _ c =>
    rw [quotConjAut_mk]
    exact ((mem_chiefActionKer_iff_mem_ker H H0 U).mp c.2).2

noncomputable def supEquivProd
    [((⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf
      (chiefActionKer H H0 U)).Normal]
    [((H0 ⊔ ⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf
      (H ⊔ chiefActionKer H H0 U)).Normal]
    (hS : (⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆ : Subgroup L)
      ≤ (conjQuotientAut H H0).ker)
    (hH0H : H0 ≤ H) (hdisj : Disjoint H (chiefActionKer H H0 U)) :
    (↥(H ⊔ chiefActionKer H H0 U) ⧸
      (H0 ⊔ ⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf
        (H ⊔ chiefActionKer H H0 U)) ≃*
      (↥H ⧸ H0.subgroupOf H) ×
        (↥(chiefActionKer H H0 U) ⧸
          (⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf (chiefActionKer H H0 U)) :=
  (quotientEquivSemidirectProduct H H0 (chiefActionKer H H0 U) hS hH0H
      (commutator_self_le _) rfl hdisj le_sup_left le_sup_right).symm.trans <| by
    rw [quotConjAut_chiefActionKer_eq_one]
    exact SemidirectProduct.mulEquivProd

def conjQuotAutRestrict : ↥U →* MulAut (↥H ⧸ H0.subgroupOf H) :=
  (conjQuotientAut H H0).comp U.subtype

@[simp]
theorem conjQuotAutRestrict_apply (u : ↥U) :
    conjQuotAutRestrict H H0 U u = conjQuotientAut H H0 (u : L) := (rfl)

def quotientBotSubgroupOfEquiv : (↥U ⧸ (⊥ : Subgroup L).subgroupOf U) ≃* ↥U :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf U)).trans QuotientGroup.quotientBot

theorem quotientBotSubgroupOfEquiv_symm_apply (u : ↥U) :
    (quotientBotSubgroupOfEquiv U).symm u = QuotientGroup.mk u := by
  rw [MulEquiv.symm_apply_eq, quotientBotSubgroupOfEquiv, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  exact ((MulEquiv.eq_symm_apply QuotientGroup.quotientBot).mp rfl).symm

noncomputable def quotientEquivSemidirectProductOfBot [(H0.subgroupOf K).Normal] (hH0H : H0 ≤ H)
    (hsup : H ⊔ U = K) (hdisj : Disjoint H U) :
    (↥H ⧸ H0.subgroupOf H) ⋊[conjQuotAutRestrict H H0 U] ↥U ≃* ↥K ⧸ H0.subgroupOf K :=
  (SemidirectProduct.congr (MulEquiv.refl _) (quotientBotSubgroupOfEquiv U).symm (fun u => by
      refine MulEquiv.ext fun z => ?_
      simp only [MulEquiv.trans_apply, MulEquiv.refl_apply, quotientBotSubgroupOfEquiv_symm_apply,
        quotConjAut_mk, conjQuotAutRestrict_apply])).trans
    ((quotientEquivSemidirectProduct H H0 U (bot_le : (⊥ : Subgroup L) ≤ _) hH0H bot_le hsup hdisj
        (hsup ▸ le_sup_left) (hsup ▸ le_sup_right)).trans
      (QuotientGroup.quotientMulEquivOfEq (by rw [sup_bot_eq])))

theorem quotientEquivSemidirectProductOfBot_inl [(H0.subgroupOf K).Normal] (hH0H : H0 ≤ H)
    (hsup : H ⊔ U = K) (hdisj : Disjoint H U) (h : ↥H) :
    quotientEquivSemidirectProductOfBot H H0 U hH0H hsup hdisj
        (SemidirectProduct.inl (QuotientGroup.mk h)) =
      QuotientGroup.mk (Subgroup.inclusion (hsup ▸ le_sup_left : H ≤ K) h) := by
  simp only [quotientEquivSemidirectProductOfBot, MulEquiv.trans_apply]
  rw [show (SemidirectProduct.congr _ _ _ (SemidirectProduct.inl (QuotientGroup.mk h)) :
    (↥H ⧸ H0.subgroupOf H) ⋊[quotConjAut H H0 U (bot_le : (⊥ : Subgroup L) ≤ _)]
      (↥U ⧸ (⊥ : Subgroup L).subgroupOf U)) = SemidirectProduct.inl (QuotientGroup.mk h) from by
    ext <;> simp]
  rw [quotientEquivSemidirectProduct_inl]
  rfl

theorem quotientEquivSemidirectProductOfBot_inr [(H0.subgroupOf K).Normal] (hH0H : H0 ≤ H)
    (hsup : H ⊔ U = K) (hdisj : Disjoint H U) (u : ↥U) :
    quotientEquivSemidirectProductOfBot H H0 U hH0H hsup hdisj (SemidirectProduct.inr u) =
      QuotientGroup.mk (Subgroup.inclusion (hsup ▸ le_sup_right : U ≤ K) u) := by
  simp only [quotientEquivSemidirectProductOfBot, MulEquiv.trans_apply]
  rw [show (SemidirectProduct.congr _ _ _ (SemidirectProduct.inr u) :
    (↥H ⧸ H0.subgroupOf H) ⋊[quotConjAut H H0 U (bot_le : (⊥ : Subgroup L) ≤ _)]
      (↥U ⧸ (⊥ : Subgroup L).subgroupOf U)) = SemidirectProduct.inr (QuotientGroup.mk u) from by
    ext <;> simp [quotientBotSubgroupOfEquiv_symm_apply]]
  rw [quotientEquivSemidirectProduct_inr]
  rfl

noncomputable def quotientEquivSemidirectProductOfCommutator
    [((⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf U).Normal]
    [((H0 ⊔ ⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf K).Normal]
    (hS : (⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆ : Subgroup L)
      ≤ (conjQuotientAut H H0).ker)
    (hH0H : H0 ≤ H) (hsup : H ⊔ U = K) (hdisj : Disjoint H U) :
    (↥H ⧸ H0.subgroupOf H) ⋊[quotConjAut H H0 U hS]
        (↥U ⧸ (⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf U) ≃*
      ↥K ⧸ (H0 ⊔ ⁅chiefActionKer H H0 U, chiefActionKer H H0 U⁆).subgroupOf K :=
  quotientEquivSemidirectProduct H H0 U hS hH0H
    ((commutator_self_le _).trans (chiefActionKer_le H H0 U)) hsup hdisj
    (hsup ▸ le_sup_left) (hsup ▸ le_sup_right)

end Quotient

end CFSG.FeitThompson
