module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Fi24Inputs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Reifart

open Subgroup

section Abstract

variable {A B : Type*} [Group A] [Group B]

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} (e : A ≃* B)
    (h : CFSG.IsElementaryAbelian p A) : CFSG.IsElementaryAbelian p B :=
  CFSG.IsElementaryAbelian.of_mulEquiv e h

theorem isExtraspecial_of_mulEquiv {p : ℕ} (e : A ≃* B)
    (h : CFSG.IsExtraspecial p A) : CFSG.IsExtraspecial p B := by
  let f : A ⧸ center A ≃* B ⧸ center B :=
    QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e)
  exact
    { center_order_p := by
        rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
        exact h.center_order_p
      quotient_elementary_abelian :=
        isElementaryAbelian_of_mulEquiv f h.quotient_elementary_abelian
      quotient_nontrivial := by
        have := h.quotient_nontrivial
        exact f.injective.nontrivial }

@[expose] def O23Abs (A : Type*) [Group A] : Subgroup A :=
  (CFSG.pCore 3 (A ⧸ CFSG.pCore 2 A)).comap (QuotientGroup.mk' (CFSG.pCore 2 A))

theorem map_O23Abs (e : A ≃* B) : (O23Abs A).map e.toMonoidHom = O23Abs B := by
  have hP2 := CFSG.pCore_map_iso 2 e
  let f : A ⧸ CFSG.pCore 2 A ≃* B ⧸ CFSG.pCore 2 B :=
    QuotientGroup.congr (CFSG.pCore 2 A) (CFSG.pCore 2 B) e hP2
  have hP3 := CFSG.pCore_map_iso 3 f
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hf : f (QuotientGroup.mk' (CFSG.pCore 2 A) x) =
      QuotientGroup.mk' (CFSG.pCore 2 B) (e x) :=
    QuotientGroup.congr_mk _ _ _ _ _
  unfold O23Abs
  rw [Subgroup.mem_comap, Subgroup.mem_comap, ← hP3, Subgroup.mem_map_equiv, ← hf,
    MulEquiv.symm_apply_apply]

end Abstract

section InGroup

variable {G G' : Type} [Group G] [Group G'] {H : Subgroup G} {H' : Subgroup G'}

theorem mem_map_subtype_iff {S : Subgroup ↥H} {x : G} :
    x ∈ S.map H.subtype ↔ ∃ hx : x ∈ H, (⟨x, hx⟩ : ↥H) ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hS⟩
    exact ⟨⟨x, hx⟩, hS, rfl⟩

theorem subgroupOf_map_subtype_eq (S : Subgroup ↥H) : (S.map H.subtype).subgroupOf H = S :=
  comap_map_eq_self_of_injective H.subtype_injective S

theorem O2In_eq (H : Subgroup G) : O2In H = (CFSG.pCore 2 ↥H).map H.subtype := rfl

theorem O23In_eq (H : Subgroup G) : O23In H = (O23Abs ↥H).map H.subtype := rfl

theorem centralizer_O2In_le (e : ↥H ≃* ↥H')
    (hcent : H' ⊓ centralizer (O2In H' : Set G') ≤ O2In H') :
    H ⊓ centralizer (O2In H : Set G) ≤ O2In H := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgH, hgc⟩ := hg
  rw [Subgroup.mem_centralizer_iff] at hgc
  have hmem : ((e ⟨g, hgH⟩ : ↥H') : G') ∈ centralizer (O2In H' : Set G') := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, O2In_eq, mem_map_subtype_iff] at hy
    obtain ⟨hyH, hyP⟩ := hy
    rw [← CFSG.pCore_map_iso 2 e, Subgroup.mem_map_equiv] at hyP
    have hx : ((e.symm ⟨y, hyH⟩ : ↥H) : G) ∈ O2In H := by
      rw [O2In_eq]; exact ⟨_, hyP, rfl⟩
    have h1 := hgc _ hx
    have h2 : e.symm ⟨y, hyH⟩ * ⟨g, hgH⟩ = ⟨g, hgH⟩ * e.symm ⟨y, hyH⟩ := Subtype.ext h1
    have h3 := congrArg e h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact congrArg Subtype.val h3
  have h4 := hcent (Subgroup.mem_inf.2 ⟨(e ⟨g, hgH⟩).2, hmem⟩)
  rw [O2In_eq, mem_map_subtype_iff] at h4
  obtain ⟨_, hP⟩ := h4
  rw [← CFSG.pCore_map_iso 2 e, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hP
  rw [O2In_eq]
  exact ⟨_, hP, rfl⟩

end InGroup

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Reifart

