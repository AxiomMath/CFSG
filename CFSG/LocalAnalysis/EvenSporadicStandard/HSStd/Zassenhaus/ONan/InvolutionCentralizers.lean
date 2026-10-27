module

public import CFSG.GH74.Generic.S45.LSporMathA
public import CFSG.GH74.Generic.S45.LSporMathB
public import CFSG.GH74.Generic.S45.LSporRu
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalOuter
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier

theorem card_centralizer_of_involution_of_isSporadic_m22
    {N : Type} [Group N]
    (hN : IsSporadic N .M22) (t : N) (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set N)) = 384 := by
  obtain ⟨e⟩ := hN
  let e' : N ≃* ↥NativeSporadic.M22 := e
  rw [CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M22 e' t]
  exact CFSG.GH74.Generic.S45.LSporB.m22_inner_centralizer_card _
    (e' t).2 (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact ht)

theorem card_centralizer_of_involution_of_isSporadic_m23
    {N : Type} [Group N]
    (hN : IsSporadic N .M23) (t : N) (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set N)) = 2688 := by
  obtain ⟨e⟩ := hN
  let e' : N ≃* ↥NativeSporadic.M23 := e
  rw [CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M23 e' t]
  exact CFSG.GH74.Generic.S45.LAlt.m23_class_card _
    (e' t).2 (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact ht)

theorem card_centralizer_of_involution_of_isSporadic_m24
    {N : Type} [Group N]
    (hN : IsSporadic N .M24) (t : N) (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set N)) = 7680 ∨ Nat.card (centralizer ({t} : Set N)) = 21504 := by
  obtain ⟨e⟩ := hN
  let e' : N ≃* ↥NativeSporadic.M24 := e
  rw [CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M24 e' t]
  rcases CFSG.GH74.Generic.S45.LAlt.m24_class_card _ (e' t).2
    (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact ht) with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem card_centralizerIn_j2P_of_involution
    {t : Equiv.Perm (Fin 315)} (ht : t ∈ CFSG.ComponentClassification.J2Cover.P)
    (h2 : orderOf t = 2) :
    Nat.card (centralizerIn CFSG.ComponentClassification.J2Cover.P t) = 240 ∨
      Nat.card (centralizerIn CFSG.ComponentClassification.J2Cover.P t) = 1920 := by
  obtain ⟨hcov, -, he1, -, he2⟩ := CFSG.ComponentClassification.J2Cover.inner_classes
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov t ht h2
  rw [centralizerIn_conj CFSG.ComponentClassification.J2Cover.P hc r,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    rw [he1]
    exact CFSG.ComponentClassification.J2Cover.cent2B_facts.2.1
  · right
    rw [he2]
    exact CFSG.ComponentClassification.J2Cover.cent2A_facts.2.1

theorem card_centralizer_of_involution_of_isSporadic_j2
    {N : Type} [Group N] (hN : IsSporadic N .J2) (t : N)
    (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set N)) = 240 ∨ Nat.card (centralizer ({t} : Set N)) = 1920 := by
  obtain ⟨e⟩ := hN
  let e' : N ≃* CFSG.ComponentClassification.J2Cover.P :=
    e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  rw [CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn
    CFSG.ComponentClassification.J2Cover.P e' t]
  refine card_centralizerIn_j2P_of_involution (e' t).2 ?_
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact ht

theorem card_centralizer_of_involution_of_isSporadic_ru
    {N : Type} [Group N]
    (hN : IsSporadic N .Ru) (t : N) (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set N)) = 245760 ∨
      Nat.card (centralizer ({t} : Set N)) = 116480 := by
  obtain ⟨e⟩ := hN
  let e' : N ≃* CFSG.Sporadic.RuSchreier.ruP := e.trans CFSG.Sporadic.RuSchreier.ruEquivP
  rw [CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_centralizerIn
    CFSG.Sporadic.RuSchreier.ruP e' t]
  refine CFSG.GH74.Generic.S45.ru_card_centralizer_involution (e' t).2 ?_
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact ht

private theorem outerAux_orderOf {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) : orderOf (MulAut.congr e α) = orderOf α :=
  MulEquiv.orderOf_eq (MulAut.congr e) α

private theorem outerAux_not_mem_inner {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {α : MulAut G} (hout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G) :
    MulAut.congr e α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner H := by
  intro hin
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at hin
  obtain ⟨a, ha, hae⟩ := hin
  exact hout (by rw [← (MulAut.congr e).injective hae]; exact ha)

private theorem outerAux_card_fixed {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) :
    Nat.card {x : G // α x = x} = Nat.card {y : H // MulAut.congr e α y = y} := by
  have hG : Nat.card {x : G // α x = x} = Nat.card ↥(fixSub α) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_fixSub.symm)
  have hH : Nat.card {y : H // MulAut.congr e α y = y} =
      Nat.card ↥(fixSub (MulAut.congr e α)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => mem_fixSub.symm)
  rw [hG, hH, ← map_fixSub_equiv e α, Subgroup.card_map_of_injective e.injective]

theorem card_fixed_of_outer_involution_of_isSporadic_m22
    {N : Type} [Group N] (hN : IsSporadic N .M22) (α : MulAut N)
    (hα : orderOf α = 2)
    (hout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner N) :
    Nat.card {x : N // α x = x} = 320 ∨ Nat.card {x : N // α x = x} = 1344 := by
  obtain ⟨e⟩ := hN
  let e' : N ≃* ↥NativeSporadic.M22 := e
  have h2 : orderOf (MulAut.congr e' α) = 2 := by rw [outerAux_orderOf]; exact hα
  have hout' : MulAut.congr e' α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (↥NativeSporadic.M22) := outerAux_not_mem_inner e' hout
  have hsq : MulAut.congr e' α * MulAut.congr e' α = 1 := by
    rw [← pow_two, ← h2]; exact pow_orderOf_eq_one _
  rw [outerAux_card_fixed e' α]
  exact CFSG.GH74.Generic.S45.m22_outer_fixed_card (MulAut.congr e' α) hsq hout'

theorem card_fixed_of_outer_involution_of_isSporadic_j2
    {N : Type} [Group N] (hN : IsSporadic N .J2) (α : MulAut N)
    (hα : orderOf α = 2)
    (hout : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner N) :
    Nat.card {x : N // α x = x} = 336 := by
  obtain ⟨e⟩ := hN
  let e' : N ≃* CFSG.ComponentClassification.J2Cover.P :=
    e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  have h2 : orderOf (MulAut.congr e' α) = 2 := by rw [outerAux_orderOf]; exact hα
  have hout' : MulAut.congr e' α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      CFSG.ComponentClassification.J2Cover.P := outerAux_not_mem_inner e' hout
  rw [outerAux_card_fixed e' α]
  obtain ⟨g, hg⟩ :=
    CFSG.ComponentClassification.J2Cover.External.exists_conj_beta_of_outer h2 hout'
  have h1 : Nat.card {x : CFSG.ComponentClassification.J2Cover.P // MulAut.congr e' α x = x} =
      Nat.card ↥(CFSG.Sporadic.Schreier.fixSub (MulAut.congr e' α)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => CFSG.Sporadic.Schreier.mem_fixSub.symm)
  rw [h1, hg]
  exact CFSG.ComponentClassification.J2Cover.External.card_fixSub_conj_beta g

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
