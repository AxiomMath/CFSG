module

public import CFSG.GH74.Uniqueness.SU.KI1r4Parts
public import CFSG.GH74.Uniqueness.SU.KI1r4L34Facts
public import CFSG.GH74.Uniqueness.SU.KI1r4L34Tr
public import CFSG.GH74.Uniqueness.SU.KI1r4L34Cfg
public import CFSG.GH74.Uniqueness.SU.KI1r4L34Res

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.GH74.Uniqueness.SU.K.R3
open scoped commutatorElement

theorem ki1r4L34_of
    (hQ : KI1r4TwoGroup) : KI1r4L34 := by
  intro H _ _ T x h h4 hsimple hcen hxK hL hd9
  classical
  set K : Subgroup H := generalizedFitting H with hKdef
  have hKn : K.Normal := (CFSG.LocalCores.generalized_fitting_characteristic).2
  obtain ⟨e⟩ := CFSG.GH74.KGroups.L34.equiv_of_lieModel hL
  have hx2 : x * x = 1 := h.mul_self_x
  obtain ⟨hcard, hC, hy, hcomm⟩ := L34M.l34_facts T K hcen e x hx2 hxK h.xT hd9
  set P : Subgroup H := (T : Subgroup H) ⊓ K with hPdef
  have hPK : P ≤ K := inf_le_right
  have hP2 : IsPGroup 2 P := T.isPGroup'.to_le inf_le_left
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hxP : x ∉ P := fun hx => hxK (hPK hx)
  have hTN : (T : Subgroup H) ≤ normalizer (P : Set H) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · rintro ⟨hpT, hpK⟩
      exact ⟨(T : Subgroup H).mul_mem ((T : Subgroup H).mul_mem ht hpT)
        ((T : Subgroup H).inv_mem ht), hKn.conj_mem p hpK t⟩
    · rintro ⟨hpT, hpK⟩
      have e1 : p = t⁻¹ * (t * p * t⁻¹) * t := by group
      rw [e1]
      exact ⟨(T : Subgroup H).mul_mem ((T : Subgroup H).mul_mem ((T : Subgroup H).inv_mem ht) hpT)
        ht, by simpa using hKn.conj_mem _ hpK t⁻¹⟩
  obtain ⟨hCfgN, h4N, hFitN, hPfit⟩ := Cfg.normalizer_two h h4 P hP2 hPne hTN hxP hC hy
  obtain ⟨hFle, hJ⟩ := hQ _ (T.subtype hTN) _ hCfgN h4N hFitN
  have hPN' : P ≤ normalizer (P : Set H) := Subgroup.le_normalizer
  have hJ1 := hJ.2.1
  have hcardPsubN : Nat.card ↥(Psub ↥(normalizer (P : Set H)) (T.subtype hTN)) = 64 := by
    obtain ⟨φ⟩ := SU5.isL34Type_iff.1 hJ1
    rw [Nat.card_congr φ.toEquiv]
    exact SU5.card_L34Syl
  have hPsubEq : Psub ↥(normalizer (P : Set H)) (T.subtype hTN) =
      generalizedFitting ↥(normalizer (P : Set H)) := inf_eq_right.2 hFle
  have hP'card : Nat.card ↥(P.subgroupOf (normalizer (P : Set H))) = 64 := by
    have h1 : (P.subgroupOf (normalizer (P : Set H))).map (normalizer (P : Set H)).subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPN']
    rw [← hcard, ← Subgroup.card_map_of_injective (normalizer (P : Set H)).subtype_injective
      (K := P.subgroupOf (normalizer (P : Set H))), h1]
  have hPN : Psub ↥(normalizer (P : Set H)) (T.subtype hTN) =
      P.subgroupOf (normalizer (P : Set H)) := by
    rw [hPsubEq]
    symm
    refine Subgroup.eq_of_le_of_card_ge (hPfit.trans le_sup_left) ?_
    rw [← hPsubEq, hcardPsubN, hP'card]
  have hJH : J2Structure H T := J2Structure.of_normalizer T P hTN rfl hJ hPN
  have hTcard : Nat.card ↥(T : Subgroup H) = 128 := by
    obtain ⟨φ⟩ := hJH.1
    rw [Nat.card_congr φ.toEquiv]
    exact SU5.card_J2Syl
  have hidx : Nat.card ↥((T : Subgroup H) ⊓ K) * 2 = Nat.card ↥(T : Subgroup H) := by
    rw [hTcard]
    show Nat.card ↥P * 2 = 128
    rw [hcard]
  exact ⟨⟨oPrimeResidual_eq_sup T K hsimple x hx2 hxK h.xT hcomm hidx hPne, hL, hd9⟩, hJH⟩

end CFSG.GH74.Uniqueness.SU.K.R4
