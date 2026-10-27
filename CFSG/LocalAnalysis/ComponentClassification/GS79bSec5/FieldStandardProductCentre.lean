module

public import Mathlib.GroupTheory.Sylow

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.GH74.Uniqueness.Section171Group
import CFSG.GroupTheory.ABGLocalTools.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ComponentClassification.GS79bSec5

open Subgroup

variable {G : Type} [Group G]

private theorem map_conj_sup_map_conj_eq {P : Subgroup G} {t : G} (ht2 : t * t = 1) :
    (P ⊔ P.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      P ⊔ P.map (MulAut.conj t).toMonoidHom := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hcomp :
      (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
    ext x
    calc
      (MulAut.conj t).toMonoidHom ((MulAut.conj t).toMonoidHom x) = t * (t * x) := by
        simp [MulAut.conj_apply, mul_assoc, ht2, htinv]
      _ = x := by rw [← mul_assoc, ht2, one_mul]
  rw [Subgroup.map_sup, Subgroup.map_map, hcomp, Subgroup.map_id, sup_comm]

private theorem isCyclic_of_isPGroup_of_le_centralizer {A SG : Subgroup G}
    (hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S)
    (hSG2 : IsPGroup 2 SG) (hSGle : SG ≤ centralizer (A : Set G)) :
    IsCyclic ↥SG := by
  let SG' : Subgroup (centralizer (A : Set G)) :=
    SG.subgroupOf (centralizer (A : Set G))
  have hSG2' : IsPGroup 2 SG' := hSG2.comap_subtype
  obtain ⟨T, hSGT⟩ := hSG2'.exists_le_sylow
  have hSG'cyc : IsCyclic ↥SG' := by
    have : IsCyclic ↥T := hcyc T
    exact Subgroup.isCyclic_of_le hSGT
  exact (Subgroup.subgroupOfEquivOfLe hSGle).isCyclic.mp hSG'cyc

private theorem map_conj_eq_self_of_mem_centralizer_sup {P : Subgroup G} {t : G}
    (htQ : t ∈ centralizer ((P ⊔ P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    P.map (MulAut.conj t).toMonoidHom = P := by
  have htP : ∀ p ∈ P, t * p * t⁻¹ = p := by
    intro p hp
    have hcomm : p * t = t * p :=
      (Subgroup.mem_centralizer_iff.mp htQ) p (Subgroup.mem_sup_left hp)
    calc
      t * p * t⁻¹ = p * t * t⁻¹ := by rw [hcomm]
      _ = p := by simp [mul_assoc]
  apply le_antisymm
  · rintro p ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply, htP q hq] using hq
  · intro p hp
    exact Subgroup.mem_map.mpr
      ⟨p, hp, by simpa [MulAut.conj_apply] using htP p hp⟩

private theorem exists_sylow_isCyclic_map_of_le_centralizer {A H : Subgroup G} {t : G}
    (hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S)
    (hHle : H ≤ centralizer (A : Set G)) (htH : t ∈ H) (ht : orderOf t = 2) :
    ∃ S : Sylow 2 H, IsCyclic ↥((S : Subgroup H).map H.subtype) ∧
      t ∈ (S : Subgroup H).map H.subtype := by
  have hZ2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  let Z : Subgroup H := (zpowers t).subgroupOf H
  have hZ2' : IsPGroup 2 Z := hZ2.comap_subtype
  obtain ⟨S, hZS⟩ := hZ2'.exists_le_sylow
  have hSG2 : IsPGroup 2 ((S : Subgroup H).map H.subtype) := S.isPGroup'.map H.subtype
  have hSGle : (S : Subgroup H).map H.subtype ≤ centralizer (A : Set G) := by
    rintro _ ⟨s, _, rfl⟩
    exact hHle s.2
  have hSGcyc : IsCyclic ↥((S : Subgroup H).map H.subtype) :=
    isCyclic_of_isPGroup_of_le_centralizer hcyc hSG2 hSGle
  have htZ : (⟨t, htH⟩ : H) ∈ Z :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers t)
  refine ⟨S, hSGcyc, ?_⟩
  exact Subgroup.mem_map.mpr ⟨⟨t, htH⟩, hZS htZ, rfl⟩

section Diag

variable [Finite G]

private theorem exists_involution_mem_inf_of_isSylow {H C : Subgroup G} (S : Sylow 2 H)
    (hCH : C ≤ H) (hCnorm : H ≤ normalizer (C : Set G)) (hCeven : 2 ∣ Nat.card C) :
    ∃ x : G, x ∈ (S : Subgroup H).map H.subtype ⊓ C ∧ orderOf x = 2 := by
  let SG : Subgroup G := (S : Subgroup H).map H.subtype
  let R : Subgroup G := SG ⊓ C
  have hRleSG : R ≤ SG := inf_le_left
  have hRleC : R ≤ C := inf_le_right
  have hIsSylowH : CFSG.ABGLocalTools.IsSylowOf 2 SG H := ⟨S, rfl⟩
  have hIsSylowC : CFSG.ABGLocalTools.IsSylowOf 2 R C :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hIsSylowH hCH hCnorm
  have hRnotdvd : ¬ 2 ∣ R.relIndex C :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hIsSylowC).2.2
  have hRne : R ≠ ⊥ := by
    intro hbot
    apply hRnotdvd
    have hrel : R.relIndex C = Nat.card C := by simp [hbot]
    rw [hrel]
    exact hCeven
  have hRcard_ne : Nat.card R ≠ 1 := fun h =>
    hRne ((Subgroup.eq_bot_iff_card R).mpr h)
  have hR2dvd : 2 ∣ Nat.card R :=
    (hIsSylowC.isPGroup.card_eq_or_dvd).resolve_left hRcard_ne
  obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 hR2dvd
  refine ⟨x.1, ⟨hRleSG x.2, hRleC x.2⟩, ?_⟩
  simpa using (Subgroup.orderOf_coe x).trans hx2

private theorem involution_mem_of_isSylow_inf_of_isCyclic {C H : Subgroup G} {t : G}
    (S : Sylow 2 H) (hCH : C ≤ H)
    (hSGcyc : IsCyclic ↥((S : Subgroup H).map H.subtype))
    (htSG : t ∈ (S : Subgroup H).map H.subtype) (ht : orderOf t = 2)
    (hCnorm : H ≤ normalizer (C : Set G)) (hCeven : 2 ∣ Nat.card C) :
    t ∈ C := by
  have hSGcyc' : IsCyclic ↥((S : Subgroup H).map H.subtype) := hSGcyc
  obtain ⟨x, hxR, hx2⟩ := exists_involution_mem_inf_of_isSylow S hCH hCnorm hCeven
  have hx2' : orderOf (⟨x, hxR.1⟩ : (S : Subgroup H).map H.subtype) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hx2
  have htSG2 : orderOf (⟨t, htSG⟩ : (S : Subgroup H).map H.subtype) = 2 := by
    rw [Subgroup.orderOf_mk, ht]
  have hEq : (⟨x, hxR.1⟩ : (S : Subgroup H).map H.subtype) = ⟨t, htSG⟩ :=
    CFSG.GH74.Uniqueness.eq_of_orderOf_eq_two_of_isCyclic hx2' htSG2
  have hxT : x = t := congrArg Subtype.val hEq
  rw [← hxT]
  exact hxR.2

private theorem odd_card_centralizer_sup_map_conj_aux {A P : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set G))
    (hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S)
    (hc : P.map (MulAut.conj t).toMonoidHom ≤ centralizer (P : Set G))
    (hAP : A ≤ P ⊔ P.map (MulAut.conj t).toMonoidHom)
    (hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) :
    Odd (Nat.card (centralizer
      ((P ⊔ P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))) := by
  let Q : Subgroup G := P ⊔ P.map (MulAut.conj t).toMonoidHom
  let C : Subgroup G := centralizer (Q : Set G)
  let Z : Subgroup G := zpowers t
  let H : Subgroup G := C ⊔ Z
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hQQ : Q.map (MulAut.conj t).toMonoidHom = Q := map_conj_sup_map_conj_eq ht2
  have htN : t ∈ normalizer (Q : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hQQ
  have hHle : H ≤ centralizer (A : Set G) :=
    sup_le (Subgroup.centralizer_le hAP) (Subgroup.zpowers_le.mpr htA)
  have hHnorm : H ≤ normalizer (Q : Set G) :=
    sup_le (Subgroup.centralizer_le_normalizer (Q : Set G)) (Subgroup.zpowers_le.mpr htN)
  have hCnormH : H ≤ normalizer (C : Set G) :=
    hHnorm.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup Q)
  have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨S, hSGcyc, htSG⟩ :=
    exists_sylow_isCyclic_map_of_le_centralizer hcyc hHle htH ht
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hCeven : 2 ∣ Nat.card C := by
    simpa [C, Q] using even_iff_two_dvd.mp hodd
  have htC : t ∈ C :=
    involution_mem_of_isSylow_inf_of_isCyclic S le_sup_left hSGcyc htSG ht hCnormH hCeven
  have hPmap : P.map (MulAut.conj t).toMonoidHom = P :=
    map_conj_eq_self_of_mem_centralizer_sup htC
  have hPle : P ≤ centralizer (P : Set G) := by
    rwa [hPmap] at hc
  obtain ⟨u, hu, v, hv, huv⟩ := hnab
  exact huv ((Subgroup.mem_centralizer_iff.mp (hPle hu) v hv).symm)

theorem odd_card_centralizer_sup_map_conj {A P : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set G))
    (hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S)
    (hc : P.map (MulAut.conj t).toMonoidHom ≤ centralizer (P : Set G))
    (hAP : A ≤ P ⊔ P.map (MulAut.conj t).toMonoidHom)
    (hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) :
    Odd (Nat.card (centralizer ((P ⊔ P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))) :=
  odd_card_centralizer_sup_map_conj_aux ht htA hcyc hc hAP hnab

theorem odd_card_center_sup_map_conj {A P : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set G))
    (hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S)
    (hc : P.map (MulAut.conj t).toMonoidHom ≤ centralizer (P : Set G))
    (hAP : A ≤ P ⊔ P.map (MulAut.conj t).toMonoidHom)
    (hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) :
    Odd (Nat.card (center ↥(P ⊔ P.map (MulAut.conj t).toMonoidHom))) := by
  let Q : Subgroup G := P ⊔ P.map (MulAut.conj t).toMonoidHom
  have hodd : Odd (Nat.card (centralizer (Q : Set G))) :=
    odd_card_centralizer_sup_map_conj ht htA hcyc hc hAP hnab
  have hle : (center ↥Q).map Q.subtype ≤ centralizer (Q : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨q, hq⟩)
  have hdvd : Nat.card (center ↥Q) ∣ Nat.card (centralizer (Q : Set G)) := by
    rw [← Subgroup.card_map_of_injective Q.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  exact hodd.of_dvd_nat hdvd

end Diag

end CFSG.ComponentClassification.GS79bSec5
