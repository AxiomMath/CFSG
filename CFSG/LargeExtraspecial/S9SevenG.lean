module

public import CFSG.LargeExtraspecial.S9SevenF
public import CFSG.LargeExtraspecial.S9SevenC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G]

theorem mul_self_mem_of_closure {R : Type*} [Group R] {N : Subgroup R} (hN : N.Normal)
    {s s' c : R} (hs : s * s ∈ N) (hs' : s' * s' ∈ N) (hgen : closure ({s, s'} : Set R) ⊔ N = ⊤)
    (hcs : c * s * c⁻¹ * s⁻¹ ∈ N) : c * c ∈ N := by
  have hπ : ∀ x : R, (QuotientGroup.mk' N) x = 1 ↔ x ∈ N := fun x => QuotientGroup.eq_one_iff x
  have h1 : (QuotientGroup.mk' N) s * (QuotientGroup.mk' N) s = 1 := by
    rw [← map_mul, hπ]; exact hs
  have h2 : (QuotientGroup.mk' N) s' * (QuotientGroup.mk' N) s' = 1 := by
    rw [← map_mul, hπ]; exact hs'
  have hcl : (QuotientGroup.mk' N) c ∈
      closure ({(QuotientGroup.mk' N) s, (QuotientGroup.mk' N) s'} : Set (R ⧸ N)) := by
    have hmap := congrArg (Subgroup.map (QuotientGroup.mk' N)) hgen
    rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_pair,
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']), sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at hmap
    rw [hmap]
    exact mem_top _
  have hcs' : (QuotientGroup.mk' N) c * (QuotientGroup.mk' N) s =
      (QuotientGroup.mk' N) s * (QuotientGroup.mk' N) c := by
    have h3 : (QuotientGroup.mk' N) (c * s * c⁻¹ * s⁻¹) = 1 := (hπ _).mpr hcs
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    calc (QuotientGroup.mk' N) c * (QuotientGroup.mk' N) s =
        ((QuotientGroup.mk' N) c * (QuotientGroup.mk' N) s * ((QuotientGroup.mk' N) c)⁻¹ *
          ((QuotientGroup.mk' N) s)⁻¹) * ((QuotientGroup.mk' N) s * (QuotientGroup.mk' N) c) := by
          group
      _ = (QuotientGroup.mk' N) s * (QuotientGroup.mk' N) c := by rw [h3, one_mul]
  have h4 := sq_eq_one_of_commute_of_mem_closure_pair h1 h2 hcl hcs'
  rw [← map_mul, hπ] at h4
  exact h4

namespace Hyp97

variable {S : Setting G} {g : G} {k : S.M} {O : Subgroup S.O} (X : Hyp97 S g k O)
include X

theorem inv_mul_mem_of_mem_Lbar_mul (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) {ℓ' : S.O} (hℓ'L : ℓ' ∈ S.Lbar ((k : G) * g))
    (hℓ'a : (ℓ' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) {l' : S.O}
    (hl' : l' ∈ S.Lbar ((k : G) * g)) (hl'O : l' ∉ O) : ℓ'⁻¹ * l' ∈ O := by
  have hspan := X.Ut_eq_span hLO hℓL hℓ
  have hla : (l' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ S.cl (g * S.z * g⁻¹) := by
    intro hfix
    apply hl'O
    refine X.mem_of_mem_Lbar_mul_cenU hLO hℓL hℓ hℓ'L hℓ'a hl'
      (mem_cenU.mpr ⟨mem_sup_right hl', fun u hu => ?_⟩)
    rw [hspan] at hu
    exact fix_of_fix_pair hfix (X.apply_cl_b_of_mem_Lbar_mul hl') hu
  have hl'a := X.apply_cl_a_eq hLO hℓL hℓ hl' hla
  have hmemL : ℓ'⁻¹ * l' ∈ S.Lbar ((k : G) * g) := mul_mem (inv_mem hℓ'L) hl'
  refine X.mem_of_mem_Lbar_mul_cenU hLO hℓL hℓ hℓ'L hℓ'a hmemL
    (mem_cenU.mpr ⟨mem_sup_right hmemL, fun u hu => ?_⟩)
  rw [hspan] at hu
  refine fix_of_fix_pair ?_ (X.apply_cl_b_of_mem_Lbar_mul hmemL) hu
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hl'a, ← hℓ'a]
  exact inv_apply_apply_O ℓ' _

theorem mul_self_mem (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) {ℓ' : S.O} (hℓ'L : ℓ' ∈ S.Lbar ((k : G) * g))
    (hℓ'a : (ℓ' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) {c : S.O}
    (hc : c ∈ cenU S g k) : c * c ∈ O := by
  have H := X.hyp4
  have hcX := (mem_cenU.mp hc).1
  have hN : (O.subgroupOf (S.Lbar g ⊔ S.Lbar ((k : G) * g))).Normal :=
    ⟨fun n hn x => by
      rw [mem_subgroupOf] at hn ⊢
      exact X.normal _ x.2 _ hn⟩
  have hgen : closure ({⟨ℓ, mem_sup_left hℓL⟩, ⟨ℓ', mem_sup_right hℓ'L⟩} :
      Set ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g))) ⊔
        O.subgroupOf (S.Lbar g ⊔ S.Lbar ((k : G) * g)) = ⊤ := by
    set Y := closure ({⟨ℓ, mem_sup_left hℓL⟩, ⟨ℓ', mem_sup_right hℓ'L⟩} :
      Set ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g))) ⊔
        O.subgroupOf (S.Lbar g ⊔ S.Lbar ((k : G) * g)) with hY
    have hℓY : (⟨ℓ, mem_sup_left hℓL⟩ : ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g))) ∈ Y :=
      mem_sup_left (subset_closure (Set.mem_insert _ _))
    have hℓ'Y : (⟨ℓ', mem_sup_right hℓ'L⟩ : ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g))) ∈ Y :=
      mem_sup_left (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hOY : ∀ y : ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g)), (y : S.O) ∈ O → y ∈ Y :=
      fun y hy => mem_sup_right (mem_subgroupOf.mpr hy)
    have hLY : S.Lbar g ≤ Y.map (S.Lbar g ⊔ S.Lbar ((k : G) * g)).subtype := by
      intro l hl
      refine ⟨⟨l, mem_sup_left hl⟩, ?_, rfl⟩
      by_cases hlO : l ∈ O
      · exact hOY _ hlO
      · have e : (⟨l, mem_sup_left hl⟩ : ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g))) =
            ⟨ℓ, mem_sup_left hℓL⟩ * ⟨ℓ⁻¹ * l, mul_mem (inv_mem (mem_sup_left hℓL))
              (mem_sup_left hl)⟩ := Subtype.ext (by simp)
        rw [e]
        exact mul_mem hℓY (hOY _ (hℓ l hl hlO))
    have hLbY : S.Lbar ((k : G) * g) ≤ Y.map (S.Lbar g ⊔ S.Lbar ((k : G) * g)).subtype := by
      intro l hl
      refine ⟨⟨l, mem_sup_right hl⟩, ?_, rfl⟩
      by_cases hlO : l ∈ O
      · exact hOY _ hlO
      · have e : (⟨l, mem_sup_right hl⟩ : ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g))) =
            ⟨ℓ', mem_sup_right hℓ'L⟩ * ⟨ℓ'⁻¹ * l, mul_mem (inv_mem (mem_sup_right hℓ'L))
              (mem_sup_right hl)⟩ := Subtype.ext (by simp)
        rw [e]
        exact mul_mem hℓ'Y (hOY _ (X.inv_mul_mem_of_mem_Lbar_mul hLO hℓL hℓ hℓ'L hℓ'a hl hlO))
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨y', hy', hyy'⟩ := (sup_le hLY hLbY) y.2
    rwa [show y = y' from Subtype.ext hyy'.symm]
  have hcomm := X.commutator_mem hLO hℓL hℓ hℓ'L hℓ'a hc (mem_sup_left hℓL)
  have h := mul_self_mem_of_closure hN
    (s := (⟨ℓ, mem_sup_left hℓL⟩ : ↥(S.Lbar g ⊔ S.Lbar ((k : G) * g))))
    (s' := ⟨ℓ', mem_sup_right hℓ'L⟩) (c := ⟨c, hcX⟩)
    (mem_subgroupOf.mpr (by
      change ℓ * ℓ ∈ O
      rw [mul_self_of_mem_Lbar S H.conj_mem hℓL]
      exact one_mem _))
    (mem_subgroupOf.mpr (by
      change ℓ' * ℓ' ∈ O
      rw [mul_self_of_mem_Lbar S (H.mul k).conj_mem hℓ'L]
      exact one_mem _))
    hgen (mem_subgroupOf.mpr hcomm)
  exact mem_subgroupOf.mp h

theorem cenU_le (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) {ℓ' : S.O} (hℓ'L : ℓ' ∈ S.Lbar ((k : G) * g))
    (hℓ'a : (ℓ' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) :
    cenU S g k ≤ O := by
  refine X.max _ (fun c hc => (mem_cenU.mp hc).1) (fun x hx c hc => conj_mem_cenU hx hc) ?_
  intro c
  have hcc := X.mul_self_mem hLO hℓL hℓ hℓ'L hℓ'a c.2
  obtain ⟨m, hm⟩ := X.isPGroup ⟨(c : S.O) * c, hcc⟩
  refine ⟨m + 1, Subtype.ext ?_⟩
  have h1 : ((c : S.O) * c) ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  rw [Subgroup.coe_pow, OneMemClass.coe_one, pow_succ', pow_mul, _root_.sq]
  exact h1

end Hyp97

end CFSG.LargeExtraspecial.S9
