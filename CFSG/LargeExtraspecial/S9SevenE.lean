module

public import CFSG.LargeExtraspecial.S9SevenD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G]

namespace Hyp97

variable {S : Setting G} {g : G} {k : S.M} {O : Subgroup S.O} (X : Hyp97 S g k O)
include X

theorem Ut_eq_span (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) :
    Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) = Submodule.span (ZMod 2)
      {S.cl (g * S.z * g⁻¹), S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)} := by
  obtain ⟨hbU, hdim⟩ := X.finrank_Ut_eq_two hLO hℓL hℓ
  have H := X.hyp4
  have ha0 := cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  have hli : LinearIndependent (ZMod 2) ![S.cl (g * S.z * g⁻¹),
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)] := by
    refine (LinearIndependent.pair_iff' ha0).mpr fun c hc => ?_
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [zero_smul] at hc
      exact cl_conj_z_ne_zero S (H.mul k).conj_mem (H.mul k).conj_ne hc.symm
    · rw [one_smul] at hc
      exact X.cl_ne hLO hc
  have hle : Submodule.span (ZMod 2) {S.cl (g * S.z * g⁻¹),
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)} ≤ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) := by
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨cl_mem_Ut _, hbU⟩
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_pair hli, hdim]

omit X in
theorem fix_of_fix_pair {S : Setting G} {g : G} {k : S.M} {y : S.O}
    (hya : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    (hyb : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) {u : S.Qt}
    (hu : u ∈ Submodule.span (ZMod 2)
      {S.cl (g * S.z * g⁻¹), S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)}) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hu
  rw [map_add, map_smul, map_smul, hya, hyb]

theorem apply_cl_a_of_mem_Lbar {l : S.O} (hl : l ∈ S.Lbar g) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  have : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
    rw [X.hyp4.fixSub_eq]; exact Submodule.mem_span_singleton_self _
  exact (mem_fixSub S).mp this l hl

theorem apply_cl_b_of_mem_Lbar_mul {l : S.O} (hl : l ∈ S.Lbar ((k : G) * g)) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  have : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ fixSub S (S.Lbar ((k : G) * g)) := by
    rw [(X.hyp4.mul k).fixSub_eq]; exact Submodule.mem_span_singleton_self _
  exact (mem_fixSub S).mp this l hl

theorem apply_cl_b_eq (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) :
    (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  obtain ⟨hbU, hdim⟩ := X.finrank_Ut_eq_two hLO hℓL hℓ
  have hspan := X.Ut_eq_span hLO hℓL hℓ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (X.apply_sub_mem_span hℓL hℓ hbU)
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · exfalso
    rw [zero_smul, eq_comm, sub_eq_zero] at hc
    have hle : Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
      intro u hu
      refine X.mem_span_of_fix hℓ hu ?_
      rw [hspan] at hu
      exact fix_of_fix_pair (X.apply_cl_a_of_mem_Lbar hℓL) hc hu
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton (cl_conj_z_ne_zero S X.hyp4.conj_mem X.hyp4.conj_ne)] at h1
    omega
  · rw [one_smul] at hc
    rw [hc]
    abel

theorem apply_cl_a_eq (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) {l : S.O} (hl : l ∈ S.Lbar ((k : G) * g))
    (hla : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ S.cl (g * S.z * g⁻¹)) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  have H := X.hyp4
  obtain ⟨hbU, hdim⟩ := X.finrank_Ut_eq_two hLO hℓL hℓ
  have hspan := X.Ut_eq_span hLO hℓL hℓ
  set a := S.cl (g * S.z * g⁻¹) with ha
  set b := S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) with hb
  set d := (l : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a with hd
  have hll : l * l = 1 := mul_self_of_mem_Lbar S (H.mul k).conj_mem hl
  have hdU : d ∈ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) :=
    sub_mem (apply_mem_Ut (mem_sup_right hl) (cl_mem_Ut _)) (cl_mem_Ut _)
  have hd0 : d ≠ 0 := fun h => hla (sub_eq_zero.mp h)
  have hld : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) d = d := by
    have h2 : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) a) = a := by
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hll]
      rfl
    rw [hd, map_sub, h2]
    have h3 : a - (l : S.Qt ≃ₗ[ZMod 2] S.Qt) a = -((l : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a) := by abel
    rw [h3, ZModModule.neg_eq_self]
  have hdb : d = b := by
    by_contra hne
    have hb0 : b ≠ 0 := cl_conj_z_ne_zero S (H.mul k).conj_mem (H.mul k).conj_ne
    have hli : LinearIndependent (ZMod 2) ![b, d] := by
      refine (LinearIndependent.pair_iff' hb0).mpr fun c hc => ?_
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul] at hc
        exact hd0 hc.symm
      · rw [one_smul] at hc
        exact hne hc.symm
    have hle : Submodule.span (ZMod 2) {b, d} ≤ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hbU, hdU⟩
    have heq : Submodule.span (ZMod 2) {b, d} = Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_pair hli, hdim])
    apply hla
    have haU : a ∈ Submodule.span (ZMod 2) {b, d} := by rw [heq]; exact cl_mem_Ut _
    obtain ⟨c, e, he⟩ := Submodule.mem_span_pair.mp haU
    rw [← he, map_add, map_smul, map_smul, X.apply_cl_b_of_mem_Lbar_mul hl, hld]
  rw [← hdb, hd]
  abel

theorem exists_ell' (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) :
    ∃ ℓ' ∈ S.Lbar ((k : G) * g), (ℓ' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  have hspan := X.Ut_eq_span hLO hℓL hℓ
  by_contra hcon
  push Not at hcon
  have hfa : ∀ l ∈ S.Lbar ((k : G) * g),
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
    intro l hl
    by_contra hla
    exact hcon l hl (X.apply_cl_a_eq hLO hℓL hℓ hl hla)
  have hmem : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar ((k : G) * g)) :=
    (mem_fixSub S).mpr fun l hl => hfa l hl
  rw [(X.hyp4.mul k).fixSub_eq] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul] at hc
    exact cl_conj_z_ne_zero S X.hyp4.conj_mem X.hyp4.conj_ne hc.symm
  · rw [one_smul] at hc
    exact X.cl_ne hLO hc.symm

theorem exists_conj (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) {ℓ' : S.O} (hℓ'L : ℓ' ∈ S.Lbar ((k : G) * g))
    (hℓ'a : (ℓ' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) :
    S.Lbar ((k : G) * g) = (S.Lbar g).map (MulAut.conj (ℓ * ℓ')).toMonoidHom := by
  have H := X.hyp4
  have hx : ((ℓ * ℓ' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hℓ'a, map_add, X.apply_cl_a_of_mem_Lbar hℓL,
      X.apply_cl_b_eq hLO hℓL hℓ, ← add_assoc, vec_add_self, zero_add]
  have hxM : ℓ * ℓ' ∈ S.Mbar := mul_mem (S.Lbar_le_Mbar g hℓL) (S.Lbar_le_Mbar _ hℓ'L)
  obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp hxM
  rw [← hj] at hx ⊢
  rw [← Lbar_mul S j g]
  rw [ρ_cl_conj_z S j H.conj_mem] at hx
  exact Lbar_eq_of_cl_eq S (H.mul j).conj_mem (H.mul j).conj_ne (H.mul k).conj_mem hx.symm

end Hyp97

end CFSG.LargeExtraspecial.S9
