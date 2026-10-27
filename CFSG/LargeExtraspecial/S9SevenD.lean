module

public import CFSG.LargeExtraspecial.S8Rad
public import CFSG.LargeExtraspecial.S9SevenA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G]

structure Hyp97 (S : Setting G) (g : G) (k : S.M) (O : Subgroup S.O) : Prop where
  hyp4 : Hyp4 S g
  cons : Cons311 S g
  le : O ≤ S.Lbar g ⊔ S.Lbar ((k : G) * g)
  normal : ∀ x ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g), ∀ o ∈ O, x * o * x⁻¹ ∈ O
  isPGroup : IsPGroup 2 O
  max : ∀ P : Subgroup S.O, P ≤ S.Lbar g ⊔ S.Lbar ((k : G) * g) →
    (∀ x ∈ S.Lbar g ⊔ S.Lbar ((k : G) * g), ∀ p ∈ P, x * p * x⁻¹ ∈ P) → IsPGroup 2 P → P ≤ O
  inf_ne_bot : S.Lbar g ⊓ O ≠ ⊥

namespace Hyp97

variable {S : Setting G} {g : G} {k : S.M} {O : Subgroup S.O} (X : Hyp97 S g k O)
include X

theorem fix_Ut {o : S.O} (ho : o ∈ O) {u : S.Qt}
    (hu : u ∈ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g))) :
    (o : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u :=
  fix_Ut_of_normal X.hyp4 le_sup_left X.le X.normal X.isPGroup ho hu

omit X in
theorem exists_ell (hidx : Nat.card (S.Lbar g) = 2 * Nat.card (S.Lbar g ⊓ O : Subgroup S.O)) :
    ∃ ℓ ∈ S.Lbar g, ℓ ∉ O ∧ ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O := by
  set K := (S.Lbar g ⊓ O).subgroupOf (S.Lbar g) with hK
  have hKc : Nat.card K = Nat.card (S.Lbar g ⊓ O : Subgroup S.O) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := K.card_mul_index
  rw [hKc, hidx] at hmul
  have hpos : 0 < Nat.card (S.Lbar g ⊓ O : Subgroup S.O) := Nat.card_pos
  have hI : K.index = 2 := by nlinarith
  have hmemK : ∀ y : S.Lbar g, y ∈ K ↔ (y : S.O) ∈ O := fun y => by
    rw [hK, mem_subgroupOf]
    exact ⟨fun h => (mem_inf.mp h).2, fun h => mem_inf.mpr ⟨y.2, h⟩⟩
  have hne : K ≠ ⊤ := fun h => by rw [h, index_top] at hI; omega
  obtain ⟨y, hy⟩ : ∃ y : S.Lbar g, y ∉ K := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.mpr fun y _ => hcon y)
  refine ⟨y, y.2, fun h => hy ((hmemK y).mpr h), fun l hl hlO => ?_⟩
  have hl' : (⟨l, hl⟩ : S.Lbar g) ∉ K := fun h => hlO ((hmemK _).mp h)
  have hiff : (y⁻¹ ∈ K ↔ (⟨l, hl⟩ : S.Lbar g) ∈ K) :=
    ⟨fun h => absurd (by simpa using inv_mem h) hy, fun h => absurd h hl'⟩
  have := (mul_mem_iff_of_index_two hI).mpr hiff
  exact (hmemK _).mp this

theorem mem_span_of_fix {ℓ : S.O} (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) {u : S.Qt}
    (hu : u ∈ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)))
    (hℓu : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) : u ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  rw [← X.hyp4.fixSub_eq]
  refine (mem_fixSub S).mpr fun l hl => ?_
  by_cases hlO : l ∈ O
  · exact X.fix_Ut hlO hu
  · have h1 := X.fix_Ut (hℓ l hl hlO) hu
    have e : l = ℓ * (ℓ⁻¹ * l) := by group
    rw [e, Subgroup.coe_mul, LinearEquiv.mul_apply, h1, hℓu]

theorem apply_sub_mem_span {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) {u : S.Qt}
    (hu : u ∈ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g))) :
    (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  have hℓℓ : ℓ * ℓ = 1 := mul_self_of_mem_Lbar S X.hyp4.conj_mem hℓL
  refine X.mem_span_of_fix hℓ (sub_mem (apply_mem_Ut (mem_sup_left hℓL) hu) hu) ?_
  have h2 : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = u := by
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hℓℓ]
    rfl
  rw [map_sub, h2]
  have h3 : u - (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) u = -((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by abel
  rw [h3, ZModModule.neg_eq_self]

theorem cl_ne (hLO : ¬ S.Lbar g ≤ O) :
    S.cl (g * S.z * g⁻¹) ≠ S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  intro he
  have hL := Lbar_eq_of_cl_eq S X.hyp4.conj_mem X.hyp4.conj_ne (X.hyp4.mul k).conj_mem he.symm
  apply hLO
  have hXL : S.Lbar g ⊔ S.Lbar ((k : G) * g) = S.Lbar g := by rw [← hL, sup_idem]
  refine le_sup_left.trans (X.max _ le_rfl (fun x hx p hp => mul_mem (mul_mem hx hp)
    (inv_mem hx)) ?_)
  rw [hXL]
  exact isPGroup_Lbar S X.hyp4.conj_mem

theorem finrank_Ut_eq_two (hLO : ¬ S.Lbar g ≤ O) {ℓ : S.O} (hℓL : ℓ ∈ S.Lbar g)
    (hℓ : ∀ l ∈ S.Lbar g, l ∉ O → ℓ⁻¹ * l ∈ O) :
    S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) ∧
      finrank (ZMod 2) ↥(Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g))) = 2 := by
  set U := Ut S g (S.Lbar g ⊔ S.Lbar ((k : G) * g)) with hU
  have H := X.hyp4
  have ha0 := cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  have haU : S.cl (g * S.z * g⁻¹) ∈ U := cl_mem_Ut _
  have hU0 : U ≠ ⊥ := fun h0 => ha0 ((Submodule.mem_bot _).mp (h0 ▸ haU))
  have hbU : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ U :=
    cl_mem_of_invariant (H.mul k) le_sup_right (fun x hx w hw => apply_mem_Ut hx hw) hU0
  refine ⟨hbU, le_antisymm ?_ ?_⟩
  ·
    set f := (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1 with hf
    have hk := S8.finrank_map_add_finrank_inf_ker f U
    have h1 : U ⊓ LinearMap.ker f ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
      intro u hu
      obtain ⟨huU, huk⟩ := Submodule.mem_inf.mp hu
      refine X.mem_span_of_fix hℓ huU ?_
      have : f u = 0 := huk
      exact sub_eq_zero.mp this
    have h2 : U.map f ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
      rintro _ ⟨u, hu, rfl⟩
      exact X.apply_sub_mem_span hℓL hℓ hu
    have h3 := Submodule.finrank_mono h1
    have h4 := Submodule.finrank_mono h2
    rw [finrank_span_singleton ha0] at h3 h4
    omega
  ·
    have hab := X.cl_ne hLO
    have hli : LinearIndependent (ZMod 2) ![S.cl (g * S.z * g⁻¹),
        S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)] := by
      refine (LinearIndependent.pair_iff' ha0).mpr fun c hc => ?_
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul] at hc
        exact cl_conj_z_ne_zero S (H.mul k).conj_mem (H.mul k).conj_ne hc.symm
      · rw [one_smul] at hc
        exact hab hc
    have hle : Submodule.span (ZMod 2) {S.cl (g * S.z * g⁻¹),
        S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)} ≤ U := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨cl_mem_Ut _, hbU⟩
    have := Submodule.finrank_mono hle
    rwa [finrank_span_pair hli] at this

end Hyp97

end CFSG.LargeExtraspecial.S9
