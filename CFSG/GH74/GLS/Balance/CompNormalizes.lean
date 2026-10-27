module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG
open scoped commutatorElement

namespace Comp

theorem false_of_odd_quotient_center {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hodd : Odd (Nat.card (Q ⧸ center Q))) : False := by
  have hsolv : Group.IsSolvable (Q ⧸ center Q) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hQ
  have hnt : Nontrivial (Q ⧸ center Q) := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  exact Group.IsPerfect.not_isSolvable (Q ⧸ center Q) hsolv

theorem exists_sylow_of_maximal {X : Type*} [Group X] [Finite X] {E Q : Subgroup X} (hQE : Q ≤ E)
    (hQ2 : IsPGroup 2 Q)
    (hQs : ∀ T : Subgroup X, T ≤ E → IsPGroup 2 T → Nat.card T ≤ Nat.card Q) :
    ∃ S : Sylow 2 E, (S : Subgroup E).map E.subtype = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (Q.subgroupOf E).map E.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQE]
  have hQ' : IsPGroup 2 (Q.subgroupOf E) := hQ2.comap_of_injective E.subtype E.subtype_injective
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  have hcardQ : Nat.card (Q.subgroupOf E) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv
  have hle : Nat.card (S : Subgroup E) ≤ Nat.card (Q.subgroupOf E) := by
    have h1 : Nat.card ((S : Subgroup E).map E.subtype) ≤ Nat.card Q :=
      hQs _ (Subgroup.map_subtype_le _) (S.isPGroup'.map E.subtype)
    rwa [Subgroup.card_map_of_injective E.subtype_injective, ← hcardQ] at h1
  have heq : Q.subgroupOf E = S := Subgroup.eq_of_le_of_card_ge hS hle
  exact ⟨S, by rw [← heq, hmap]⟩

theorem exists_sylow_map_eq_inf {X : Type*} [Group X] [Finite X] {E K Q : Subgroup X} (hKE : K ≤ E)
    (hKn : (K.subgroupOf E).Normal) (hQE : Q ≤ E) (hQ2 : IsPGroup 2 Q)
    (hQs : ∀ T : Subgroup X, T ≤ E → IsPGroup 2 T → Nat.card T ≤ Nat.card Q) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype = Q ⊓ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := exists_sylow_of_maximal hQE hQ2 hQs
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_eq_subgroupOf_of_normal S₀ (K.subgroupOf E)
  let e : K.subgroupOf E ≃* K := Subgroup.subgroupOfEquivOfLe hKE
  have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  refine ⟨P.mapSurjective he, ?_⟩
  rw [Sylow.coe_mapSurjective, hP]
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨x, ⟨x₁, hx₁, rfl⟩, rfl⟩
    refine ⟨?_, x₁.2⟩
    rw [← hS₀]
    exact ⟨(x₁ : E), hx₁, rfl⟩
  · rintro ⟨hyQ, hyK⟩
    rw [← hS₀] at hyQ
    obtain ⟨s, hs, rfl⟩ := hyQ
    exact ⟨e.toMonoidHom ⟨s, hyK⟩, ⟨⟨s, hyK⟩, hs, rfl⟩, rfl⟩

theorem false_of_central_sylow {X : Type*} [Group X] [Finite X] {K : Subgroup X} (hK : IsComponent K)
    (S : Sylow 2 K) (hS : ∀ y ∈ (S : Subgroup K).map K.subtype, ∀ k ∈ K, k * y = y * k) : False := by
  have hle : (S : Subgroup K) ≤ center K := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hS _ (Subgroup.mem_map_of_mem _ hy) k k.2)
  have hodd : ¬ 2 ∣ (center K).index := fun h =>
    Sylow.not_dvd_index S (h.trans (Subgroup.index_dvd_of_le hle))
  have hodd' : Odd (Nat.card (K ⧸ center K)) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  exact false_of_odd_quotient_center hK.1 hodd'

end Comp

variable {X : Type} [Group X] [Finite X]

theorem mem_normalizer_of_centralizes_sylow {K : Subgroup X} (hK : IsComponent K) (Q : Subgroup X)
    (hQE : Q ≤ layer X) (hQ2 : IsPGroup 2 Q)
    (hQs : ∀ T : Subgroup X, T ≤ layer X → IsPGroup 2 T → Nat.card T ≤ Nat.card Q)
    {c : X} (hc : c ∈ centralizer (Q : Set X)) : c ∈ normalizer (K : Set X) := by
  by_contra hcK
  have hKc : IsComponent (K.map (MulAut.conj c).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj c) hK
  have hne : K ≠ K.map (MulAut.conj c).toMonoidHom := by
    intro h
    apply hcK
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h.symm
  have hcomm := (CFSG.LocalCores.distinct_components_commute hK hKc).resolve_left hne
  have hKE := CFSG.LocalCores.components_normal_in_layer hK
  obtain ⟨S, hS⟩ := Comp.exists_sylow_map_eq_inf hKE.1 hKE.2 hQE hQ2 hQs
  refine Comp.false_of_central_sylow hK S ?_
  intro y hy k hk
  rw [hS] at hy
  have hyc : c * y * c⁻¹ = y := by
    rw [← mem_centralizer_iff.mp hc y hy.1, mul_inv_cancel_right]
  have hyKc : y ∈ K.map (MulAut.conj c).toMonoidHom := ⟨y, hy.2, hyc⟩
  have hKc' : K.map (MulAut.conj c).toMonoidHom ≤ centralizer (K : Set X) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  exact mem_centralizer_iff.mp (hKc' hyKc) k hk

end CFSG.GH74.GLS.Balance
