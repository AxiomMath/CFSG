module

public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

namespace L29Burnside

section Abstract

theorem exists_index_oResidual_two {H : Type*} [Group H] [Finite H] :
    ∃ b : ℕ, (oResidual 2 H).index = 2 ^ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := Stage1.Thm6.Prod.oResidual_normal 2 H
  have hq : IsPGroup 2 (H ⧸ oResidual 2 H) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, hord⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 2 (by norm_num)
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply Subgroup.subset_closure
    change Nat.Coprime (orderOf (x ^ 2 ^ a)) 2
    rw [orderOf_pow_of_dvd (pow_ne_zero a (by norm_num)) (Dvd.intro _ hord.symm), hord,
      Nat.mul_div_cancel_left m (pow_pos (by norm_num) a)]
    exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)
  exact hq.exists_card_eq

theorem mem_of_odd_orderOf {R : Type*} [Group R] (K : Subgroup R) [K.Normal]
    (hq : IsPGroup 2 (R ⧸ K)) {x : R} (hx : Odd (orderOf x)) : x ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hq (x : R ⧸ K)
  have hd : orderOf (QuotientGroup.mk' K x) ∣ orderOf x := orderOf_map_dvd (QuotientGroup.mk' K) x
  have hmk : orderOf (QuotientGroup.mk' K x) = 2 ^ j := hj
  rw [hmk] at hd
  have h1 : 2 ^ j = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left j hx.coprime_two_right.symm) hd
  have h2 : (QuotientGroup.mk' K x) = 1 := by
    rw [← orderOf_eq_one_iff, hmk, h1]
  exact (QuotientGroup.eq_one_iff x).mp h2

theorem exists_normal_two_compl_of_cyclic {R : Type*} [Group R] [Finite R] (Q : Sylow 2 R)
    (hQ : IsCyclic ↥Q) : ∃ K : Subgroup R, K.Normal ∧ Odd (Nat.card K) ∧
      ∃ j : ℕ, K.index = 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h2 : 2 ∣ Nat.card R
  · have hp : (Nat.card R).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
    have hNC := IsCyclic.normalizer_le_centralizer hp hQ
    refine ⟨(MonoidHom.transferSylow Q hNC).ker, inferInstance, ?_, ?_⟩
    · exact Nat.odd_iff.mpr
        (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow Q hNC))
    · obtain ⟨j, hj⟩ := Q.isPGroup'.exists_card_eq
      exact ⟨j, ((MonoidHom.ker_transferSylow_isComplement' Q hNC).symm.index_eq_card).trans hj⟩
  · refine ⟨⊤, inferInstance, ?_, 0, by simp⟩
    rw [Subgroup.card_top]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)

theorem normal_map_subtype_of_odd {H : Type*} [Group H] (R : Subgroup H) [R.Normal]
    (K : Subgroup R) [K.Normal] (hq : IsPGroup 2 (↥R ⧸ K)) (hK : Odd (Nat.card K)) :
    (K.map R.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hn
  have hmR : g * (k : H) * g⁻¹ ∈ R := Subgroup.Normal.conj_mem inferInstance _ k.2 g
  refine ⟨⟨_, hmR⟩, ?_, rfl⟩
  refine mem_of_odd_orderOf K hq ?_
  have h1 : orderOf (⟨g * (k : H) * g⁻¹, hmR⟩ : ↥R) = orderOf k := by
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe k]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (k : H)
  rw [h1, ← Subgroup.orderOf_mk (H := K) (k : R) hk]
  exact Odd.of_dvd_nat hK (orderOf_dvd_natCard _)

end Abstract

end L29Burnside

section Main

theorem hasNormal2Compl_of_O2_cyclic {G : Type} [Group G] [Finite G] (X : Subgroup G)
    (h : ∃ P : Sylow 2 ↥(O2Of X), IsCyclic ↥P) : HasNormal2Compl X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h
  have hRn : (oResidual 2 ↥X).Normal := Stage1.Thm6.Prod.oResidual_normal 2 ↥X
  let e : ↥(oResidual 2 ↥X) ≃* ↥(O2Of X) :=
    (oResidual 2 ↥X).equivMapOfInjective X.subtype X.subtype_injective
  let Q : Sylow 2 ↥(oResidual 2 ↥X) := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQ : IsCyclic ↥Q :=
    isCyclic_of_surjective ((e.symm.toMonoidHom).subgroupMap (P : Subgroup ↥(O2Of X)))
      (MonoidHom.subgroupMap_surjective _ _)
  obtain ⟨K, hKn, hKodd, j, hj⟩ := L29Burnside.exists_normal_two_compl_of_cyclic Q hQ
  obtain ⟨b, hb⟩ := L29Burnside.exists_index_oResidual_two (H := ↥X)
  have hq : IsPGroup 2 (↥(oResidual 2 ↥X) ⧸ K) := IsPGroup.of_card hj
  have hN := L29Burnside.normal_map_subtype_of_odd (oResidual 2 ↥X) K hq hKodd
  have hsub : ((K.map (oResidual 2 ↥X).subtype).map X.subtype).subgroupOf X =
      K.map (oResidual 2 ↥X).subtype :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  refine ⟨(K.map (oResidual 2 ↥X).subtype).map X.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [hsub]
    exact hN
  · rw [Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.card_map_of_injective (oResidual 2 ↥X).subtype_injective]
    exact hKodd
  · refine ⟨j + b, ?_⟩
    rw [hsub, Subgroup.index_map_subtype, hj, hb, pow_add]

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
