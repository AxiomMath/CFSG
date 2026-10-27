module

public import CFSG.LargeExtraspecial.AS62C36Planes
public import CFSG.LargeExtraspecial.AS62C36NormMem

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

namespace AS62

variable {G : Type} [Group G] [Finite G] {S : Setting G} {H : Subgroup G}

namespace ConfHyp

private noncomputable abbrev actSubspace (S : Setting G) :
    MulAction S.M (Submodule (ZMod 2) S.Qt) where
  smul m U := U.map (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)
  one_smul U := by
    change U.map (((S.ρ 1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = U
    rw [map_one]
    exact Submodule.map_id U
  mul_smul a b U := by
    change U.map (((S.ρ (a * b) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      (U.map (((S.ρ b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)).map
        (((S.ρ a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)
    rw [map_mul, ← Submodule.map_comp]
    rfl

theorem relIndex_inf_normalizer_V_le_three (hc : ConfHyp S H) (h : W2Hyp S) :
    (normalizer ((closure (S.zConj H) : Subgroup G) : Set G)).relIndex S.M ≤ 3 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨t, ht, htz⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
  have htM := hc.mem_M_of_mem ht
  obtain ⟨hA, -, -⟩ := hc.fiveOne ht htz
  obtain ⟨-, -, -, htD⟩ := hc.exists_conj_eq ht htz
  set ℓ := commSpace (S.rhoL htM)
  have hℓ2 : finrank (ZMod 2) ℓ = 2 := hA.2.2.2.1
  have hℓq : ∀ x ∈ ℓ, S.q x = 0 := hA.2.2.2.2
  letI := actSubspace S
  set X : Set (Submodule (ZMod 2) S.Qt) :=
    {U | finrank (ZMod 2) U = 2 ∧ (∀ v ∈ U, S.q v = 0) ∧ U ⊓ ℓ = ⊥}
  have hstab : MulAction.stabilizer S.M ℓ =
      (normalizer ((closure (S.zConj H) : Subgroup G) : Set G)).subgroupOf S.M := by
    ext m
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, hc.mem_normalizer_V_iff ht htz m.2]
    rfl
  have horb : MulAction.orbit S.M ℓ ⊆ insert ℓ X := by
    rintro _ ⟨m, rfl⟩
    have hmt : (m : G) * t * (m : G)⁻¹ ∈ S.M := mul_mem (mul_mem m.2 htM) (inv_mem m.2)
    have hDm := S.conj_mem_DSet m.2 htD
    obtain ⟨hA', -, -⟩ := S.fiveOne_two hc.sixFourConcl hc.hW hDm hmt
    have hU : m • ℓ = commSpace (S.rhoL hmt) := (commSpace_rhoL_conj m.2 htM hmt).symm
    change m • ℓ ∈ insert ℓ X
    rw [hU]
    set U := commSpace (S.rhoL hmt)
    have hne : finrank (ZMod 2) ↥(ℓ ⊓ U) ≠ 1 := fun h1 =>
      false_of_two_lines hc.h22 h htD hDm htM hmt h1
    have hle : finrank (ZMod 2) ↥(ℓ ⊓ U) ≤ 2 := (Submodule.finrank_mono inf_le_left).trans hℓ2.le
    rcases (by omega : finrank (ZMod 2) ↥(ℓ ⊓ U) = 0 ∨ finrank (ZMod 2) ↥(ℓ ⊓ U) = 2) with h0 | h2
    · right
      refine ⟨hA'.2.2.2.1, hA'.2.2.2.2, ?_⟩
      rw [inf_comm]
      exact Submodule.finrank_eq_zero.mp h0
    · left
      have e : ℓ ⊓ U = ℓ := Submodule.eq_of_le_of_finrank_eq inf_le_left (h2.trans hℓ2.symm)
      exact (Submodule.eq_of_le_of_finrank_eq (inf_eq_left.mp e)
        (hℓ2.trans hA'.2.2.2.1.symm)).symm
  have hXcard : X.ncard ≤ 2 :=
    ncard_tsPlane_inf_eq_bot_le_two (q := S.q) hc.finrank_Qt S.q_nondegenerate hℓ2 hℓq
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer]
  calc (MulAction.orbit S.M ℓ).ncard ≤ (insert ℓ X).ncard :=
        Set.ncard_le_ncard horb (Set.toFinite _)
    _ ≤ X.ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ 3 := by omega

theorem card_M_inf_normalizer_V_le (hc : ConfHyp S H) :
    Nat.card ↥(S.M ⊓ normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) ≤ 384 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨t, ht, htz⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
  obtain ⟨hA, -, -⟩ := hc.fiveOne ht htz
  set N := normalizer ((closure (S.zConj H) : Subgroup G) : Set G)
  set K : Subgroup S.M := N.subgroupOf S.M with hK
  have hcard : Nat.card ↥(S.M ⊓ N) = Nat.card K := by
    rw [inf_comm, hK, ← inf_subgroupOf_right,
      Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
  have hker : Nat.card ↥(K ⊓ S.ρ.ker) ≤ 32 :=
    (card_le_of_le inf_le_right).trans
      (by rw [S.ker_ρ, ← S.card_QG_eq_card_Q, hc.card_QG])
  have himg : Nat.card ↥(K.map S.ρ) ≤ 12 := by
    have h12 := card_le_twelve_of_map_eq (q := S.q) hc.finrank_Qt S.q_nondegenerate hA.2.2.2.1
      hA.2.2.2.2 ((K.map S.ρ).map S.O.subtype) (map_subtype_le _) ?_
    · rwa [card_map_of_injective S.O.subtype_injective] at h12
    · rintro σ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact (hc.mem_normalizer_V_iff ht htz k.2).mp (mem_subgroupOf.mp hk)
  have h1 := Setting.card_eq_relIndex_mul K S.ρ.ker
  rw [relIndex_ker] at h1
  rw [hcard, h1]
  exact (Nat.mul_le_mul himg hker).trans (by norm_num)

theorem card_M_inf_normalizer_V (hc : ConfHyp S H) (h : W2Hyp S) (h36 : Nat.card S.Mbar = 36) :
    Nat.card ↥(S.M ⊓ normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) = 384 := by
  have h1 := Setting.card_eq_relIndex_mul S.M
    (normalizer ((closure (S.zConj H) : Subgroup G) : Set G))
  have h2 := card_M_eq_card_QG_mul S
  rw [hc.card_QG, h36] at h2
  have h3 := Nat.mul_le_mul_right
    (Nat.card ↥(S.M ⊓ normalizer ((closure (S.zConj H) : Subgroup G) : Set G)))
    (hc.relIndex_inf_normalizer_V_le_three h)
  have h4 := hc.card_M_inf_normalizer_V_le
  omega

theorem card_normalizer_V_of_card_Mbar (hc : ConfHyp S H) (h : W2Hyp S)
    (h36 : Nat.card S.Mbar = 36) :
    Nat.card (normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) = 1920 := by
  rw [hc.card_normalizer_V, inf_comm, hc.card_M_inf_normalizer_V h h36]

end ConfHyp

end AS62

end CFSG.LargeExtraspecial
