module

public import Mathlib.GroupTheory.Nilpotent
public import TauCeti.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

open scoped Pointwise

theorem y6_frattini {G : Type} [Group G] [Finite G] {N K C : Subgroup G} (hKN : K ≤ N)
    (hKn : (K.subgroupOf N).Normal) (hCK : C ≤ K) (hC : IsPGroup 2 ↥C)
    (hidx : ¬ 2 ∣ C.relIndex K) : N ≤ (normalizer (C : Set G) ⊓ N) ⊔ K := by
  intro n hn
  have hnK : n ∈ normalizer (K : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hKN hn
  let Ck : Subgroup ↥K := C.subgroupOf K
  have hCk : IsPGroup 2 Ck := hC.comap_of_injective K.subtype Subtype.coe_injective
  let D : Subgroup G := C.map (MulAut.conj n : G →* G)
  have hKmap : K.map (MulAut.conj n : G →* G) = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnK
  have hDK : D ≤ K := by
    have hle : C.map (MulAut.conj n : G →* G) ≤ K.map (MulAut.conj n : G →* G) :=
      Subgroup.map_mono hCK
    rwa [hKmap] at hle
  have hD2 : IsPGroup 2 D := hC.map (MulAut.conj n : G →* G)
  have hDrel : D.relIndex K = C.relIndex K := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj n : G →* G)) C K
      (MulAut.conj n).injective
    rwa [hKmap] at h
  let Dk : Subgroup ↥K := D.subgroupOf K
  have hDk : IsPGroup 2 Dk := hD2.comap_of_injective K.subtype Subtype.coe_injective
  have hidxCk : ¬ 2 ∣ Ck.index := hidx
  have hidxDk : ¬ 2 ∣ Dk.index := by
    show ¬ 2 ∣ D.relIndex K
    rw [hDrel]
    exact hidx
  let P₁ : Sylow 2 ↥K := hCk.toSylow hidxCk
  let P₂ : Sylow 2 ↥K := hDk.toSylow hidxDk
  haveI : Finite (Sylow 2 ↥K) := Sylow.finite_of_finiteIndex P₁
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (↥K) P₁ P₂
  have hcoe : MulAut.conj k • Ck = Dk := by
    have h := congrArg (fun Q : Sylow 2 ↥K => (Q : Subgroup ↥K)) hk
    simpa only [P₁, P₂, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using h
  have hsub : (MulAut.conj (k : G) • C).subgroupOf K = D.subgroupOf K := by
    rw [← Subgroup.conj_smul_subgroupOf hCK k]
    simpa only [Ck, Dk] using hcoe
  have hfinal : MulAut.conj (k : G) • C = MulAut.conj n • C := by
    have hinf := Subgroup.subgroupOf_inj.mp hsub
    rw [inf_eq_left.mpr (Subgroup.conj_smul_le_of_le hCK k), inf_eq_left.mpr hDK] at hinf
    rw [← TauCeti.map_conj_eq_conj_smul n C]
    exact hinf
  have hn' : (k : G)⁻¹ * n ∈ normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hsmul : MulAut.conj ((k : G)⁻¹ * n) • C = C := by
      calc MulAut.conj ((k : G)⁻¹ * n) • C
          = ((MulAut.conj (k : G))⁻¹ * MulAut.conj n) • C := by rw [map_mul, map_inv]
        _ = (MulAut.conj (k : G))⁻¹ • (MulAut.conj n • C) := by rw [mul_smul]
        _ = (MulAut.conj (k : G))⁻¹ • (MulAut.conj (k : G) • C) := by rw [← hfinal]
        _ = C := inv_smul_smul _ _
    exact hsmul
  have hkK : (k : G) ∈ K := k.2
  have hknN : (k : G)⁻¹ * n ∈ N := N.mul_mem (N.inv_mem (hKN k.2)) hn
  have hkn : (k : G)⁻¹ * n ∈ normalizer (C : Set G) ⊓ N := ⟨hn', hknN⟩
  have hmem : (k : G) * ((k : G)⁻¹ * n) ∈ K ⊔ (normalizer (C : Set G) ⊓ N) :=
    Subgroup.mul_mem_sup hkK hkn
  have heq : (k : G) * ((k : G)⁻¹ * n) = n := by group
  rw [heq] at hmem
  rwa [sup_comm] at hmem

theorem y6_sylow_of_self_normalizing {G : Type} [Group G] [Finite G] {K C : Subgroup G}
    (hCK : C ≤ K) (hC : IsPGroup 2 ↥C)
    (hN : ∀ x ∈ K, x ∈ normalizer (C : Set G) → x ∈ C) : ¬ 2 ∣ C.relIndex K := by
  let Ck : Subgroup ↥K := C.subgroupOf K
  have hCk : IsPGroup 2 Ck := hC.comap_of_injective K.subtype Subtype.coe_injective
  obtain ⟨P, hCkP⟩ := hCk.exists_le_sylow
  by_cases hEq : Ck = (P : Subgroup ↥K)
  · have hidx : C.relIndex K = (P : Subgroup ↥K).index := by
      rw [show C.relIndex K = Ck.index from rfl, hEq]
    rw [hidx]
    exact P.not_dvd_index
  · exfalso
    let H : Subgroup ↥(P : Subgroup ↥K) := Ck.subgroupOf (P : Subgroup ↥K)
    have hHlt : H < ⊤ := by
      change Ck.subgroupOf (P : Subgroup ↥K) < ⊤
      rw [lt_top_iff_ne_top]
      intro htop
      have hPC : (P : Subgroup ↥K) ≤ Ck := by
        intro y hy
        have hy' : (⟨y, hy⟩ : ↥(P : Subgroup ↥K)) ∈ H := by
          change (⟨y, hy⟩ : ↥(P : Subgroup ↥K)) ∈ Ck.subgroupOf (P : Subgroup ↥K)
          rw [htop]
          trivial
        exact Subgroup.mem_subgroupOf.mp hy'
      exact hEq (le_antisymm hCkP hPC)
    haveI : Group.IsNilpotent ↥(P : Subgroup ↥K) := IsPGroup.isNilpotent P.isPGroup'
    have hNC := Group.normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup ↥K))
    obtain ⟨x, hx_norm, hx_not⟩ := SetLike.exists_of_lt (hNC H hHlt)
    have hxK_norm : (x : ↥K) ∈ normalizer Ck := by
      have h1 : x ∈ (normalizer Ck).subgroupOf (P : Subgroup ↥K) := by
        rw [Subgroup.subgroupOf_normalizer_eq hCkP]
        exact hx_norm
      exact Subgroup.mem_subgroupOf.mp h1
    have hxG_norm : (x : G) ∈ normalizer (C : Set G) := by
      have h2 : (x : ↥K) ∈ (normalizer (C : Set G)).subgroupOf K := by
        rw [Subgroup.subgroupOf_normalizer_eq hCK]
        exact hxK_norm
      exact Subgroup.mem_subgroupOf.mp h2
    have hxK : (x : G) ∈ K := (x : ↥K).2
    have hxC : (x : G) ∈ C := hN (x : G) hxK hxG_norm
    have hxH : x ∈ H := by
      show (x : ↥K) ∈ Ck
      exact Subgroup.mem_subgroupOf.mpr hxC
    exact hx_not hxH

end CFSG.OddStandard.HigherRank.YamadaG23
