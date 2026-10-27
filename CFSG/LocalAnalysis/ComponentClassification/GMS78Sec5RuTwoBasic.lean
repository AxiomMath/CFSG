module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuOneBasic
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNormA
public import CFSG.Quasithin.H13.L32ARuOne
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuStein

import CFSG.Mathlib.GroupTheory.PermCenter

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

theorem eq_bot_of_normal_of_isPGroup_perm_five {N : Subgroup (Equiv.Perm (Fin 5))}
    (hN : N.Normal) (hp : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : N.subgroupOf (alternatingGroup (Fin 5)) = ⊥ := by
    have hn : (N.subgroupOf (alternatingGroup (Fin 5))).Normal :=
      Subgroup.normal_subgroupOf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5)))
      with h | h
    · exact h
    · exfalso
      have hle : alternatingGroup (Fin 5) ≤ N := by
        intro x hx
        have : (⟨x, hx⟩ : alternatingGroup (Fin 5)) ∈ N.subgroupOf (alternatingGroup (Fin 5)) :=
          h ▸ mem_top _
        exact this
      have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
        rw [Nat.card_perm, Nat.card_fin, show Nat.factorial 5 = 120 from rfl] at h2
        omega
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      have hdvd : 60 ∣ 2 ^ k := by
        rw [← h60, ← hk]
        exact Subgroup.card_dvd_of_le hle
      have h3 : 3 ∣ 2 ^ k := dvd_trans (by norm_num) hdvd
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hev : ∀ n ∈ N, Equiv.Perm.sign n = 1 → n = 1 := by
    intro n hn hs
    have h1 : (⟨n, Equiv.Perm.mem_alternatingGroup.mpr hs⟩ : alternatingGroup (Fin 5)) ∈
        N.subgroupOf (alternatingGroup (Fin 5)) := hn
    rw [hA, mem_bot] at h1
    exact congrArg Subtype.val h1
  have huniq : ∀ n ∈ N, ∀ m ∈ N, n ≠ 1 → m ≠ 1 → n = m := by
    intro n hn m hm hn1 hm1
    have hsn : Equiv.Perm.sign n = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign n) with h | h
      · exact absurd (hev n hn h) hn1
      · exact h
    have hsm : Equiv.Perm.sign m = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign m) with h | h
      · exact absurd (hev m hm h) hm1
      · exact h
    have h1 := hev _ (mul_mem hn (inv_mem hm)) (by rw [map_mul, map_inv, hsn, hsm]; rfl)
    exact mul_inv_eq_one.mp h1
  rw [eq_bot_iff]
  intro n hn
  rw [mem_bot]
  by_contra hn1
  have hcen : n ∈ Subgroup.center (Equiv.Perm (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g * n * g⁻¹ ∈ N := hN.conj_mem n hn g
    have hg1 : g * n * g⁻¹ ≠ 1 := fun h => hn1 (by
      calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group)
    have h1 := huniq _ hg n hn hg1 hn1
    calc g * n = g * n * g⁻¹ * g := by group
      _ = n * g := by rw [h1]
  rw [CFSG.center_perm_eq_bot_of_three_le_card (α := Fin 5) (by simp), mem_bot] at hcen
  exact hn1 hcen

theorem pCoreOf_eq_of_perm_five {G : Type} [Group G] [Finite G] {H J : Subgroup G}
    (σ : H →* Equiv.Perm (Fin 5)) (hσ : Function.Surjective σ) (hker : σ.ker = J.subgroupOf H)
    (hJH : J ≤ H) (hJ : IsPGroup 2 J) : pCoreOf 2 H = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf 2 hJH (hker ▸ σ.normal_ker) hJ)
  have h0 : CFSG.Open.pCore 2 (Equiv.Perm (Fin 5)) = ⊥ := by
    have : (CFSG.Open.pCore 2 (Equiv.Perm (Fin 5))).Characteristic :=
      CFSG.LieType.BorelTits.pCore_characteristic 2
    exact eq_bot_of_normal_of_isPGroup_perm_five inferInstance
      (CFSG.LieType.BorelTits.pCore_isPGroup 2)
  have h1 : (CFSG.Open.pCore 2 H).map σ = ⊥ :=
    le_bot_iff.mp ((CFSG.LieType.BorelTits.map_pCore_le 2 σ hσ).trans h0.le)
  have h2 : CFSG.Open.pCore 2 H ≤ J.subgroupOf H := hker ▸ (Subgroup.map_eq_bot_iff _).mp h1
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (h2 hx)

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

theorem pCoreOf_normalizer_gmsA_eq
    (hS : SzR G L T R 1 y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hCe : ∀ e ∈ T ⊓ centralizer (L : Set G), e ≠ 1 →
      centralizer ({e} : Set G) = (T ⊓ centralizer (L : Set G)) ⊔ L)
    (hCL : ∀ a ∈ L, a ≠ 1 → a ^ 2 = 1 →
      IsPGroup 2 (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) :
    pCoreOf 2 (normalizer (gmsA L T : Set G)) = R := by
  have hC := centralizer_gmsA_eq hS h34 hR₂ h4 hCV hCe hCL
  have hN := normalizer_gmsA_eq hS h34 hR₂ h4 hCV hCe hCL hNS
  have htop := hS.map_normalizer_eq_top h34 hR₂ h4 hCV hNS
  obtain ⟨e, -⟩ := hS.steinbergCoords h34 hR₂ h4 hNS
  have hLV : normalizer (gmsA L T : Set G) ≤ normalizer (gmsA L T : Set G) := le_rfl
  have hAut : autOn (normalizer (gmsA L T : Set G)) (gmsA L T) = ⊤ := by
    rw [eq_top_iff]
    intro φ _
    obtain ⟨x, -, rfl⟩ := (htop ▸ mem_top φ : φ ∈ ((normalizer (R : Set G)).subgroupOf
      (normalizer (gmsA L T : Set G))).map (gmsA L T).normalizerMonoidHom)
    exact ⟨x, mem_subgroupOf.mpr x.2, rfl⟩
  have hθs := H13.L32A.repV_surjective hLV e hAut
  have hθk : (H13.L32A.repV hLV e).ker = R.subgroupOf (normalizer (gmsA L T : Set G)) := by
    rw [H13.L32A.repV_ker, hC]
  have hRN : R ≤ normalizer (gmsA L T : Set G) := hN ▸ le_normalizer
  exact pCoreOf_eq_of_SL32 _ hθs hθk hRN hS.isR.isPGroup

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
