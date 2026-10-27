module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Open.FusionDefs
import CFSG.Goldschmidt.StrongClosure
import CFSG.Walter.AStar.Subnormal
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.GLS.NT44

set_option autoImplicit false

theorem normal_of_isComponent_of_stronglyClosed_le_of_not_le_centralizer
    {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    {A L : Subgroup G} (hL : CFSG.IsComponent L)
    (hAS : A ≤ (S : Subgroup G)) (hAL : A ≤ L)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set G) (S : Subgroup G))
    (hnot : ¬ A ≤ Subgroup.centralizer (L : Set G)) : L.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ g : G, CFSG.Goldschmidt.conjSub g L = L := by
    intro g
    let Lg : Subgroup G := CFSG.Goldschmidt.conjSub g L
    let B : Subgroup G := CFSG.Goldschmidt.conjSub g A
    have hLg : CFSG.IsComponent Lg := by
      dsimp [Lg, CFSG.Goldschmidt.conjSub]
      exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹) hL
    have hBLg : B ≤ Lg := by
      dsimp [B, Lg, CFSG.Goldschmidt.conjSub]
      exact Subgroup.map_mono hAL
    have hA2 : IsPGroup 2 A := S.2.to_le hAS
    have hB2 : IsPGroup 2 B := by
      dsimp [B, CFSG.Goldschmidt.conjSub]
      exact hA2.map _
    obtain ⟨P, hPmap⟩ :=
      CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal (p := 2) S hLg.2
    obtain ⟨Q, hBQ⟩ := (hB2.comap_subtype (K := Lg)).exists_le_sylow
    have hPis : CFSG.ABGLocalTools.IsSylowOf 2 ((S : Subgroup G) ⊓ Lg) Lg := by
      refine ⟨P, ?_⟩
      rw [hPmap]
    have hQis : CFSG.ABGLocalTools.IsSylowOf 2
        ((Q : Subgroup Lg).map Lg.subtype) Lg := ⟨Q, rfl⟩
    obtain ⟨k, hk, hkconj⟩ :=
      CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hPis hQis
    have hconjSub_le_S : CFSG.Goldschmidt.conjSub k B ≤ (S : Subgroup G) := by
      intro x hx
      have hxB : k * x * k⁻¹ ∈ B := CFSG.Goldschmidt.mem_conjSub.1 hx
      have hkxLg : k * x * k⁻¹ ∈ Lg := hBLg hxB
      have hxLg : x ∈ Lg := by
        have hxeq : x = k⁻¹ * (k * x * k⁻¹) * k := by group
        rw [hxeq]
        exact Lg.mul_mem (Lg.mul_mem (Lg.inv_mem hk) hkxLg) hk
      have hxQ : k * x * k⁻¹ ∈ (Q : Subgroup Lg).map Lg.subtype := by
        refine ⟨⟨k * x * k⁻¹, hkxLg⟩, ?_, rfl⟩
        exact hBQ (by simpa [Subgroup.mem_subgroupOf] using hxB)
      have hxP : k⁻¹ * (k * x * k⁻¹) * k ∈ (S : Subgroup G) ⊓ Lg :=
        (hkconj (k * x * k⁻¹)).1 hxQ
      have hxS : k⁻¹ * (k * x * k⁻¹) * k ∈ (S : Subgroup G) := hxP.1
      have hxeq : k⁻¹ * (k * x * k⁻¹) * k = x := by group
      rwa [hxeq] at hxS
    have hgk_le_S : CFSG.Goldschmidt.conjSub (g * k) A ≤ (S : Subgroup G) := by
      rw [CFSG.Goldschmidt.conjSub_mul]
      simpa [B] using hconjSub_le_S
    have hgk_eq_A : CFSG.Goldschmidt.conjSub (g * k) A = A :=
      CFSG.Goldschmidt.conj_eq_of_conj_le hcl hgk_le_S
    have hA_le_Lg : A ≤ Lg := by
      have hkB_le_Lg : CFSG.Goldschmidt.conjSub k B ≤ Lg := by
        intro x hx
        have hkxB : k * x * k⁻¹ ∈ B := CFSG.Goldschmidt.mem_conjSub.1 hx
        have hkxLg : k * x * k⁻¹ ∈ Lg := hBLg hkxB
        have hxeq : x = k⁻¹ * (k * x * k⁻¹) * k := by group
        rw [hxeq]
        exact Lg.mul_mem (Lg.mul_mem (Lg.inv_mem hk) hkxLg) hk
      intro a ha
      have ha' : a ∈ CFSG.Goldschmidt.conjSub (g * k) A := by
        rwa [hgk_eq_A]
      rw [CFSG.Goldschmidt.conjSub_mul] at ha'
      exact hkB_le_Lg (by simpa [B] using ha')
    rcases CFSG.LocalCores.distinct_components_commute hLg hL with hEq | hComm
    · simpa [Lg] using hEq
    · exfalso
      exact hnot (hA_le_Lg.trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hComm))
  refine ⟨fun n hn g => ?_⟩
  have h := CFSG.Goldschmidt.conj_mem_conjSub (g := g⁻¹) (A := L) hn
  have hgL : CFSG.Goldschmidt.conjSub g⁻¹ L = L := hconj g⁻¹
  simpa [hgL] using h

end CFSG.GH74.GLS.NT44

end
