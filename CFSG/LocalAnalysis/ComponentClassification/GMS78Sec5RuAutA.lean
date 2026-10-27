module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCentA
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGL32

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

theorem isElemAbelian_gmsA_and_card
    (hS : SzR G L T R 1 y d) : IsElemAbelian 2 (gmsA L T) ∧ Nat.card (gmsA L T) = 8 := by
  obtain ⟨-, hVel, -, -, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  obtain ⟨hA₁c, -, -⟩ := hS.facts.sylow hS.sec3
  exact ⟨isElemAbelian_of_le hVel le_sup_left, by rw [hA₁c]; norm_num⟩

theorem map_normalizer_eq_top
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) :
    ((normalizer (R : Set G)).subgroupOf (normalizer (gmsA L T : Set G))).map
      (gmsA L T).normalizerMonoidHom = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAel, h8⟩ := hS.isElemAbelian_gmsA_and_card
  obtain ⟨eA⟩ := CFSG.ComponentClassification.GHarris.nonempty_mulAut_equiv_GL32 hAel h8
  have hNA : normalizer (R : Set G) ≤ normalizer (gmsA L T : Set G) :=
    hS.normalizer_le_normalizer_gmsA hR₂
  set ρ := (gmsA L T).normalizerMonoidHom with hρ
  set H := ((normalizer (R : Set G)).subgroupOf (normalizer (gmsA L T : Set G))).map ρ with hH
  have hmemH : ∀ g (hg : g ∈ normalizer (R : Set G)), ρ ⟨g, hNA hg⟩ ∈ H := fun g hg =>
    ⟨⟨g, hNA hg⟩, mem_subgroupOf.mpr hg, rfl⟩
  have hρ1 : ∀ g (hg : g ∈ normalizer (R : Set G)), ρ ⟨g, hNA hg⟩ = 1 → g ∈ R := by
    intro g hg h1
    rw [← hS.normalizer_inf_centralizer_eq h34 hR₂ h4 hCV]
    refine mem_inf.mpr ⟨hg, mem_centralizer_iff.mpr fun b hb => ?_⟩
    have h2 := congrArg (fun φ : MulAut (gmsA L T) => ((φ ⟨b, hb⟩ : gmsA L T) : G)) h1
    simp only [hρ, normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
    calc b * g = g * b * g⁻¹ * g := by rw [h2]
      _ = g * b := by group
  have h7 : 7 ∣ Nat.card H := by
    have hd : ρ ⟨d, hNA hS.mem_normalizer⟩ = hS.torus.aut := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [hρ, normalizerMonoidHom_apply_apply_coe, IsTorus.aut, normalizerMonoidHom_apply_apply_coe]
      exact hS.conj_eq b (mem_sup_left (mem_inf.mp b.2).1)
    have ho : orderOf hS.torus.aut = 7 := by
      rw [hS.torus.orderOf_aut hS.facts hS.sec3]
      norm_num
    rw [← ho, ← hd]
    exact Subgroup.orderOf_dvd_natCard H (hmemH d hS.mem_normalizer)
  have h2 : 2 ∣ Nat.card H := by
    obtain ⟨S, hS', hRS⟩ := AS76b.exists_isSylowOf_le (le_normalizer : R ≤ normalizer (R : Set G))
      hS.isR.isPGroup
    have hne : R ≠ S := fun h => hNS (by subst h; exact hS')
    obtain ⟨z, hzS, hzR⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hRS hne)
    have hzN : z ∈ normalizer (R : Set G) := hS'.le hzS
    obtain ⟨k, hk⟩ := hS'.isPGroup ⟨z, hzS⟩
    have hzk : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hw1 : ρ ⟨z, hNA hzN⟩ ≠ 1 := fun h => hzR (hρ1 z hzN h)
    have hwk : ρ ⟨z, hNA hzN⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have hz1 : (⟨z, hNA hzN⟩ : normalizer (gmsA L T : Set G)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hzk)
      rw [hz1, map_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hwk)
    rcases j with _ | j
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hj, pow_zero])) hw1
    · exact (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans
        (hj ▸ Subgroup.orderOf_dvd_natCard H (hmemH z hzN))
  have hH' : H.map eA.toMonoidHom = ⊤ := eq_top_of_two_dvd_of_seven_dvd_GL32
    (by rwa [card_map_of_injective eA.injective]) (by rwa [card_map_of_injective eA.injective])
  rw [eq_top_iff]
  intro x _
  obtain ⟨h, hh, hhx⟩ := (hH' ▸ mem_top (eA x) : eA x ∈ H.map eA.toMonoidHom)
  rw [← eA.injective hhx]
  exact hh

theorem relIndex_normalizer_eq
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hCV : centralizer (gmsV L T : Set G) = T)
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) :
    R.relIndex (normalizer (R : Set G)) = 168 := by
  obtain ⟨hAel, h8⟩ := hS.isElemAbelian_gmsA_and_card
  obtain ⟨eA⟩ := CFSG.ComponentClassification.GHarris.nonempty_mulAut_equiv_GL32 hAel h8
  have hNA : normalizer (R : Set G) ≤ normalizer (gmsA L T : Set G) :=
    hS.normalizer_le_normalizer_gmsA hR₂
  set ψ := (gmsA L T).normalizerMonoidHom.comp (inclusion hNA) with hψ
  have hker : ψ.ker = R.subgroupOf (normalizer (R : Set G)) := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h1
      have hmem : (g : G) ∈ normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) := by
        refine mem_inf.mpr ⟨g.2, mem_centralizer_iff.mpr fun b hb => ?_⟩
        have h2 := congrArg (fun φ : MulAut (gmsA L T) => ((φ ⟨b, hb⟩ : gmsA L T) : G)) h1
        simp only [hψ, MonoidHom.coe_comp, Function.comp_apply,
          normalizerMonoidHom_apply_apply_coe, coe_inclusion, MulAut.one_apply] at h2
        calc b * g = g * b * (g : G)⁻¹ * g := by rw [h2]
          _ = g * b := by group
      rwa [hS.normalizer_inf_centralizer_eq h34 hR₂ h4 hCV] at hmem
    · intro hg
      refine MulEquiv.ext fun b => Subtype.ext ?_
      simp only [hψ, MonoidHom.coe_comp, Function.comp_apply, normalizerMonoidHom_apply_apply_coe,
        coe_inclusion, MulAut.one_apply]
      rw [hS.commute_gmsA hg b.2]
      group
  have hrange : ψ.range = ⊤ := by
    have h := hS.map_normalizer_eq_top h34 hR₂ h4 hCV hNS
    rw [eq_top_iff]
    intro x _
    obtain ⟨⟨g, hgA⟩, hg, rfl⟩ := (h ▸ mem_top x : x ∈ ((normalizer (R : Set G)).subgroupOf
      (normalizer (gmsA L T : Set G))).map (gmsA L T).normalizerMonoidHom)
    exact ⟨⟨g, mem_subgroupOf.mp hg⟩, rfl⟩
  have h1 := Subgroup.index_ker ψ
  rw [hker, hrange, card_top, Nat.card_congr eA.toEquiv,
    CFSG.ComponentClassification.GHarris.card_GL32_gh] at h1
  exact h1

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
