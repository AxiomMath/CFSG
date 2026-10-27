module

import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem mem_centralizer_of_isPGroup_of_card_eq_sq {G : Type*} [Group G] [Finite G] {p r : ℕ}
    [Fact p.Prime] [hr : Fact r.Prime] {Z : Subgroup G} {t : G} (hZ : Nat.card Z = p ^ 2)
    (htZ : t ∈ Subgroup.normalizer (Z : Set G)) (htr : IsPGroup r (Subgroup.zpowers t))
    (hr1 : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1) (hrp : r ≠ p) :
    ∀ z ∈ Z, t * z * t⁻¹ = z := by
  have hp : p.Prime := Fact.out
  set t' : Subgroup.normalizer (Z : Set G) := ⟨t, htZ⟩ with ht'
  set S : Subgroup (Subgroup.normalizer (Z : Set G)) := Subgroup.zpowers t' with hS
  have hSr : IsPGroup r S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp htr
    refine IsPGroup.of_card (n := k) ?_
    rw [hS, Nat.card_zpowers, ht', Subgroup.orderOf_mk, ← Nat.card_zpowers, hk]
  have hmod := hSr.card_modEq_card_fixedPoints Z
  set F : Subgroup Z := FixedPoints.subgroup S Z with hF
  have hFcard : Nat.card (MulAction.fixedPoints S Z) = Nat.card F := rfl
  rw [hFcard, hZ] at hmod
  obtain ⟨i, hi, hFi⟩ := (Nat.dvd_prime_pow hp).mp (hZ ▸ Subgroup.card_subgroup_dvd_card F)
  have hi2 : i = 2 := by
    rw [hFi] at hmod
    have hd := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hp.pos hi)).mp hmod.symm
    interval_cases i
    · exact absurd (by simpa using hd) hr2
    · exfalso
      rw [show p ^ 2 - p ^ 1 = p * (p - 1) by rw [pow_one, sq, Nat.mul_sub_one]] at hd
      rcases (Nat.Prime.dvd_mul hr.out).mp hd with h | h
      · exact hrp ((Nat.prime_dvd_prime_iff_eq hr.out hp).mp h)
      · exact hr1 h
    · rfl
  have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hFi, hi2, hZ])
  intro z hz
  have hmem : (⟨z, hz⟩ : Z) ∈ F := hFtop ▸ Subgroup.mem_top _
  have h := congrArg Subtype.val
    ((FixedPoints.mem_subgroup S Z _).mp hmem ⟨t', Subgroup.mem_zpowers t'⟩)
  have h3 : ((t' • (⟨z, hz⟩ : Z) : Z) : G) = t * z * t⁻¹ := rfl
  simpa [Subgroup.smul_def, h3] using h

section Pair

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem le_of_map_mk_le_of_isPGroup {H U A B : Subgroup G} (hUH : U ≤ H) (hUp : IsPGroup p U)
    (hAU : A ≤ U) (hBU : B ≤ U)
    (hAB : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) : A ≤ B := by
  have hp : p.Prime := Fact.out
  have hUN : U ⊓ GLBPrimeCore p H = ⊥ := inf_eq_bot_of_isPGroup hp hUp (glbPrimeCore_coprime p H)
  intro a ha
  obtain ⟨b, hb, hba⟩ := hAB (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨a, hUH (hAU ha)⟩ ∈ _)
  have hbN : ((b⁻¹ * ⟨a, hUH (hAU ha)⟩ : H) : G) ∈ GLBPrimeCore p H := by
    rw [mem_glbPrimeCore_iff_mk_eq_one, map_mul, map_inv, hba, inv_mul_cancel]
  have hbU : ((b⁻¹ * ⟨a, hUH (hAU ha)⟩ : H) : G) ∈ U := by
    simpa using U.mul_mem (U.inv_mem (hBU (Subgroup.mem_subgroupOf.mp hb))) (hAU ha)
  have h1 : ((b⁻¹ * ⟨a, hUH (hAU ha)⟩ : H) : G) = 1 := by
    have hmem : ((b⁻¹ * ⟨a, hUH (hAU ha)⟩ : H) : G) ∈ U ⊓ GLBPrimeCore p H := ⟨hbU, hbN⟩
    rwa [hUN, Subgroup.mem_bot] at hmem
  have h2 : (a : G) = b := by
    have := congrArg (fun z => (b : G) * z) h1
    simpa using this
  rw [h2]
  exact Subgroup.mem_subgroupOf.mp hb

variable {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

end Pair

end CFSG.AGLEmbedding
