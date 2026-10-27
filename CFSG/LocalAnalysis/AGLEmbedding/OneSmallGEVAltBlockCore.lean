module

import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltComp
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem D1OneSmallData.zbar_mem_block_of (hd : D1OneSmallData p P M H R Rbar K)
    (hz : D1SmallCZElt p H R K z) (hph : D1PhaseThree p P M H R)
    (hcz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hle : ∀ {Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}, (∀ x ∈ Λ, ∃ k : ℕ, x ^ p ^ k = 1) →
      Λ ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hph.le_M hz.1⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (∀ g : ↥M, (g : G) * z = z * g → QuotientGroup.mk' (CFSG.pCore 2 ↥M) g ∈
        Subgroup.normalizer (Λ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) →
      Λ ≤ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hph.le_M hz.1⟩))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hsup : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hph.le_M hz.1⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hph.le_M hz.1⟩) = p)
    (hnot : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hph.le_M hz.1⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hph.le_M hz.1⟩ ∈ barM M L := by
  have hp := hd.cfg.red.prime
  have hzM : z ∈ M := hph.le_M hz.1
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set zb := mkM ⟨z, hzM⟩
  have hzbp : zb ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one zb
  set 𝓑 : Set (Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    {Lb | ∃ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' ∧ barM M L' = Lb}
  have h𝓑 : ∀ Lb ∈ 𝓑, IsComponentOf Lb ⊤ := by
    rintro _ ⟨L', hL', rfl⟩
    exact hL'.component
  set Λ := Subgroup.closure (lambdaSet p 𝓑 zb)
  have hΛC : Λ ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.closure_le _).mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_lambdaSet_self hl)
  have hΛn : ∀ g : ↥M, (g : G) * z = z * g →
      mkM g ∈ Subgroup.normalizer (Λ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro g hgz
    refine conj_mem_closure_lambdaSet ?_ ?_
    · rw [← map_mul, ← map_mul]
      exact congrArg mkM (Subtype.ext hgz)
    · rintro _ ⟨L', hL', rfl⟩
      have hgH : (g : G) ∈ H := hcz (Subgroup.mem_centralizer_singleton_iff.mpr hgz)
      exact ⟨_, hL'.map_conj g.2 (localGroup_le_normalizer_pCoreOf 2 H hgH),
        barM_map_conj g.2 L'⟩
  have hΛz := hle (fun x hx => exists_pow_eq_one_of_mem_closure_lambdaSet h𝓑 hx) hΛC hΛn
  set Lb := barM M L
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  have hLC : Lb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb C hLC] at hsup
  obtain ⟨l, hl, c, hcC, hlc⟩ := hsup
  have hlz : l⁻¹ * zb ∈ C := by
    have : zb = l * c := hlc.symm
    rw [this]
    simpa using hcC
  obtain ⟨l', hl'L, -, hl'p, hl'c⟩ :=
    exists_pow_mem_of_inv_mul_mem_centralizer hp hzbp hl hlz
  have hl'Λ : l' ∈ Λ := Subgroup.subset_closure ⟨Lb, ⟨L, hL, rfl⟩, hl'L, hl'p, hl'c⟩
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hΛz hl'Λ)
  by_contra hzL
  have h1 : zb ^ (1 - i) ∈ C := by
    rw [zpow_sub, zpow_one, hi]
    have : zb * l'⁻¹ = l'⁻¹ * zb := by
      rw [← hi, ← zpow_neg, ← zpow_one_add, ← zpow_add_one, add_comm]
    rw [this]
    exact hl'c
  have h2 : zb ^ (1 - i) ≠ 1 := by
    intro h
    apply hzL
    have : zb = l' := by
      rw [← hi]
      calc zb = zb ^ (1 - i) * zb ^ i := by rw [← zpow_add, sub_add_cancel, zpow_one]
        _ = zb ^ i := by rw [h, one_mul]
    exact this ▸ hl'L
  have h3 := mem_zpowers_of_mem_zpowers_of_prime hp hord
    (Subgroup.zpow_mem_zpowers zb (1 - i)) h2
  exact hnot ((Subgroup.zpowers_le.mpr h1) h3)

end CFSG.AGLEmbedding
