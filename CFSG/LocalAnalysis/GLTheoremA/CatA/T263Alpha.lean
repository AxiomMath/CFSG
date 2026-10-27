module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263I263
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseAlphaEnd
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDownAux
public import CFSG.Foundations.KCoreClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

@[expose] def T263NotGF2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → ∀ n : ℕ, Odd n → 1 < n →
    (catalogIs (X ⧸ Subgroup.center X) (S10.isU6n n) ∨ catalogIs (X ⧸ Subgroup.center X) (S10.isTE6n n)) →
    ¬ GLAMarking X (fun lab _ _ _ _ _ => lab.n = 1)

theorem normalizer_of_InYK' {G : Type} [Group G] {y : G} {K B : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({y} : Set G)) (hInY : S10.InYK y K B) :
    B ≤ Subgroup.normalizer (K : Set G) := by
  have hcomm : ∀ k ∈ K, y * k = k * y := fun k hk =>
    Subgroup.mem_centralizer_iff.1 (hK hk) y (Set.mem_singleton y)
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have e : y * h * y⁻¹ = h := by
        rw [hcomm h hh]
        group
      rw [e]
      exact hh
    · intro hh
      have e1 : y * (y * h * y⁻¹) = y * h := by
        rw [hcomm _ hh]
        group
      have e2 : y * h * y⁻¹ = h := mul_left_cancel e1
      rw [e2] at hh
      exact hh
  intro g hg
  obtain ⟨i, k, hk, rfl⟩ := hInY g hg
  exact mul_mem (zpow_mem hyN i) (Subgroup.le_normalizer hk)

theorem isGB_of_isGStar' {G : Type} [Group G] [Finite G] {p : ℕ} {B L : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (h : IsGStar p B L) : IsGB p B L := by
  obtain ⟨E, hEB, hE, hcard, hlayer⟩ := h
  refine ⟨E, hEB, hE, hcard, hEB.trans hBN, ?_⟩
  rwa [closureIn_eq_self_of_le hBN] at hlayer

theorem isKGroup_sup_of_i263a {G : Type} [Group G] [Finite G] (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hKp : CFSG.Open.IsKProper G) {y : G} {K B' : Subgroup G}
    {Q : TauCeti.CFSGIndex → Prop}
    (hBel : CFSG.Open.IsElemAbelian 3 B') (hyB : y ∈ B') (hK : GLAPComponent 3 (Subgroup.centralizer ({y} : Set G)) K)
    (hcat : catalogIs (PSimple 3 K) Q) : CFSG.Open.IsKGroup ↥(K ⊔ B') := by
  haveI := hsimp
  by_cases hy1 : y = 1
  · subst hy1
    have htop : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
      ext g
      simp [Subgroup.mem_centralizer_iff]
    have hK' : GLAPComponent 3 (⊤ : Subgroup G) K := htop ▸ hK
    obtain ⟨e⟩ := rtd_nonempty_pSimple_equiv_top Nat.prime_three hnab hK'
    obtain ⟨i, -, ⟨f⟩⟩ := hcat
    have hcatG : IsCatalogGroup G := ⟨i, ⟨e.symm.trans f⟩⟩
    have hGK : CFSG.Open.IsKGroup G :=
      (CFSG.KCore.KProperNonab.kGroupAllSimple_of_isSimpleGroup CFSG.Open.isCatalogGroup_isoInvariant
        CFSG.Assembly.inCatalog_containsAbelianSimple hcatG hKp).kGroupNonab
    exact hGK.subgroup (K ⊔ B')
  · have hZ : Subgroup.center G = ⊥ := CFSG.StandardType.center_eq_bot_of_isSimpleGroup_of_nonabelian hnab
    have hBC : B' ≤ Subgroup.centralizer ({y} : Set G) := isElemAbelian_le_centralizer hBel hyB
    have hKB : K ⊔ B' ≠ ⊤ := by
      intro htop
      apply hy1
      have hle : K ⊔ B' ≤ Subgroup.centralizer ({y} : Set G) := sup_le hK.1 hBC
      rw [htop, top_le_iff] at hle
      have hcen : y ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact ((Subgroup.mem_centralizer_iff.1 (hle ▸ Subgroup.mem_top g)) y (Set.mem_singleton y)).symm
      rw [hZ] at hcen
      exact Subgroup.mem_bot.1 hcen
    exact isKGroup_of_isKProper hKp hKB

theorem i263a_of_facts (hF : T263FactGen) (hex : T263NotGF2) (G : Type) [Group G] [Finite G]
    (hsimp : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hKp : CFSG.Open.IsKProper G)
    (hr : 4 ≤ GLATwoLocalRank 3 G) : I263AlphaAt G := by
  intro y K B' n hBmax hyB hK hInY hodd hn1 hcat hT
  have hBN : B' ≤ Subgroup.normalizer (K : Set G) := normalizer_of_InYK' hK.1 hInY
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  have hc : IsChevSimple 2 (PSimple 3 K) := S10.caseAlphaEnd_chev2 hcat
  have hKgrp : CFSG.Open.IsKGroup ↥(K ⊔ B') := by
    rcases hcat with h | h
    · exact isKGroup_sup_of_i263a hsimp hnab hKp hBmax.1 hyB hK h
    · exact isKGroup_sup_of_i263a hsimp hnab hKp hBmax.1 hyB hK h
  rcases i263_core hF Nat.prime_three (by norm_num) hr hBmax hBN hq hc hKgrp hT with h | ⟨-, hm⟩
  · exact isGB_of_isGStar' hBN h
  · exact absurd hm (hex (PQuot 3 K) hq n hodd hn1 hcat)

end CFSG.LocalAnalysis.GLTheoremA.T263

end
