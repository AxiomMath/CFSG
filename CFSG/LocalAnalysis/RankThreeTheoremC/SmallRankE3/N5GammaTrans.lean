module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4GammaTools
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGStrong
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty Subgroup

theorem n5_hnb {G : Type} [Group G] [Finite G] {p : ℕ} {H D S B L M : Subgroup G} {z : G}
    [hDn : (D.subgroupOf H).Normal] (d3 : KGC.KGData3 p H D S B L M z)
    (hfield : ∀ b ∈ B, b ∉ Subgroup.zpowers z →
      ¬ ((∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ D) ∧ (∀ s ∈ S, b * s * b⁻¹ * s⁻¹ ∈ D))) :
    ∀ b ∈ KGC.img H D B, b ≠ 1 → ¬ ∀ k ∈ KGC.img H D L, b * k = k * b := by
  intro b hb hb1 hbK
  obtain ⟨b', hb'B, rfl⟩ := KGC.mem_img.mp hb
  have c := d3.toData.cfg
  have hbX := KGQ.centralizes_X c hb hbK
  have hzL : KGC.qmk H D ⟨z, d3.toData.z_mem_H⟩ ∈ KGC.img H D L :=
    KGC.mem_img.mpr ⟨⟨z, d3.toData.z_mem_H⟩, d3.toData.z_mem_L, rfl⟩
  have hnot : (b' : G) ∉ Subgroup.zpowers z := by
    intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hbeq : b' = (⟨z, d3.toData.z_mem_H⟩ : ↥H) ^ i :=
      Subtype.ext (by simpa using hi.symm)
    have hbL : KGC.qmk H D b' ∈ KGC.img H D L := by
      rw [hbeq, map_zpow]
      exact Subgroup.zpow_mem _ hzL i
    exact hb1 (KGQ.center_trivial c hbL hbK)
  have h1 : ∀ l ∈ L, (b' : G) * l * (b' : G)⁻¹ * l⁻¹ ∈ D := by
    intro l hl
    obtain ⟨x, rfl⟩ : ∃ x : ↥H, (x : G) = l := ⟨⟨l, d3.toData.L_le_H hl⟩, rfl⟩
    have hxK : KGC.qmk H D x ∈ KGC.img H D L := KGC.mem_img.mpr ⟨x, hl, rfl⟩
    have hcomm := hbK (KGC.qmk H D x) hxK
    have hone : KGC.qmk H D (b' * x * b'⁻¹ * x⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    simpa using KGC.qmk_eq_one_iff.mp hone
  have h2 : ∀ s ∈ S, (b' : G) * s * (b' : G)⁻¹ * s⁻¹ ∈ D := by
    intro s hs
    obtain ⟨x, rfl⟩ : ∃ x : ↥H, (x : G) = s := ⟨⟨s, d3.toData.S_le_H hs⟩, rfl⟩
    have hxS : KGC.qmk H D x ∈ KGC.img H D S := KGC.mem_img.mpr ⟨x, hs, rfl⟩
    have hcomm := hbX (KGC.qmk H D x) (Subgroup.mem_sup_right hxS)
    have hone : KGC.qmk H D (b' * x * b'⁻¹ * x⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    simpa using KGC.qmk_eq_one_iff.mp hone
  exact hfield (b' : G) hb'B hnot ⟨h1, h2⟩

theorem n5_pSolvable_img {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {H D M : Subgroup G} [hDn : (D.subgroupOf H).Normal] (hDH : D ≤ H)
    (hN : H ≤ Subgroup.normalizer (D : Set G)) (hD2 : IsPGroup 2 D) (hDM : D ≤ M)
    {y : G} (hyH : y ∈ H) (hyo : orderOf y = p)
    (hsolv : CFSG.HallHigman.IsPSolvable p ↥(M ⊓ Subgroup.centralizer ({y} : Set G))) :
    CFSG.HallHigman.IsPSolvable p
      ↥(KGC.img H D M ⊓ Subgroup.centralizer ({KGC.qmk H D ⟨y, hyH⟩} : Set (KGC.QA H D))) := by
  have heq : ((M ⊓ Subgroup.centralizer ({y} : Set G) ⊓ H).subgroupOf H).map (KGC.qmk H D) =
      KGC.img H D M ⊓ Subgroup.centralizer ({KGC.qmk H D ⟨y, hyH⟩} : Set (KGC.QA H D)) := by
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
      obtain ⟨⟨hxM, hxC⟩, -⟩ := hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC
      refine Subgroup.mem_inf.mpr ⟨KGC.mem_img.mpr ⟨x, hxM, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxC
    · intro ha
      obtain ⟨ham, hcent⟩ := Subgroup.mem_inf.mp ha
      obtain ⟨m, hmM, rfl⟩ := KGC.mem_img.mp ham
      rw [Subgroup.mem_centralizer_singleton_iff] at hcent
      have hcomm0 : KGC.qmk H D ((⟨y, hyH⟩ : ↥H) * m * (⟨y, hyH⟩ : ↥H)⁻¹ * m⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hcent.symm]
        group
      have hD0 : y * (m : G) * y⁻¹ * (m : G)⁻¹ ∈ D := KGC.qmk_eq_one_iff.mp hcomm0
      obtain ⟨d, hdD, c, hcC, hmdc⟩ :=
        n4_exists_mul_centralizer hp2 hDH hN hD2 hyH hyo m.2 hD0
      have hc_eq : c = d⁻¹ * (m : G) := by
        rw [hmdc, inv_mul_cancel_left]
      have hcM : c ∈ M := by
        rw [hc_eq]
        exact M.mul_mem (M.inv_mem (hDM hdD)) hmM
      have hcH : c ∈ H := by
        rw [hc_eq]
        exact H.mul_mem (H.inv_mem (hDH hdD)) m.2
      have hqd : KGC.qmk H D (⟨d, hDH hdD⟩ : ↥H) = 1 := KGC.qmk_eq_one_iff.mpr hdD
      have hqx : KGC.qmk H D (⟨c, hcH⟩ : ↥H) = KGC.qmk H D m := by
        have hm : m = (⟨d, hDH hdD⟩ : ↥H) * ⟨c, hcH⟩ := Subtype.ext hmdc
        rw [hm, map_mul, hqd, one_mul]
      have hxN : (⟨c, hcH⟩ : ↥H) ∈ ((M ⊓ Subgroup.centralizer ({y} : Set G)) ⊓ H).subgroupOf H :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcM, hcC⟩, hcH⟩)
      exact Subgroup.mem_map.mpr ⟨⟨c, hcH⟩, hxN, hqx⟩
  have hN1 : CFSG.HallHigman.IsPSolvable p
      ↥((M ⊓ Subgroup.centralizer ({y} : Set G) ⊓ H).subgroupOf H) :=
    n4_pSolvable_subgroupOf inf_le_left inf_le_right hsolv
  have hmap := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
    (KGC.qmk H D) hN1
  rw [heq] at hmap
  exact hmap

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
