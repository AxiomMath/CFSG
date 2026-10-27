module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Frob

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem y6_O2_le {G : Type} [Group G] [Finite G] {N A M : Subgroup G} (hAN : A ≤ N)
    (hfrob : SecProp N A (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y)) (hMN : M ≤ N)
    (hMnorm : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) (hM2 : IsPGroup 2 ↥M) : M ≤ A := by
  obtain ⟨hAnorm, hfr⟩ := hfrob
  haveI := hAnorm
  let π : ↥N →* ↥N ⧸ A.subgroupOf N := QuotientGroup.mk' (A.subgroupOf N)
  let P : Subgroup (↥N ⧸ A.subgroupOf N) := (M.subgroupOf N).map π
  have hMn : (M.subgroupOf N).Normal :=
    ⟨fun m hm n => by
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hMnorm (n : G) n.2 (m : G) hm⟩
  have hP2 : IsPGroup 2 ↥P :=
    (hM2.of_equiv (Subgroup.subgroupOfEquivOfLe hMN).symm).map π
  have hPn : P.Normal := hMn.map π (QuotientGroup.mk'_surjective (A.subgroupOf N))
  have hPbot : P = ⊥ := y6_frob18_no_normal_two hfr P hPn hP2
  intro m hm
  have hmN : m ∈ N := hMN hm
  have hmem : π ⟨m, hmN⟩ ∈ P :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hm)
  rw [hPbot, Subgroup.mem_bot] at hmem
  have hmem' : ((⟨m, hmN⟩ : ↥N) : ↥N ⧸ A.subgroupOf N) = 1 := hmem
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff ⟨m, hmN⟩).mp hmem')

end CFSG.OddStandard.HigherRank.YamadaG23
