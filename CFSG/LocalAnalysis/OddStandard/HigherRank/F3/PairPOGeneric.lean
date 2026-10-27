module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPODefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Raw

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

theorem hasPOmegaMember_of_cover_block {H Q : Type} [Group H] [Group Q] [Finite Q]
    [IsSimpleGroup Q] (α : H →* Q) (hα : Function.Surjective α) (hαk : α.ker ≤ center H)
    (Jh : Subgroup H) (c : H) (hcJ : c ∈ Jh) (hc2 : c * c = 1) (hc1 : α c ≠ 1)
    (hle : Jh ≤ centralizer ({c} : Set H))
    (hnorm : (Jh.subgroupOf (centralizer ({c} : Set H))).Normal) (hX : POmegaBlock ↥Jh) :
    HasPOmegaMember Q := by
  have hρs : Function.Surjective (α.subgroupMap Jh) := α.subgroupMap_surjective Jh
  have hne : ∃ x : ↥Jh, α.subgroupMap Jh x ≠ 1 :=
    ⟨⟨c, hcJ⟩, fun h => hc1 (congrArg Subtype.val h)⟩
  have hker := LieType.CurtisTits.ker_le_center_of_isQuasisimple hX.quasisimple hne
  have hqs : IsQuasisimple ↥(Jh.map α) :=
    LieType.CurtisTits.isQuasisimple_of_surjective hX.quasisimple hρs hne
  have hZp : IsPGroup 2 ↥(center ↥(Jh.map α)) := by
    rw [LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hX.quasisimple hρs hker]
    exact hX.isPGroup_center.map _
  obtain ⟨n, hn, hm⟩ := hX.shape
  have hshape : CFSG.Blueprint.LieModel (↥(Jh.map α) ⧸ center ↥(Jh.map α)) .POmegaPlus n 3 1 :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hX.quasisimple hρs hker) hm
  have hu2 : orderOf (α c) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two, ← map_mul, hc2, map_one]) hc1
  obtain ⟨hmap_le, hsn⟩ :=
    ComponentClassification.HarrisLit.T1.P54.F3.map_isSubnormal_of_central hα hαk hle
      hnorm.isSubnormal
  have hsub : IsSubnormal (Jh.map α) (centralizer ({α c} : Set Q)) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hmap_le).mpr hsn
  have hnc : α c ∉ center Q := by
    intro hcz
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with hbot | htop
    · rw [hbot, Subgroup.mem_bot] at hcz
      exact hc1 hcz
    · have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
        Subgroup.mem_center_iff.mp (by rw [htop]; exact Subgroup.mem_top b) a
      obtain ⟨a, b, hab⟩ := hqs.2.2
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subtype.ext (hcomm x y))
  exact ⟨Jh.map α, α c, hu2, Subgroup.mem_map_of_mem α hcJ, hnc, hsub, hqs, hZp, n, hn, hshape⟩

end CFSG.OddStandard.HigherRank.F3
