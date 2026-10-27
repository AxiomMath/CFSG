module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.RankThree.PartOne.S9.Sylow.GlobalLemmas

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def threeStarImgMulEquiv (M Q : Subgroup G) (hQM : Q ≤ M)
    (hQD : Q ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M = ⊥) :
    ↥Q ≃* ↥(threeStarImg M Q) := by
  let π : ↥M →* threeStar M := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)
  let f : ↥Q →* threeStar M := π.comp (Subgroup.inclusion hQM)
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' : π (Subgroup.inclusion hQM a) = π (Subgroup.inclusion hQM b) := hab
    have hker : (Subgroup.inclusion hQM a)⁻¹ * (Subgroup.inclusion hQM b) ∈
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)).ker := by
      rw [MonoidHom.mem_ker]
      show π (Subgroup.inclusion hQM a)⁻¹ * π (Subgroup.inclusion hQM b) = 1
      exact (congrArg (fun x : threeStar M => x⁻¹ * π (Subgroup.inclusion hQM b))
        hab').trans (inv_mul_cancel _)
    rw [QuotientGroup.ker_mk'] at hker
    have hD : (a : G)⁻¹ * (b : G) ∈ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
      rw [CFSG.inSubgroup]
      exact Subgroup.mem_map.mpr ⟨(Subgroup.inclusion hQM a)⁻¹ * Subgroup.inclusion hQM b,
        hker, by simp⟩
    have hQ : (a : G)⁻¹ * (b : G) ∈ Q := Q.mul_mem (Q.inv_mem a.2) b.2
    have hone : (a : G)⁻¹ * (b : G) = 1 := by
      have := Subgroup.mem_inf.mpr ⟨hQ, hD⟩
      rw [hQD, Subgroup.mem_bot] at this
      exact this
    apply Subtype.ext
    calc (a : G) = (a : G) * 1 := by rw [mul_one]
      _ = (a : G) * ((a : G)⁻¹ * (b : G)) := by rw [hone]
      _ = (b : G) := mul_inv_cancel_left (a : G) (b : G)
  have hrange : f.range = threeStarImg M Q := by
    rw [threeStarImg, MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr q.2
    · intro hx
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

theorem inf_inSubgroup_pPrimeCore_eq_bot {M Y : Subgroup G} (hY : IsPGroup 3 Y) :
    Y ⊓ CFSG.inSubgroup (CFSG.pPrimeCore 3) M = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd ?_ hY
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (CFSG.RankThree.PartOne.Sec9B.coprime_card_inSubgroup_pPrimeCore (r := 3) M)

theorem card_threeStarImg_of_isPGroup {M Y : Subgroup G} (hY : IsPGroup 3 Y) (hYM : Y ≤ M) :
    Nat.card ↥(threeStarImg M Y) = Nat.card ↥Y :=
  (Nat.card_congr
    (threeStarImgMulEquiv M Y hYM (inf_inSubgroup_pPrimeCore_eq_bot hY)).toEquiv).symm

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
