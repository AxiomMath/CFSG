module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Steps
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630AutQ8D8Fix

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankIsQ8D8)
open AutQ8D8

theorem kFactAutQ8D8Five_holds : KFactAutQ8D8Five := by
  unfold KFactAutQ8D8Five
  intro R _ _ hR P hP
  unfold smallRankIsQ8D8 at hR
  obtain ⟨A, B, ⟨eA⟩, ⟨eB⟩, hcomm, hsup, hAB⟩ := hR
  have hR32 : Nat.card R = 32 := natCard_eq_thirtyTwo eA eB hcomm hsup hAB
  have hcen : Nat.card (Subgroup.center R) = 2 := natCard_center eA eB hcomm hsup hAB
  have hfix : ∀ q : MulAut R, ∀ z ∈ Subgroup.center R, q z = z :=
    fun q z hz => apply_eq_of_mem_center hcen q hz
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite (MulAut R) :=
    Finite.of_injective (fun g : MulAut R => (g : R → R))
      (fun g h hgh => MulEquiv.ext (fun x => congrFun hgh x))
  classical
  haveI : Fintype ↥P := Fintype.ofFinite ↥P
  haveI : ∀ g : ↥P, Fintype (MulAction.fixedBy R g) := fun g => Fintype.ofFinite _
  haveI : Fintype (Quotient (MulAction.orbitRel ↥P R)) := Fintype.ofFinite _
  have hterm : ∀ g : ↥P,
      Fintype.card (MulAction.fixedBy R g) = 2 + if g = 1 then 30 else 0 := by
    intro g
    rw [← Nat.card_eq_fintype_card]
    by_cases hg1 : g = 1
    · subst hg1
      have hset : MulAction.fixedBy R (1 : ↥P) = Set.univ := by
        ext r
        simp [MulAction.mem_fixedBy]
      rw [hset, Nat.card_univ, hR32]
      simp
    · rw [if_neg hg1, add_zero]
      have hset : MulAction.fixedBy R g = (Subgroup.center R : Set R) := by
        ext r
        rw [MulAction.mem_fixedBy, SetLike.mem_coe]
        constructor
        · intro hgr
          have hQ : IsPGroup 5 (Subgroup.zpowers (g : MulAut R)) :=
            hP.to_le (Subgroup.zpowers_le.mpr g.2)
          have hQne : ∃ q ∈ Subgroup.zpowers (g : MulAut R), q ≠ 1 :=
            ⟨(g : MulAut R), Subgroup.mem_zpowers _, fun h => hg1 (Subtype.ext h)⟩
          have hst : (g : MulAut R) ∈ MulAction.stabilizer (MulAut R) r :=
            MulAction.mem_stabilizer_iff.mpr hgr
          have hr : ∀ q ∈ Subgroup.zpowers (g : MulAut R), q r = r := by
            intro q hq
            exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr hst hq)
          exact mem_center_of_fixed hQ hQne hR32 hcen hfix hr
        · intro hr
          exact hfix (g : MulAut R) r hr
      rw [hset]
      exact hcen
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥P R
  have hsum : ∑ g : ↥P, Fintype.card (MulAction.fixedBy R g) = 2 * Fintype.card ↥P + 30 := by
    rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_add_distrib]
    simp [mul_comm]
  have hdvd : Fintype.card ↥P ∣ 30 := by
    have h1 : Fintype.card ↥P ∣ 2 * Fintype.card ↥P + 30 := by
      rw [← hsum, hburn]
      exact dvd_mul_left _ _
    exact (Nat.dvd_add_right (dvd_mul_left _ 2)).mp h1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  rw [Nat.card_eq_fintype_card] at hn
  rw [Nat.card_eq_fintype_card, hn]
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · exfalso
    have h25 : 25 ∣ Fintype.card ↥P := ⟨5 ^ n, by rw [hn]; ring⟩
    have h30 := dvd_trans h25 hdvd
    norm_num at h30

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
