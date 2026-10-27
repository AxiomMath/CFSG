module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdCyc

public section

namespace CFSG.GroupTheory.QuasisimpleCenterRankOne

private theorem isMulCommutative_of_cyclic_image_center {J : Type*} [Group J] (Q : Subgroup J)
    (hcyc : IsCyclic (Q.map (QuotientGroup.mk' (Subgroup.center J)))) :
    IsMulCommutative Q := by
  let π : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  let f : Q →* Q.map π := π.subgroupMap Q
  have hker : f.ker ≤ Subgroup.center Q := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxZ : (x : J) ∈ Subgroup.center J := by
      refine (QuotientGroup.eq_one_iff (x := (x : J))).mp ?_
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxZ (y : J))
  have : IsCyclic (Q.map π) := hcyc
  exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hker

theorem not_dvd_card_center_of_pRank_le_one {J : Type*} [Group J] [Finite J]
    (hJ : CFSG.IsQuasisimple J) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : CFSG.pRank p (J ⧸ Subgroup.center J) ≤ 1) : ¬ p ∣ Nat.card (Subgroup.center J) := by
  intro hdvd
  have : Group.IsPerfect J := hJ.1
  have hp : p.Prime := Fact.out
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center J) p hdvd
  have hzJ : orderOf ((z : Subgroup.center J) : J) = p := by
    rw [Subgroup.orderOf_coe]
    exact hzord
  have hZp : IsPGroup p (Subgroup.zpowers ((z : Subgroup.center J) : J)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzJ, pow_one])
  obtain ⟨Q, hzQ⟩ := hZp.exists_le_sylow
  let π : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  let S : Sylow p (J ⧸ Subgroup.center J) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) Q
  have hScoe : (S : Subgroup (J ⧸ Subgroup.center J)) = (Q : Subgroup J).map π :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) Q
  have hcyc : IsCyclic ((Q : Subgroup J).map π) :=
    hScoe ▸
      CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_sylow_of_pRank_le_one
        hp hp2 h S
  have : IsMulCommutative (Q : Subgroup J) :=
    isMulCommutative_of_cyclic_image_center (Q : Subgroup J) hcyc
  have hbot : (Q : Subgroup J) ⊓ Subgroup.center J = ⊥ :=
    CFSG.Quasithin.SBd19F.sylow_inf_center_eq_bot Q
  have hmem : ((z : Subgroup.center J) : J) ∈ (Q : Subgroup J) ⊓ Subgroup.center J :=
    ⟨hzQ (Subgroup.mem_zpowers _), z.2⟩
  rw [hbot] at hmem
  have hz1 : ((z : Subgroup.center J) : J) = 1 := by simpa using hmem
  have hp1 : p = 1 := by rw [← hzJ, orderOf_eq_one_iff.mpr hz1]
  exact hp.ne_one hp1

end CFSG.GroupTheory.QuasisimpleCenterRankOne
