module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Solv
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31NonSolv

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_exists_invol_inter (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) {y : G}
    (ht : ActsAs L (y * s.t * y⁻¹) s.fr'.σ) :
    ∃ u : G, u ∈ L ∧ y⁻¹ * u * y ∈ L ∧ orderOf u = 2 ∧
      u * (y * s.t * y⁻¹) = (y * s.t * y⁻¹) * u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : (y * s.t * y⁻¹) ^ 2 = 1 := by
    rw [conj_pow, ← s.t_order, pow_orderOf_eq_one]
    simp
  have hnotsolv : ¬ Group.IsSolvable ↥(centEl L (y * s.t * y⁻¹)) :=
    s3_centEl_not_solvable s hS hZ ht ht2
  have hnotodd : ¬ Odd (Nat.card ↥(centEl L (y * s.t * y⁻¹) ⊓ conjSub y L)) := by
    intro hodd
    exact hnotsolv (s3_centEl_solvable_of_odd s hS hOut y hodd)
  have hdvd : 2 ∣ Nat.card ↥(centEl L (y * s.t * y⁻¹) ⊓ conjSub y L) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnotodd)
  obtain ⟨u₀, hu₀⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(centEl L (y * s.t * y⁻¹) ⊓ conjSub y L)) 2 hdvd
  have huX : (u₀ : G) ∈ centEl L (y * s.t * y⁻¹) := (Subgroup.mem_inf.mp u₀.2).1
  have huY : (u₀ : G) ∈ conjSub y L := (Subgroup.mem_inf.mp u₀.2).2
  have huL : (u₀ : G) ∈ L := (Subgroup.mem_inf.mp huX).1
  have hcomm : (u₀ : G) * (y * s.t * y⁻¹) = (y * s.t * y⁻¹) * (u₀ : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp huX).2
  simp only [conjSub, Subgroup.mem_map] at huY
  obtain ⟨l, hl, hfl⟩ := huY
  have hfl' : y * l * y⁻¹ = (u₀ : G) := by
    simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hfl
  have hyl : y⁻¹ * (u₀ : G) * y = l := by
    rw [← hfl']
    group
  exact ⟨(u₀ : G), huL, by rw [hyl]; exact hl, (Subgroup.orderOf_coe u₀).trans hu₀, hcomm⟩

end CFSG.OddStandard.HigherRank.YamadaG23
