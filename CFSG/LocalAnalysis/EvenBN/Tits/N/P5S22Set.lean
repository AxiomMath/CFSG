module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S20Set
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S22Abs

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem star_x5_mem_Ks (h49 : d.Thm49Statement) (hd : d.Hyp) : star d d.x₅ ∈ Ks d := by
  have hxHs : star d d.x₅ ∈ Hs d := actFun_mem_imgIn (x5_mem_Hg h49 hd) (x5_mem_Hg h49 hd)
  refine ⟨?_, hxHs⟩
  have hxUs : star d d.x₅ ∈ normalizer ((Us d : Subgroup (MulAut ↥d.s56V)) : Set _) := by
    rw [Us_eq h49 hd]
    exact CFSG.LocalAnalysis.EvenBN.Tits.S56.commutator_normalized _ _
      (mem_sup_right (mem_zpowers _))
  have hxt : star d d.x₅ ∈ normalizer ((zpowers (star d d.t) : Subgroup (MulAut ↥d.s56V)) :
      Set _) :=
    normalizer_zpowers_of_commute (actFun_comm_of_comm d.s56V hd.s56_x5_comm_t)
  exact normalizer_sup_of_mem hxUs hxt

theorem star_t_mem_Ks (h49 : d.Thm49Statement) (hd : d.Hyp) : star d d.t ∈ Ks d := by
  refine ⟨?_, actFun_mem_imgIn (t_mem_Hg h49 hd) (t_mem_Hg h49 hd)⟩
  exact Subgroup.le_normalizer (mem_sup_right (mem_zpowers _) : star d d.t ∈ U0s d)

theorem card_centralizer_star_t_dvd (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hC : img d (CMt d) = centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d) :
    Nat.card ↥(centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d) ∣ 2 ^ 18 * 5 := by
  rw [← hC]
  have h1 : Nat.card ↥(img d (CMt d)) ∣ Nat.card ↥(CMt d ⊓ normalizer (d.s56V : Set G)) :=
    card_imgIn_dvd d.s56V (CMt d)
  have h2 : Nat.card ↥(CMt d ⊓ normalizer (d.s56V : Set G)) ∣ Nat.card ↥d.M :=
    Subgroup.card_dvd_of_le (inf_le_left.trans CMt_le_M)
  have h3 : Nat.card ↥d.M ∣ 2 ^ 18 * 5 := by
    rcases hd.card_M_N_values h49 with ⟨-, hM, -⟩ | ⟨-, hM, -⟩
    · rw [hM]; exact ⟨2 ^ 18 * 5 / (2 ^ 17 * 5), by norm_num⟩
    · rw [hM]
  exact h1.trans (h2.trans h3)

theorem isSolvable_centralizer_star_t (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hC : img d (CMt d) = centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d) :
    Group.IsSolvable ↥(centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) ⊓ Hs d) :=
  isSolvable_of_card_dvd_two_pow_mul_five (a := 18) (card_centralizer_star_t_dvd h49 hd hC)

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
