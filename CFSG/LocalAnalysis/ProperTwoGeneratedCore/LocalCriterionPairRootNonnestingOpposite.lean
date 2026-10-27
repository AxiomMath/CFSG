module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankMaximalKernel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairRootNonnesting

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.TwoRankLowerBound.Helpers

universe u

variable {G : Type u} [Group G]

theorem square_one_normalizes_opposite_join (U : Subgroup G) (t : G)
    (htt : t * t = 1) :
    t ∈ Subgroup.normalizer
      ((U ⊔ U.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  let Ut := U.map (MulAut.conj t).toMonoidHom
  have htUt : Ut.map (MulAut.conj t).toMonoidHom = U := by
    rw [Subgroup.map_map]
    have htwice : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        MonoidHom.id G := by
      ext x
      change t * (t * x * t⁻¹) * t⁻¹ = x
      calc
        _ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [htt, inv_one, one_mul, mul_one]
    rw [htwice, Subgroup.map_id]
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (U ⊔ Ut).map (MulAut.conj t).toMonoidHom = U ⊔ Ut
  rw [Subgroup.map_sup, htUt]
  exact sup_comm Ut U

theorem opposite_join_normal_of_generation (I U : Subgroup G) (z t : G)
    (hzU : z ∈ U) (htt : t * t = 1)
    (hIU : I ≤ Subgroup.normalizer (U : Set G))
    (htI : t ∈ Subgroup.normalizer (I : Set G))
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ I = ⊤) :
    (U ⊔ U.map (MulAut.conj t).toMonoidHom).Normal := by
  let Ut := U.map (MulAut.conj t).toMonoidHom
  let P := U ⊔ Ut
  have hIUt : I ≤ Subgroup.normalizer (Ut : Set G) :=
    numeratorPairRank_opposite_normalized I U t hIU htI
  have hIP : I ≤ Subgroup.normalizer (P : Set G) :=
    (le_inf hIU hIUt).trans (Subgroup.inf_normalizer_le_normalizer_sup U Ut)
  have hzP : z ∈ P := (show U ≤ P from le_sup_left) hzU
  have htP : t ∈ Subgroup.normalizer (P : Set G) :=
    square_one_normalizes_opposite_join U t htt
  have hGnormal : (⊤ : Subgroup G) ≤ Subgroup.normalizer (P : Set G) := by
    rw [← hgen]
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr (P.le_normalizer hzP))
      (Subgroup.zpowers_le.mpr htP)) hIP
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hGnormal)

theorem opposite_join_le_centralizer (U : Subgroup G) (t u : G)
    (hU : U ≤ Subgroup.centralizer ({u} : Set G)) (htu : Commute t u) :
    U ⊔ U.map (MulAut.conj t).toMonoidHom ≤ Subgroup.centralizer ({u} : Set G) := by
  apply sup_le hU
  rintro x ⟨a, ha, rfl⟩
  have hau : Commute a u := Subgroup.mem_centralizer_singleton_iff.mp (hU ha)
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  change t * a * t⁻¹ * u = u * (t * a * t⁻¹)
  exact ((htu.mul_left hau).mul_left htu.inv_left).eq

theorem simple_opposite_join_contradiction [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (I U : Subgroup G) (z t u : G) (hzU : z ∈ U) (hz : z ≠ 1) (hu : u ≠ 1)
    (htt : t * t = 1) (hIU : I ≤ Subgroup.normalizer (U : Set G))
    (htI : t ∈ Subgroup.normalizer (I : Set G))
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ I = ⊤)
    (hU : U ≤ Subgroup.centralizer ({u} : Set G)) (htu : Commute t u) : False := by
  let P := U ⊔ U.map (MulAut.conj t).toMonoidHom
  let : P.Normal := opposite_join_normal_of_generation I U z t hzU htt hIU htI hgen
  have hzP : z ∈ P := (show U ≤ P from le_sup_left) hzU
  have hPC : P ≤ Subgroup.centralizer ({u} : Set G) :=
    opposite_join_le_centralizer U t u hU htu
  have hCproper : Subgroup.centralizer ({u} : Set G) ≠ ⊤ := by
    intro htop
    have hucenter : u ∈ Subgroup.center G :=
      Subgroup.centralizer_eq_top_iff_subset.mp htop (Set.mem_singleton u)
    rw [center_eq_bot_of_nonabelian_simple G hnonab] at hucenter
    exact hu (Subgroup.mem_bot.mp hucenter)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hPbot | hPtop
  · rw [hPbot] at hzP
    exact hz (Subgroup.mem_bot.mp hzP)
  · exact hCproper (top_le_iff.mp (hPtop ▸ hPC))

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairRootNonnesting
