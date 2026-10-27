module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

theorem mem_normalizer_of_even_inf {Q : Subgroup G} (htight : TightlyEmbedded Q) {x : G}
    (heven : Even (Nat.card (Q ⊓ rightConjugate Q x : Subgroup G))) :
    x ∈ normalizer (Q : Set G) := by
  by_contra hx
  exact Nat.not_even_iff_odd.mpr (htight.2 x hx) heven

theorem mem_normalizer_of_le_rightConjugate [Finite G] {Q Y : Subgroup G}
    (htight : TightlyEmbedded Q) (hYQ : Y ≤ Q) (hY : Even (Nat.card Y)) {x : G}
    (hYx : Y ≤ rightConjugate Q x) : x ∈ normalizer (Q : Set G) := by
  refine mem_normalizer_of_even_inf htight ?_
  obtain ⟨k, hk⟩ := even_iff_two_dvd.mp hY
  exact even_iff_two_dvd.mpr ((dvd_mul_right 2 k).trans
    (hk ▸ Subgroup.card_dvd_of_le (le_inf hYQ hYx)))

theorem normalizer_le_of_even [Finite G] {Q Y : Subgroup G} (htight : TightlyEmbedded Q)
    (hYQ : Y ≤ Q) (hY : Even (Nat.card Y)) :
    normalizer (Y : Set G) ≤ normalizer (Q : Set G) :=
  StandardSubgroupAPI.normalizer_le_normalizer_of_le_of_even htight hYQ hY

theorem centralizer_le_normalizer_zpowers (t : G) :
    centralizer ({t} : Set G) ≤ normalizer (zpowers t : Set G) := by
  intro x hx
  have htx : Commute t x := (mem_centralizer_singleton_iff.mp hx).symm
  have hc : ∀ k : ℤ, x * t ^ k * x⁻¹ = t ^ k := fun k => by
    rw [(htx.zpow_left k).symm.eq, mul_inv_cancel_right]
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [hc k]
    exact zpow_mem (mem_zpowers t) k
  · intro hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
    have hy' : y = t ^ k := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x⁻¹ * (x * t ^ k * x⁻¹) * x := by rw [← hk, hc k]
        _ = t ^ k := by group
    rw [hy']
    exact zpow_mem (mem_zpowers t) k

theorem centralizer_le_of_involution [Finite G] {Q : Subgroup G} (htight : TightlyEmbedded Q)
    {t : G} (htQ : t ∈ Q) (ht : orderOf t = 2) :
    centralizer ({t} : Set G) ≤ normalizer (Q : Set G) :=
  StandardSubgroupAPI.centralizer_le_normalizer_of_mem_of_orderOf_eq_two htight htQ ht

theorem le_normalizer_of_fourGroup [Finite G] {Q E Y : Subgroup G} (htight : TightlyEmbedded Q)
    (hEQ : E ≤ Q) (hE : ∀ e ∈ E, e ^ 2 = 1) (hE4 : Nat.card E = 4) (hY : Odd (Nat.card Y))
    (hEY : E ≤ normalizer (Y : Set G)) : Y ≤ normalizer (Q : Set G) := by
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two E Y (fun e => Subtype.ext (hE e e.2)) (by rw [hE4]; norm_num)
    (fun h => Nat.not_even_iff_odd.mpr hY (even_iff_two_dvd.mpr h)) hEY
  rw [hgen]
  refine iSup_le fun e => iSup_le fun he => inf_le_right.trans ?_
  have he1 : (e : G) ≠ 1 := fun h => he (Subtype.ext h)
  exact centralizer_le_of_involution htight (hEQ e.2)
    (orderOf_eq_prime (hE e e.2) he1)

end CFSG.ComponentClassification.Asc75T4
