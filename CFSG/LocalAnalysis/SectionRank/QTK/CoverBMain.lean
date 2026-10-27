module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBAlt
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBEven
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBExc
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBSpor
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBTable
public import CFSG.LocalAnalysis.SectionRank.QTK.Assembly

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem lieModel_of_statedClassicalModel {S : Type} [Group S] {t : StatedLieTag} {n p f : ℕ}
    (hm : StatedClassicalModel S t n p f) : LieModel S t n p f := by
  refine Or.inl ⟨?_, hm⟩
  cases t <;> first | exact hm.2.elim | simp [classicalTags]

theorem tablePrime_of_dvd
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {t : StatedLieTag}
    {n ℓ f : ℕ} (hm : LieModel (K ⧸ center K) t n ℓ f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrZ : r ∣ Nat.card (center K)) : TablePrime t n ℓ f r :=
  odd_prime_dvd_table hr hr2 (hrZ.trans (card_center_dvd_table hK hm))

variable {G : Type} [Group G] [Finite G]

theorem qtkSimpleList_of_cover
    (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G} (hq : CFSG.IsQuasisimple ↥Y)
    (hK : CFSG.SectionRank.IsKGroupCat ↥Y) : QTKSimpleList (↥Y ⧸ center ↥Y) := by
  have : IsSimpleGroup (↥Y ⧸ center ↥Y) := hq.2.1
  have hcat : Catalog (↥Y ⧸ center ↥Y) := by
    refine CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK ⊤
      ((QuotientGroup.mk' (center ↥Y)).comp (⊤ : Subgroup ↥Y).subtype) fun s => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨⟨y, mem_top y⟩, rfl⟩
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hex | ⟨s, ⟨e⟩⟩
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact Or.inl ⟨n, hn, le_nine_of_alt he e, ⟨e⟩⟩
  · have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥Y) → TablePrime t n p f r :=
      fun r hr hr2 hrZ =>
        tablePrime_of_dvd hq (lieModel_of_statedClassicalModel hm) hr hr2 hrZ
    by_cases hp2 : p = 2
    · subst hp2
      exact qtkSimpleList_of_cover_even_classical he hm hZ
    · exact qtkSimpleList_of_cover_odd_classical he hp2 hm hZ
  · exact qtkSimpleList_of_exceptionalList (qtExceptionalList_of_cover he hex
      fun t n ℓ f hm r hr hr2 hrZ => tablePrime_of_dvd hq hm hr hr2 hrZ)
  · exact qtkSimpleList_of_mem_qtkSporadicNames (mem_qtkSporadicNames_of_cover he hq e) e

end CFSG.SectionRank.QTK.CoverB
