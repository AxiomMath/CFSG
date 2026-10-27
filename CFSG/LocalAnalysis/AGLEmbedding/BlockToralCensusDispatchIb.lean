module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

theorem cycPerfect_of_ib {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    {J : Subgroup Y} (h : IbPerfectSections p J) : CycPerfect p J := by
  intro V hVJ hV Q hQV hQ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card V := Subgroup.card_dvd_of_le hQV
  have hk1 : k ≤ 1 := by
    by_contra hk1
    exact h V hVJ hV ((pow_dvd_pow p (by omega : 2 ≤ k)).trans (hk ▸ hdvd))
  interval_cases k
  · rw [pow_zero] at hk
    have := Subgroup.card_eq_one.mp hk
    subst this
    exact isCyclic_of_subsingleton
  · rw [pow_one] at hk
    exact isCyclic_of_prime_card hk

namespace ToralCensus

theorem not_isCyclic_of_elemAbelian_pow {Y : Type*} [Group Y] {p k : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) {E : Subgroup Y} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k) :
    ¬ IsCyclic E := by
  intro hc
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero k hp.ne_zero)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hE.2 g g.2)
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rw [hg, hcard] at hdvd
  have := Nat.le_of_dvd hp.pos hdvd
  have h2 : p < p ^ k :=
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

end ToralCensus

@[expose] def KFactBlockToralIbOdd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    Odd (Nat.card (Subgroup.center ↥L)) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → IbPerfectSections p J →
    ∀ x ∈ L, x ^ p = 1 → x ∉ Subgroup.centralizer (L : Set Y) →
    (∃ V : Subgroup Y, ⁅V, V⁆ = V ∧ V ≤ Subgroup.normalizer (L : Set Y) ∧
      V ≤ Subgroup.normalizer (pCoreOf 2 J : Set Y) ∧ x ∈ V) →
    (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    (∃ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3) → False

open ToralCensus in
theorem kFactBlockToralIbOdd_of (hC : KFactFixCensusPrime) (hL3 : KFactL3RankTwo) :
    KFactBlockToralIbOdd := by
  intro Y _ _ L J hL hcl hP hJL hJB hodd p hp hp5 hIb x hxL hxp hxC hV hfix hE
  obtain ⟨E, hEle, hEel, hEc⟩ := hE
  have hCP : CompParab L J := ⟨hL, hcl, hodd, hP, hJL, hJB⟩
  obtain ⟨hZ, hcase⟩ := hC Y L J hCP p hp hp5 (cycPerfect_of_ib hp hIb) x
    (Subgroup.mem_sup_left hxL) hxp hxC hV hfix
  rcases hcase with hcyc | ⟨e, -, he⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hEp : IsPGroup p E := IsPGroup.of_card (n := 3) hEc
    exact not_isCyclic_of_elemAbelian_pow hp (by norm_num) hEel hEc (hcyc E hEle hEp)
  · exact hL3 Y L hL p hp hp5 hZ ⟨e, he⟩ E (le_trans hEle inf_le_left) hEel hEc

end CFSG.AGLEmbedding
