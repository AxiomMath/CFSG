module

public import CFSG.Dihedral.OriginalOddCore

public noncomputable section

namespace CFSG.DihedralBlueprint

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCore_two_quotient_of_hasNormalTwoComplement (H : Subgroup G)
    (h : HasNormalTwoComplement H) : IsPGroup 2 (H ⧸ Assembly.oddCore H) := by
  obtain ⟨K, hKH, hnormal, hodd, a, hindex⟩ := h
  have hKcore := normal_odd_le_oddCoreOf K H hKH hnormal hodd
  have hle : K.subgroupOf H ≤ Assembly.oddCore H := by
    intro x hx
    have hm : (x : G) ∈ oddCoreOf H := hKcore hx
    change x ∈ ((Assembly.oddCore H).map H.subtype).comap H.subtype at hm
    simpa only [Subgroup.comap_map_eq_self_of_injective H.subtype_injective] using hm
  have hdvd : (Assembly.oddCore H).index ∣ 2 ^ a := by
    rw [← hindex]
    exact Subgroup.index_dvd_of_le hle
  exact IsPGroup.of_card_dvd_pow (by simpa only [Subgroup.index_eq_card] using hdvd)

omit [Finite G] in
theorem quotient_isPGroup_of_hasSylowTwoQuotient (H : Subgroup G)
    (h : HasSylowTwoQuotient H) : IsPGroup 2 (H ⧸ Assembly.oddCore H) := by
  obtain ⟨T, ⟨e⟩⟩ := h
  exact T.isPGroup'.of_equiv e.symm

omit [Finite G] in
theorem not_hasAlternatingQuotient_of_two_quotient (H : Subgroup G)
    (h : IsPGroup 2 (H ⧸ Assembly.oddCore H)) : ¬ HasAlternatingQuotient H := by
  rintro ⟨e⟩
  have hA : IsPGroup 2 (alternatingGroup (Fin 7)) := h.of_equiv e
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    decide
  have hdiv : 3 ∣ 2 ^ n := by rw [← hn, hcard]; decide
  have hbad : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
  norm_num at hbad

theorem not_hasSylowTwoQuotient_of_card_twentyFour (H : Subgroup G)
    (hcard : Nat.card (H ⧸ Assembly.oddCore H) = 24) : ¬ HasSylowTwoQuotient H := by
  intro h
  obtain ⟨n, hn⟩ := (quotient_isPGroup_of_hasSylowTwoQuotient H h).exists_card_eq
  have hdiv : 3 ∣ 2 ^ n := by rw [← hn, hcard]; decide
  have hbad : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
  norm_num at hbad

theorem not_hasNormalTwoComplement_of_card_twentyFour (H : Subgroup G)
    (hcard : Nat.card (H ⧸ Assembly.oddCore H) = 24) : ¬ HasNormalTwoComplement H := by
  intro h
  obtain ⟨n, hn⟩ := (oddCore_two_quotient_of_hasNormalTwoComplement H h).exists_card_eq
  have hdiv : 3 ∣ 2 ^ n := by rw [← hn, hcard]; decide
  have hbad : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
  norm_num at hbad

omit [Finite G] in
theorem not_hasAlternatingQuotient_of_card_twentyFour (H : Subgroup G)
    (hcard : Nat.card (H ⧸ Assembly.oddCore H) = 24) : ¬ HasAlternatingQuotient H := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  rw [hcard, nat_card_alternatingGroup, Nat.card_eq_fintype_card] at h
  norm_num at h

end CFSG.DihedralBlueprint
