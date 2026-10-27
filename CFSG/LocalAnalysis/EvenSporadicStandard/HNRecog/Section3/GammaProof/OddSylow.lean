module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.OddTools
public import CFSG.GroupTheory.SmallOrderNotSimple

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {K : Type} [Group K] [Finite K]

theorem gamma_card_dvd_seven_of_le_centralizer
    (h7 : ∀ g : K, orderOf g = 7 → Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 7)
    {H R : Subgroup K} (hHR : H ≤ Subgroup.centralizer (R : Set K))
    {g : K} (hgR : g ∈ R) (hg : orderOf g = 7) : Nat.card H ∣ 7 := by
  have hsub : ({g} : Set K) ⊆ (R : Set K) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact hgR
  exact (Subgroup.card_dvd_of_le (hHR.trans (Subgroup.centralizer_le hsub))).trans (h7 g hg)

private lemma gamma_centralizer_sylow_eq_top_105
    {p : ℕ} [Fact p.Prime] (hK : Nat.card K = 105) (hp : p = 3 ∨ p = 5)
    {P : Sylow p K} (hPnormal : P.Normal) (hPcard : Nat.card (P : Subgroup K) = p) :
    Subgroup.centralizer (P : Set K) = ⊤ := by
  haveI : P.Normal := hPnormal
  let C : Subgroup K := Subgroup.centralizer (P : Set K)
  have hC105 : Nat.card C ∣ 105 := by
    have := Subgroup.card_dvd_of_le (le_top : C ≤ ⊤)
    simpa [C, hK] using this
  have htop : Subgroup.normalizer ((P : Subgroup K) : Set K) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hPnormal
  have hL : (⊤ : Subgroup K) ≤ Subgroup.normalizer ((P : Subgroup K) : Set K) := by
    simpa [htop]
  have hdvd := gamma_card_dvd_of_le_normalizer (P := (P : Subgroup K)) (L := ⊤)
    (by rw [hPcard]; exact Fact.out) hL
  have h105C : 105 ∣ Nat.card C := by
    have hdvd' : 105 ∣ Nat.card C * (p - 1) := by
      simpa [C, hK, hPcard] using hdvd
    have hcop : Nat.Coprime 105 (p - 1) := by
      have hodd : Odd 105 := by decide
      rcases hp with rfl | rfl
      · simpa using hodd.coprime_two_right
      · simpa using hodd.coprime_two_right.pow_right 2
    exact hcop.dvd_mul_right.mp hdvd'
  have hCcard : Nat.card C = 105 := Nat.dvd_antisymm hC105 h105C
  exact (Subgroup.card_eq_iff_eq_top C).mp (by rw [hCcard, hK])

private lemma gamma_false_of_sylow_prime_105 (hK : Nat.card K = 105)
    (h7 : ∀ g : K, orderOf g = 7 → Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 7)
    {p : ℕ} [Fact p.Prime] {P : Sylow p K} (hp : p = 3 ∨ p = 5)
    (hPnormal : P.Normal) (hPcard : Nat.card (P : Subgroup K) = p) : False := by
  have hCtop := gamma_centralizer_sylow_eq_top_105 hK hp hPnormal hPcard
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := K) 7 (by rw [hK]; norm_num)
  have hgC : g ∈ Subgroup.centralizer (P : Set K) := by rw [hCtop]; trivial
  have hPleCg : (P : Subgroup K) ≤ Subgroup.centralizer ({g} : Set K) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hgC y hy
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup K)) p
    (by rw [hPcard])
  have hxKord : orderOf (x : K) = p := (Subgroup.orderOf_coe x).trans hxord
  have hpdvd : p ∣ Nat.card ↥(Subgroup.centralizer ({g} : Set K)) := by
    rw [← hxKord]
    exact Subgroup.orderOf_dvd_natCard _ (hPleCg x.2)
  have hpdvd7 : p ∣ 7 := hpdvd.trans (h7 g hgord)
  rcases hp with rfl | rfl
  · exact absurd hpdvd7 (by norm_num)
  · exact absurd hpdvd7 (by norm_num)

theorem gamma_odd_false_63 (hK : Nat.card K = 63)
    (h7 : ∀ g : K, orderOf g = 7 → Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 7) :
    False := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hf7 : (Nat.card K).factorization 7 = 1 := by
    rw [hK]
    exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hn7 : Nat.card (Sylow 7 K) = 1 := by
    obtain ⟨hdvd, hmod⟩ := CFSG.GroupTheory.card_sylow_dvd_and_modEq (p := 7) (G := K)
      (CFSG.GroupTheory.index_sylow_eq (m := 9) hf7 (by rw [hK]; norm_num))
    have hpos : 0 < Nat.card (Sylow 7 K) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 7 K) = n at hdvd hmod hpos hle ⊢
    interval_cases n <;> first | rfl | (exfalso; revert hdvd hmod; decide)
  haveI : Subsingleton (Sylow 7 K) := (Nat.card_eq_one_iff_unique.1 hn7).1
  obtain ⟨P⟩ : Nonempty (Sylow 7 K) := inferInstance
  haveI : P.Normal := P.normal_of_subsingleton
  have hPcard : Nat.card (P : Subgroup K) = 7 := by
    rw [P.card_eq_multiplicity, hf7, pow_one]
  have htop : Subgroup.normalizer ((P : Subgroup K) : Set K) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr P.normal_of_subsingleton
  have hL : (⊤ : Subgroup K) ≤ Subgroup.normalizer ((P : Subgroup K) : Set K) := by
    simpa [htop]
  have hdvd := gamma_card_dvd_of_le_normalizer (P := (P : Subgroup K)) (L := ⊤)
    (by rw [hPcard]; norm_num) hL
  let T : Subgroup K := ⊤ ⊓ Subgroup.centralizer (P : Set K)
  have hdvd' : 63 ∣ Nat.card T * 6 := by
    simpa [T, hK, hPcard] using hdvd
  obtain ⟨gP, hgPord⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup K)) 7
    (by rw [hPcard])
  let g : K := gP
  have hgP : g ∈ (P : Subgroup K) := gP.2
  have hgord : orderOf g = 7 := (Subgroup.orderOf_coe gP).trans hgPord
  have hT7 : Nat.card T ∣ 7 :=
    gamma_card_dvd_seven_of_le_centralizer h7 inf_le_right hgP hgord
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hT7 with hT1 | hT7'
  · rw [hT1] at hdvd'
    norm_num at hdvd'
  · rw [hT7'] at hdvd'
    norm_num at hdvd'

theorem gamma_odd_false_105 (hK : Nat.card K = 105)
    (h7 : ∀ g : K, orderOf g = 7 → Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 7) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hf3 : (Nat.card K).factorization 3 = 1 := by
    rw [hK]
    exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hf5 : (Nat.card K).factorization 5 = 1 := by
    rw [hK]
    exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h3cases : Nat.card (Sylow 3 K) = 1 ∨ Nat.card (Sylow 3 K) = 7 := by
    obtain ⟨hdvd, hmod⟩ := CFSG.GroupTheory.card_sylow_dvd_and_modEq (p := 3) (G := K)
      (CFSG.GroupTheory.index_sylow_eq (m := 35) hf3 (by rw [hK]; norm_num))
    have hpos : 0 < Nat.card (Sylow 3 K) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 3 K) = n at hdvd hmod hpos hle ⊢
    interval_cases n <;> first | (left; rfl) | (right; rfl) |
      (exfalso; revert hdvd hmod; decide)
  have h5cases : Nat.card (Sylow 5 K) = 1 ∨ Nat.card (Sylow 5 K) = 21 := by
    obtain ⟨hdvd, hmod⟩ := CFSG.GroupTheory.card_sylow_dvd_and_modEq (p := 5) (G := K)
      (CFSG.GroupTheory.index_sylow_eq (m := 21) hf5 (by rw [hK]; norm_num))
    have hpos : 0 < Nat.card (Sylow 5 K) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 5 K) = n at hdvd hmod hpos hle ⊢
    interval_cases n <;> first | (left; rfl) | (right; rfl) |
      (exfalso; revert hdvd hmod; decide)
  obtain ⟨P3⟩ : Nonempty (Sylow 3 K) := inferInstance
  obtain ⟨P5⟩ : Nonempty (Sylow 5 K) := inferInstance
  have hP3card : Nat.card (P3 : Subgroup K) = 3 := by
    rw [P3.card_eq_multiplicity, hf3, pow_one]
  have hP5card : Nat.card (P5 : Subgroup K) = 5 := by
    rw [P5.card_eq_multiplicity, hf5, pow_one]
  rcases h5cases with h5n | h5n
  · haveI : Subsingleton (Sylow 5 K) := (Nat.card_eq_one_iff_unique.1 h5n).1
    exact gamma_false_of_sylow_prime_105 hK h7 (Or.inr rfl) P5.normal_of_subsingleton hP5card
  · rcases h3cases with h3n | h3n
    · haveI : Subsingleton (Sylow 3 K) := (Nat.card_eq_one_iff_unique.1 h3n).1
      exact gamma_false_of_sylow_prime_105 hK h7 (Or.inl rfl) P3.normal_of_subsingleton
        hP3card
    ·
      let N : Subgroup K := Subgroup.normalizer (P3 : Set K)
      have hidx : N.index = 7 := by
        have h := P3.card_eq_index_normalizer
        rw [h3n] at h
        simpa [N] using h.symm
      have hNcard : Nat.card N = 15 := by
        have := Subgroup.card_mul_index (H := N)
        rw [hidx, hK] at this
        omega
      have hdvd := gamma_card_dvd_of_le_normalizer (P := (P3 : Subgroup K)) (L := N)
        (by rw [hP3card]; norm_num) le_rfl
      let D : Subgroup K := N ⊓ Subgroup.centralizer (P3 : Set K)
      have hdvd' : 15 ∣ Nat.card D * 2 := by
        simpa [D, hNcard, hP3card] using hdvd
      have hD15 : Nat.card D ∣ 15 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : D ≤ N)
        simpa [D, hNcard] using this
      obtain ⟨k, hk⟩ := hD15
      have hk2 : k ∣ 2 := by
        have hD2 : Nat.card D * k ∣ Nat.card D * 2 := by
          rwa [hk] at hdvd'
        exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hD2
      have hDcard : Nat.card D = 15 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with hk1 | hk2'
        · rw [hk1] at hk
          simpa using hk.symm
        · rw [hk2'] at hk
          omega
      have hDN : D = N :=
        Subgroup.eq_of_le_of_card_ge (inf_le_left : D ≤ N)
          (by rw [hDcard, hNcard])
      have hNleC : N ≤ Subgroup.centralizer (P3 : Set K) := by
        have hDC : D ≤ Subgroup.centralizer (P3 : Set K) := inf_le_right
        rwa [hDN] at hDC
      obtain ⟨hN, hhNord⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
        (by rw [hNcard]; norm_num)
      let h : K := hN
      have hhN : h ∈ N := hN.2
      have hhord : orderOf h = 5 := (Subgroup.orderOf_coe hN).trans hhNord
      let R : Subgroup K := Subgroup.zpowers h
      have hRcard : Nat.card R = 5 := by
        dsimp only [R]
        rw [Nat.card_zpowers, hhord]
      have hRleC : R ≤ Subgroup.centralizer (P3 : Set K) :=
        Subgroup.zpowers_le.mpr (hNleC hhN)
      have hP3leCR : (P3 : Subgroup K) ≤ Subgroup.centralizer (R : Set K) :=
        Subgroup.le_centralizer_iff.mpr hRleC
      have hP3leNR : (P3 : Subgroup K) ≤ Subgroup.normalizer (R : Set K) :=
        hP3leCR.trans (Subgroup.centralizer_le_normalizer (R : Set K))
      have h3dvdNR : 3 ∣ Nat.card ↥(Subgroup.normalizer (R : Set K)) := by
        rw [← hP3card]
        exact Subgroup.card_dvd_of_le hP3leNR
      let Q : Sylow 5 K := Sylow.ofCard R (by rw [hRcard, hf5, pow_one])
      have hQidx : (Subgroup.normalizer (R : Set K)).index = 21 := by
        have hQ := Q.card_eq_index_normalizer
        change Nat.card (Sylow 5 K) =
          (Subgroup.normalizer (((Q : Sylow 5 K) : Subgroup K) : Set K)).index at hQ
        rw [Sylow.coe_ofCard] at hQ
        rw [h5n] at hQ
        exact hQ.symm
      have hNRcard : Nat.card ↥(Subgroup.normalizer (R : Set K)) = 5 := by
        have := Subgroup.card_mul_index (H := Subgroup.normalizer (R : Set K))
        rw [hQidx, hK] at this
        omega
      rw [hNRcard] at h3dvdNR
      norm_num at h3dvdNR

end CFSG.EvenSporadicStandard.HNRecog.Section3
