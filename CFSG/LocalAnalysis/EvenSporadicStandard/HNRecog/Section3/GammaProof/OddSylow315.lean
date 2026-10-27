module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.OddSylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {K : Type} [Group K] [Finite K]

private lemma gamma_false_315_normal_three (hK : Nat.card K = 315)
    (h7 : ∀ g : K, orderOf g = 7 → Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 7)
    (P : Sylow 3 K) (hPnormal : P.Normal) (hPcard : Nat.card (P : Subgroup K) = 9) :
    False := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : P.Normal := hPnormal
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := K) 7 (by rw [hK]; norm_num)
  let R : Subgroup K := Subgroup.zpowers g
  have hRcard : Nat.card R = 7 := by
    dsimp only [R]
    rw [Nat.card_zpowers, hgord]
  have hRp : IsPGroup 7 R := IsPGroup.of_card (n := 1) (by simpa using hRcard)
  have htop : Subgroup.normalizer ((P : Subgroup K) : Set K) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hPnormal
  have hRleN : R ≤ Subgroup.normalizer ((P : Subgroup K) : Set K) := by
    rw [htop]
    exact le_top
  have hmod := gamma_card_modEq_of_le_normalizer (q := 7) (P := (P : Subgroup K))
    (R := R) hRp hRleN
  let D : Subgroup K := (P : Subgroup K) ⊓ Subgroup.centralizer (R : Set K)
  have hD9 : Nat.card D ∣ 9 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : D ≤ (P : Subgroup K))
    simpa [D, hPcard] using this
  have hD7 : Nat.card D ∣ 7 :=
    gamma_card_dvd_seven_of_le_centralizer h7 inf_le_right (Subgroup.mem_zpowers g) hgord
  have hD1 : Nat.card D = 1 := by
    have hgcd : Nat.card D ∣ Nat.gcd 9 7 := Nat.dvd_gcd hD9 hD7
    have hg : Nat.gcd 9 7 = 1 := by norm_num
    rw [hg] at hgcd
    exact Nat.dvd_one.mp hgcd
  have hmod' : 9 ≡ Nat.card D [MOD 7] := by
    simpa [D, hPcard] using hmod
  rw [hD1] at hmod'
  norm_num [Nat.ModEq] at hmod'

private lemma gamma_false_315_nonnormal_three (hK : Nat.card K = 315)
    (h5 : ∀ g : K, orderOf g = 5 → Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 15)
    (P : Sylow 3 K) (hn : Nat.card (Sylow 3 K) = 7)
    (hPcard : Nat.card (P : Subgroup K) = 9) : False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let N : Subgroup K := Subgroup.normalizer (P : Set K)
  have hidx : N.index = 7 := by
    have h := P.card_eq_index_normalizer
    rw [hn] at h
    simpa [N] using h.symm
  have hNcard : Nat.card N = 45 := by
    have := Subgroup.card_mul_index (H := N)
    rw [hidx, hK] at this
    omega
  obtain ⟨hN, hhNord⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (by rw [hNcard]; norm_num)
  let h : K := hN
  have hhN : h ∈ N := hN.2
  have hhord : orderOf h = 5 := (Subgroup.orderOf_coe hN).trans hhNord
  let R : Subgroup K := Subgroup.zpowers h
  have hRcard : Nat.card R = 5 := by
    dsimp only [R]
    rw [Nat.card_zpowers, hhord]
  have hRp : IsPGroup 5 R := IsPGroup.of_card (n := 1) (by simpa using hRcard)
  have hRleN : R ≤ Subgroup.normalizer (P : Set K) := Subgroup.zpowers_le.mpr hhN
  have hmod := gamma_card_modEq_of_le_normalizer (q := 5) (P := (P : Subgroup K))
    (R := R) hRp hRleN
  let D : Subgroup K := (P : Subgroup K) ⊓ Subgroup.centralizer (R : Set K)
  have hD9 : Nat.card D ∣ 9 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : D ≤ (P : Subgroup K))
    simpa [D, hPcard] using this
  have hD9eq : Nat.card D = 9 := by
    have hDpos : 0 < Nat.card D := Nat.card_pos
    have hDle : Nat.card D ≤ 9 := Nat.le_of_dvd (by norm_num) hD9
    have hmod' : 9 ≡ Nat.card D [MOD 5] := by
      simpa [D, hPcard] using hmod
    generalize Nat.card D = d at hD9 hDpos hDle hmod' ⊢
    interval_cases d <;>
      first
        | rfl
        | (exfalso; revert hmod'; decide)
        | (exfalso; revert hD9; decide)
  have hDP : D = (P : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge (inf_le_left : D ≤ (P : Subgroup K))
      (by rw [hD9eq, hPcard])
  have hPleCR : (P : Subgroup K) ≤ Subgroup.centralizer (R : Set K) := by
    have hDC : D ≤ Subgroup.centralizer (R : Set K) := inf_le_right
    rwa [hDP] at hDC
  have hPleCh : (P : Subgroup K) ≤ Subgroup.centralizer ({h} : Set K) := by
    refine hPleCR.trans (Subgroup.centralizer_le ?_)
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact Subgroup.mem_zpowers h
  have h9dvd : 9 ∣ Nat.card ↥(Subgroup.centralizer ({h} : Set K)) := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le hPleCh
  have h9dvd15 : 9 ∣ 15 := h9dvd.trans (h5 h hhord)
  norm_num at h9dvd15

theorem gamma_odd_false_315 (hK : Nat.card K = 315)
    (h7 : ∀ g : K, orderOf g = 7 → Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 7)
    (h5 : ∀ g : K, orderOf g = 5 → Nat.card ↥(Subgroup.centralizer ({g} : Set K)) ∣ 15) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hf3 : (Nat.card K).factorization 3 = 2 := by
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
  obtain ⟨P3⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hP3card : Nat.card (P3 : Subgroup K) = 9 := by
    rw [P3.card_eq_multiplicity, hf3]
    norm_num
  rcases h3cases with h3n | h3n
  · haveI : Subsingleton (Sylow 3 K) := (Nat.card_eq_one_iff_unique.1 h3n).1
    exact gamma_false_315_normal_three hK h7 P3 P3.normal_of_subsingleton hP3card
  · exact gamma_false_315_nonnormal_three hK h5 P3 h3n hP3card

end CFSG.EvenSporadicStandard.HNRecog.Section3
