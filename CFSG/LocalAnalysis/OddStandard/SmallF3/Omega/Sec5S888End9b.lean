module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End8b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End9a

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

private lemma eight_dvd_sq_sub_one_of_odd {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨r, hr⟩ := hq
  have h : q ^ 2 - 1 = 4 * (r * (r + 1)) := by
    have hsq : q ^ 2 = 4 * (r * (r + 1)) + 1 := by rw [hr]; ring
    omega
  obtain ⟨s, hs⟩ := Nat.even_mul_succ_self r
  rw [h, hs]
  exact ⟨s, by ring⟩

private lemma even_mul_sq_sub_one_div_two {q : ℕ} (hq : Odd q) :
    Even (q * (q ^ 2 - 1) / 2) := by
  have h8 : 8 ∣ q ^ 2 - 1 := eight_dvd_sq_sub_one_of_odd hq
  obtain ⟨t, ht⟩ := h8
  have h4 : 2 * 2 ∣ q * (q ^ 2 - 1) := ⟨2 * q * t, by rw [ht]; ring⟩
  rw [even_iff_two_dvd]
  exact Nat.dvd_div_of_mul_dvd h4

private lemma eq_of_dvd_two_mul_of_odd {m d : ℕ} (hmd : m ∣ d) (hd : d ∣ 2 * m)
    (hodd : Odd d) (hoddm : Odd m) : d = m := by
  obtain ⟨k, rfl⟩ := hmd
  have hm0 : m ≠ 0 := by
    obtain ⟨j, hj⟩ := hoddm
    omega
  have hk2 : k ∣ 2 := by
    rw [mul_comm 2 m] at hd
    exact (mul_dvd_mul_iff_left hm0).mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with hk | hk
  · rw [hk, mul_one]
  · exfalso
    rw [hk, mul_comm] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul m)

theorem sl2_quotient_of_double_cover {P L : Type} [Group P] [Finite P] [Group L] {z : P}
    (hz : z ∈ center P) (hz2 : orderOf z = 2) (φ : P →* L) (hφ : Function.Surjective φ)
    (hzφ : φ z = 1) {m : ℕ} (hcard : Nat.card φ.ker = 2 * m) (hm : Odd m)
    (hzc : z ∈ commutator P) {p n : ℕ} [Fact p.Prime] (hp : p ≠ 2) (h5 : 5 ≤ p ^ n)
    (e : L ≃* PSL(2, GaloisField p n)) :
    Nonempty (P ⧸ CFSG.oddCore P ≃* SL(2, GaloisField p n)) := by
  classical
  have hzker : z ∈ φ.ker := MonoidHom.mem_ker.mpr hzφ
  obtain ⟨O, hOnorm, hOleR, hOcard, hOinf, hOsup⟩ :=
    exists_odd_normal_complement hz hz2 hzker hcard hm
  haveI hOnormal : O.Normal := hOnorm
  have hOodd : Odd (Nat.card O) := by rw [hOcard]; exact hm
  let η : P ⧸ O →* L := QuotientGroup.lift O φ hOleR
  have hηsurj : Function.Surjective η := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨QuotientGroup.mk' O x, by simp [η]⟩
  have hker : η.ker = Subgroup.map (QuotientGroup.mk' O) φ.ker := by
    change (QuotientGroup.lift O φ hOleR).ker = Subgroup.map (QuotientGroup.mk' O) φ.ker
    rw [QuotientGroup.ker_lift]
  let f : φ.ker →* P ⧸ O := (QuotientGroup.mk' O).comp (φ.ker).subtype
  have hfker : f.ker = O.subgroupOf φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := O) (x : P)).mp (by simpa [f] using hx)
    · intro hx
      show QuotientGroup.mk' O (x : P) = 1
      exact (QuotientGroup.eq_one_iff (N := O) (x : P)).mpr hx
  have hfrange : f.range = η.ker := by
    rw [hker]
    change ((QuotientGroup.mk' O).comp (φ.ker).subtype).range =
      Subgroup.map (QuotientGroup.mk' O) φ.ker
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hfker_card : Nat.card f.ker = m := by
    rw [hfker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOleR).toEquiv, hOcard]
  have hηcard : Nat.card η.ker = 2 := by
    have hmpos : 0 < m := by
      obtain ⟨j, hj⟩ := hm
      omega
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfker_card, hcard, hfrange, mul_comm 2 m] at h
    exact Nat.mul_left_cancel hmpos h
  have hzp : QuotientGroup.mk' O z ∈ Subgroup.center (P ⧸ O) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨p0, rfl⟩ := QuotientGroup.mk'_surjective O g
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' O) (Subgroup.mem_center_iff.mp hz p0)
  have hzerok : QuotientGroup.mk' O z ∈ η.ker := by
    rw [hker]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hzker
  have hz2' : (QuotientGroup.mk' O z) ^ 2 = 1 := by
    rw [← map_pow, show z ^ 2 = 1 by
      have h := pow_orderOf_eq_one z
      rwa [hz2] at h, map_one]
  have hz1' : QuotientGroup.mk' O z ≠ 1 := by
    intro h
    have hzO : z ∈ O := (QuotientGroup.eq_one_iff (N := O) z).mp h
    have hzbot : z ∈ (⊥ : Subgroup P) := by
      have hmem : z ∈ O ⊓ Subgroup.zpowers z := ⟨hzO, Subgroup.mem_zpowers z⟩
      rwa [hOinf] at hmem
    have hz1 : z = 1 := Subgroup.mem_bot.mp hzbot
    rw [hz1] at hz2
    simp at hz2
  have hord_z' : orderOf (QuotientGroup.mk' O z) = 2 :=
    orderOf_eq_prime hz2' hz1'
  have hcard_zp : Nat.card (Subgroup.zpowers (QuotientGroup.mk' O z)) = 2 := by
    rw [Nat.card_zpowers, hord_z']
  have hker_eq : η.ker = Subgroup.zpowers (QuotientGroup.mk' O z) := by
    have hzle : Subgroup.zpowers (QuotientGroup.mk' O z) ≤ η.ker :=
      Subgroup.zpowers_le.mpr hzerok
    exact (Subgroup.eq_of_le_of_card_ge hzle (by rw [hηcard, hcard_zp])).symm
  have hηle : η.ker ≤ Subgroup.center (P ⧸ O) := by
    rw [hker_eq]
    exact Subgroup.zpowers_le.mpr hzp
  have hηcomm : η.ker ≤ commutator (P ⧸ O) := by
    have hzcomm : QuotientGroup.mk' O z ∈ commutator (P ⧸ O) := by
      have hmapc : (commutator P).map (QuotientGroup.mk' O) = commutator (P ⧸ O) := by
        rw [_root_.commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O),
          ← _root_.commutator_def]
      rw [← hmapc]
      exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hzc
    rw [hker_eq]
    exact Subgroup.zpowers_le.mpr hzcomm
  obtain ⟨eSL⟩ := double_cover_sl2 η hηsurj hηcard hηle hηcomm hp h5 e
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h5
  have hGFcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  have h4 : 4 ≤ Nat.card (GaloisField p n) := by rw [hGFcard]; omega
  haveI : IsSimpleGroup (PSL(2, GaloisField p n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  haveI hLsimple : IsSimpleGroup L := e.isSimpleGroup
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hoddPP : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p n)) := by
    refine ⟨p, n, Fact.out, hpodd, ?_, hGFcard⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp at h5
    · exact hpos
  have hevenL : Even (Nat.card L) := by
    have hcardPSL : Nat.card L = Nat.card (PSL(2, GaloisField p n)) :=
      Nat.card_congr e.toEquiv
    rw [hcardPSL, CFSG.GorensteinWalter.psl2_card_formula _ hoddPP, hGFcard]
    exact even_mul_sq_sub_one_div_two hpodd.pow
  have hNle : CFSG.oddCore P ≤ φ.ker := by
    haveI : (Subgroup.map φ (CFSG.oddCore P)).Normal :=
      (inferInstance : (CFSG.oddCore P).Normal).map φ hφ
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.map φ (CFSG.oddCore P)) with hbot | htop
    · intro x hx
      rw [MonoidHom.mem_ker]
      have hmem : φ x ∈ Subgroup.map φ (CFSG.oddCore P) := Subgroup.mem_map_of_mem φ hx
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    · exfalso
      have hNodd : Odd (Nat.card (CFSG.oddCore P)) := CFSG.ABGLocalTools.odd_card_oddCore
      have hdiv : Nat.card L ∣ Nat.card (CFSG.oddCore P) := by
        have h := Subgroup.card_map_dvd (CFSG.oddCore P) φ
        rw [htop] at h
        simpa using h
      have h2L : 2 ∣ Nat.card L := even_iff_two_dvd.mp hevenL
      have h2N : ¬ 2 ∣ Nat.card (CFSG.oddCore P) := hNodd.not_two_dvd_nat
      exact h2N (h2L.trans hdiv)
  have hcore : CFSG.oddCore P = O := by
    have hOle' : O ≤ CFSG.oddCore P := CFSG.ABGLocalTools.le_oddCore_of_normal hOnorm hOodd
    have hNm : Nat.card (CFSG.oddCore P) = m := by
      have hdvd1 : m ∣ Nat.card (CFSG.oddCore P) := by
        rw [← hOcard]
        exact Subgroup.card_dvd_of_le hOle'
      have hdvd2 : Nat.card (CFSG.oddCore P) ∣ 2 * m := by
        rw [← hcard]
        exact Subgroup.card_dvd_of_le hNle
      exact eq_of_dvd_two_mul_of_odd hdvd1 hdvd2 CFSG.ABGLocalTools.odd_card_oddCore hm
    exact (Subgroup.eq_of_le_of_card_ge hOle' (by rw [hNm, hOcard])).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans eSL⟩

end CFSG.OddStandard.SmallF3.Omega
