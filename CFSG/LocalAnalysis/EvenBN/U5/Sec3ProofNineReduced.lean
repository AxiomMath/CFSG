module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineNotNormal
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Nine
public import CFSG.Adapters.LieModelOrders

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

section S3dGeneric

variable {X : Type} [Group X] [Finite X]

theorem s39d_sharp_outcome (hL : GMSK.GMSLinearStandardLayerListKRankOneStatement)
    (hX : CFSG.SectionRank.IsKGroupCat X) {A : Subgroup X} {n : ℕ} (hn : 2 ≤ n) {k : Type}
    [Field k] [Fintype k] (hk : Fintype.card k = 2 ^ n) (φ : A ≃* SL(2, k)) {t : X}
    (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set X))
    (hAn : (A.subgroupOf (centralizer ({t} : Set X))).Normal)
    (hrank : ∀ P : Subgroup X, P ≤ centralizer (A : Set X) → IsPGroup 2 P → Nat.card P ≤ 2)
    (hnn : ¬ (A.map (QuotientGroup.mk' (standardComponentOddCore X))).Normal) :
    GMSK.LayerOutcome (X ⧸ standardComponentOddCore X)
        (A.map (QuotientGroup.mk' (standardComponentOddCore X))) n ∧
      SteinbergBV.OneOrTwoLayerConclusion (A.map (QuotientGroup.mk' (standardComponentOddCore X)))
        (QuotientGroup.mk' (standardComponentOddCore X) t) := by
  have hAt : A ≤ centralizer ({t} : Set X) := fun a ha =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htA a ha)
  refine ⟨GMSK.layerOutcome_oddCore_quotient hL hX hn hk φ ht htA hAn hrank hnn, ?_⟩
  obtain ⟨hstd, -⟩ := GMSK.stdLinearData_odd_quotient hn hk φ ht hAt hAn
    (GMSK.exists_sylow_inf_centralizer_eq_zpowers ht htA hrank) _
    (GMSK.odd_card_standardComponentOddCore X) hnn
  obtain ⟨-, hθt, -, hrel⟩ := s39c_std_quotient hn hk φ ht htA hAn hrank
  have hθA : QuotientGroup.mk' (standardComponentOddCore X) t ∈
      centralizer (((A.map (QuotientGroup.mk' (standardComponentOddCore X)) :
        Subgroup (X ⧸ standardComponentOddCore X)) : Set (X ⧸ standardComponentOddCore X))) := by
    rintro _ ⟨a, ha, rfl⟩
    change QuotientGroup.mk' (standardComponentOddCore X) a *
      QuotientGroup.mk' (standardComponentOddCore X) t = _
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 htA a ha]
  exact GMSK.oneOrTwoLayer_of_stdLinearData (GMSK.standardComponentOddCore_quotient_eq_bot X)
    hstd hθt hθA hrel

end S3dGeneric

section S3dOrders

theorem s39d_odd_pow_sub_one {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [Nat.odd_iff]
  omega

theorem s39d_card_psl2 {Y : Type} [Group Y] {m : ℕ} (hm : 1 ≤ m) (h : LieModel Y .PSL 2 2 m) :
    Nat.card Y = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h]
  show CFSG.Open.ordA 1 (2 ^ m) = _
  unfold CFSG.Open.ordA
  have hg : Nat.gcd (1 + 1) (2 ^ m - 1) = 1 := Nat.coprime_two_left.2 (s39d_odd_pow_sub_one hm)
  rw [show Finset.Icc 2 (1 + 1) = {2} by decide, Finset.prod_singleton, hg, Nat.div_one]
  simp

theorem s39d_card_psl3 {Y : Type} [Group Y] {m : ℕ} (h : LieModel Y .PSL 3 2 m) :
    Nat.card Y * Nat.gcd 3 (2 ^ m - 1) =
      (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) := by
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h]
  show CFSG.Open.ordA 2 (2 ^ m) * Nat.gcd 3 (2 ^ m - 1) = _
  unfold CFSG.Open.ordA
  rw [show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have e3 : (2 + 1 : ℕ) = 3 := rfl
  have e6 : 2 * (2 + 1) / 2 = 3 := by norm_num
  rw [e3, e6]
  have h1 : Nat.gcd 3 (2 ^ m - 1) ∣ 2 ^ m - 1 := Nat.gcd_dvd_right _ _
  have h2 : 2 ^ m - 1 ∣ (2 ^ m) ^ 3 - 1 := Nat.sub_one_dvd_pow_sub_one (2 ^ m) 3
  have hdvd : Nat.gcd 3 (2 ^ m - 1) ∣
      (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (h1.trans h2) _) _
  rw [Nat.div_mul_cancel hdvd]
  ring

theorem s39d_outcome_types {Hq : Type} [Group Hq] [Finite Hq] {At : Subgroup Hq} {f : ℕ}
    (hf : 2 ≤ f) {k : Type} [Field k] [Fintype k] (hk : Fintype.card k = 2 ^ (2 * f))
    (e : ↥At ≃* SL(2, k)) (hLO : GMSK.LayerOutcome Hq At (2 * f)) :
    (Nonempty (CFSG.layer Hq ≃* ↥At × ↥At) ∧
        Nat.card (CFSG.layer Hq) = (2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1)) ^ 2) ∨
      (LieModel (CFSG.layer Hq) .PSL 2 2 (2 * (2 * f)) ∧
        Nat.card (CFSG.layer Hq) = (2 ^ (2 * f)) ^ 2 * (((2 ^ (2 * f)) ^ 2) ^ 2 - 1)) ∨
      (∃ g, g ∣ 3 ∧ Nat.card (CFSG.layer Hq) * g =
        (2 ^ (2 * f)) ^ 3 * ((2 ^ (2 * f)) ^ 3 + 1) * ((2 ^ (2 * f)) ^ 2 - 1)) ∨
      (∃ g, g ∣ 3 ∧ Nat.card (CFSG.layer Hq) * g =
        (2 ^ (2 * f)) ^ 3 * ((2 ^ (2 * f)) ^ 2 - 1) * ((2 ^ (2 * f)) ^ 3 - 1)) := by
  have h42 : 2 ^ (2 * (2 * f)) = (2 ^ (2 * f)) ^ 2 := by rw [← pow_mul]; ring_nf
  rcases hLO with hA | hB | hC | hD
  · obtain ⟨ψ⟩ := hA
    left
    refine ⟨⟨ψ⟩, ?_⟩
    rw [Nat.card_congr ψ.toEquiv, Nat.card_prod, Nat.card_congr e.toEquiv,
      GMSK.Sporadic.card_sl2 hk]
    ring
  · rcases hB with hB | hB | hB
    · right; left
      refine ⟨hB, ?_⟩
      rw [s39d_card_psl2 (by omega) hB, h42]
    · right; right; left
      exact ⟨Nat.gcd 3 (2 ^ (2 * f) + 1), Nat.gcd_dvd_left _ _,
        GMSK.card_mul_gcd_of_lieModel_PSU3 hB⟩
    · right; right; right
      exact ⟨Nat.gcd 3 (2 ^ (2 * f) - 1), Nat.gcd_dvd_left _ _, s39d_card_psl3 hB⟩
  · exfalso
    obtain ⟨h2, -⟩ := hC
    omega
  · exfalso
    obtain ⟨h3, -⟩ := hD
    omega

end S3dOrders

section S3dArith

theorem s39d_ar_a {Q : ℕ} (hQ : 3 ≤ Q) : ¬ (Q ^ 2 - 1) ∣ Q * (Q ^ 3 + 1) := by
  intro h
  obtain ⟨P, hP⟩ : ∃ P, Q ^ 2 = P + 1 := ⟨Q ^ 2 - 1, by have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hP' : Q ^ 2 - 1 = P := by omega
  rw [hP'] at h
  have e : Q * (Q ^ 3 + 1) = P * (P + 1) + (P + (1 + Q)) := by
    have : Q ^ 4 = (P + 1) ^ 2 := by rw [← hP]; ring
    nlinarith [this]
  have h1 : P ∣ 1 + Q := by
    have := (Nat.dvd_add_right (dvd_mul_right P (P + 1))).1 (e ▸ h)
    exact (Nat.dvd_add_right (dvd_refl P)).1 this
  have h2 := Nat.le_of_dvd (by omega) h1
  nlinarith

theorem s39d_ar_b {Q : ℕ} (hQ : 2 ≤ Q) : ¬ (Q ^ 2 + 1) ∣ Q * (Q ^ 3 + 1) := by
  intro h
  obtain ⟨P, hP⟩ : ∃ P, Q ^ 2 = P + 1 := ⟨Q ^ 2 - 1, by have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have e : Q * (Q ^ 3 + 1) = (Q ^ 2 + 1) * (Q ^ 2 - 1) + (Q + 1) := by
    have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : Q ^ 4 = (P + 1) ^ 2 := by rw [← hP]; ring
    have h2 : Q ^ 2 - 1 = P := by omega
    rw [h2]
    nlinarith [this]
  have h1 : (Q ^ 2 + 1) ∣ Q + 1 := (Nat.dvd_add_right (dvd_mul_right _ _)).1 (e ▸ h)
  have h2 := Nat.le_of_dvd (by omega) h1
  nlinarith

theorem s39d_ar_c {Q : ℕ} (hQ : 2 ≤ Q) : ¬ (Q ^ 2 - 1) ∣ Q * (Q ^ 3 - 1) := by
  intro h
  obtain ⟨P, hP⟩ : ∃ P, Q ^ 2 = P + 1 := ⟨Q ^ 2 - 1, by have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hP' : Q ^ 2 - 1 = P := by omega
  rw [hP'] at h
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have e : Q * (Q ^ 3 - 1) = P * (P + 1) + (P + 1 - Q) := by
    have h4 : Q * Q ^ 3 = (P + 1) ^ 2 := by rw [← hP]; ring
    have h5 : Q * (Q ^ 3 - 1) = Q * Q ^ 3 - Q := by rw [Nat.mul_sub, mul_one]
    have h6 : Q ≤ P + 1 := by rw [← hP]; nlinarith
    rw [h5, h4]
    have : (P + 1) ^ 2 = P * (P + 1) + (P + 1) := by ring
    omega
  have h1 : P ∣ P + 1 - Q := by
    have := (Nat.dvd_add_right (dvd_mul_right P (P + 1))).1 (e ▸ h)
    exact this
  have h6 : Q < P + 1 := by rw [← hP]; nlinarith
  have h2 := Nat.le_of_dvd (by omega) h1
  have : P + 1 - Q ≤ P := by omega
  rcases Nat.lt_or_ge (P + 1 - Q) P with hlt | hge
  · have : P + 1 - Q = 0 := by
      obtain ⟨m, hm⟩ := h1
      rcases m with _ | m
      · simpa using hm
      · nlinarith
    omega
  · omega

theorem s39d_ar_d {Q : ℕ} (hQ : 2 ≤ Q) : ¬ (Q ^ 2 + 1) ∣ Q * (Q ^ 3 - 1) := by
  intro h
  have h3 : Q ≤ Q ^ 3 := Nat.le_self_pow (by norm_num) Q
  have e : Q * (Q ^ 3 - 1) + (Q - 1) = (Q ^ 2 + 1) * (Q ^ 2 - 1) := by
    obtain ⟨P, hP⟩ : ∃ P, Q ^ 2 = P + 1 :=
      ⟨Q ^ 2 - 1, by have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
    have h5 : Q * (Q ^ 3 - 1) = Q * Q ^ 3 - Q := by rw [Nat.mul_sub, mul_one]
    have h4 : Q * Q ^ 3 = (P + 1) ^ 2 := by rw [← hP]; ring
    have h6 : Q ≤ Q * Q ^ 3 := by nlinarith
    have h7 : Q ^ 2 - 1 = P := by omega
    rw [h5, h7, hP]
    have : (P + 1 + 1) * P = (P + 1) ^ 2 - 1 := by
      have : (P + 1) ^ 2 = (P + 1 + 1) * P + 1 := by ring
      omega
    rw [this, h4]
    omega
  have h1 : (Q ^ 2 + 1) ∣ Q - 1 := by
    have h8 : (Q ^ 2 + 1) ∣ Q * (Q ^ 3 - 1) + (Q - 1) := e ▸ dvd_mul_right _ _
    exact (Nat.dvd_add_right h).1 h8
  have h2 := Nat.le_of_dvd (by omega) h1
  have h9 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  omega

theorem s39d_ar_e {Q : ℕ} (hQ : 2 ≤ Q) : ¬ (Q ^ 2 - 1) ∣ Q ^ 2 + 1 := by
  intro h
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 4 ≤ Q ^ 2 := by nlinarith
  have : (Q ^ 2 - 1) ∣ 2 := by
    have e : Q ^ 2 + 1 = (Q ^ 2 - 1) + 2 := by omega
    rw [e] at h
    exact (Nat.dvd_add_right (dvd_refl _)).1 h
  have := Nat.le_of_dvd (by omega) this
  omega

theorem s39d_ar_f {Q : ℕ} (hQ : 2 ≤ Q) : ¬ (Q ^ 2 + 1) ∣ Q ^ 2 - 1 := by
  intro h
  have h4 : 4 ≤ Q ^ 2 := by nlinarith
  have := Nat.le_of_dvd (by omega) h
  omega

end S3dArith

section S3dArith2

theorem s39d_coprime_Q_sub {Q : ℕ} (hQ : 2 ≤ Q) : Nat.Coprime Q (Q ^ 2 - 1) := by
  have h1 : Nat.Coprime (Q ^ 2) (Q ^ 2 - 1) :=
    (Nat.coprime_self_sub_right (Nat.one_le_pow _ _ (by omega))).mpr (Nat.coprime_one_right _)
  exact h1.coprime_dvd_left (dvd_pow_self Q two_ne_zero)

theorem s39d_coprime_Q_add {Q : ℕ} : Nat.Coprime Q (Q ^ 2 + 1) := by
  have h1 : Nat.Coprime (Q ^ 2) (Q ^ 2 + 1) := by
    simp [Nat.coprime_self_add_right]
  exact h1.coprime_dvd_left (dvd_pow_self Q two_ne_zero)

theorem s39d_ar_UL_dvd {f : ℕ} (hf : 2 ≤ f) {L g m : ℕ}
    (hL : L * g = (2 ^ (2 * f)) ^ 3 * ((2 ^ (2 * f)) ^ 3 + 1) * ((2 ^ (2 * f)) ^ 2 - 1) ∨
      L * g = (2 ^ (2 * f)) ^ 3 * ((2 ^ (2 * f)) ^ 2 - 1) * ((2 ^ (2 * f)) ^ 3 - 1))
    (hm : m = (2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1)) ^ 2 ∨
      m = (2 ^ (2 * f)) ^ 2 * (((2 ^ (2 * f)) ^ 2) ^ 2 - 1)) : ¬ m ∣ L := by
  have hQ16 : 16 ≤ 2 ^ (2 * f) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * f) = Q at hQ16 hL hm
  intro hd
  have hd' : m ∣ L * g := hd.mul_right g
  obtain ⟨P, hP⟩ : ∃ P, Q ^ 2 = P + 1 :=
    ⟨Q ^ 2 - 1, by have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hP1 : Q ^ 2 - 1 = P := by omega
  have hP2 : (Q ^ 2) ^ 2 - 1 = P * (Q ^ 2 + 1) := by
    have : (Q ^ 2) ^ 2 = P * (Q ^ 2 + 1) + 1 := by rw [hP]; ring
    omega
  have hQpos : 0 < Q := by omega
  have hPpos : 0 < P := by nlinarith
  rw [hP1] at hL hm
  rw [hP2] at hm
  rcases hL with hL | hL <;> rcases hm with hm | hm <;> rw [hL, hm] at hd'
  ·
    have h1 : (Q * P) * (Q * P) ∣ (Q * P) * (Q ^ 2 * (Q ^ 3 + 1)) := by
      convert hd' using 1 <;> ring
    have h2 := Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos hQpos hPpos) h1
    have h3 : Q * P ∣ Q * (Q * (Q ^ 3 + 1)) := by convert h2 using 1; ring
    have h4 := Nat.dvd_of_mul_dvd_mul_left hQpos h3
    rw [← hP1] at h4
    exact s39d_ar_a (by omega) h4
  ·
    have h1 : (Q ^ 2 * P) * (Q ^ 2 + 1) ∣ (Q ^ 2 * P) * (Q * (Q ^ 3 + 1)) := by
      convert hd' using 1 <;> ring
    have h2 := Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos (by positivity) hPpos) h1
    exact s39d_ar_b (by omega) h2
  ·
    have h1 : (Q * P) * (Q * P) ∣ (Q * P) * (Q ^ 2 * (Q ^ 3 - 1)) := by
      convert hd' using 1 <;> ring
    have h2 := Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos hQpos hPpos) h1
    have h3 : Q * P ∣ Q * (Q * (Q ^ 3 - 1)) := by convert h2 using 1; ring
    have h4 := Nat.dvd_of_mul_dvd_mul_left hQpos h3
    rw [← hP1] at h4
    exact s39d_ar_c (by omega) h4
  ·
    have h1 : (Q ^ 2 * P) * (Q ^ 2 + 1) ∣ (Q ^ 2 * P) * (Q * (Q ^ 3 - 1)) := by
      convert hd' using 1 <;> ring
    have h2 := Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos (by positivity) hPpos) h1
    exact s39d_ar_d (by omega) h2

theorem s39d_ar_UL_pow {f : ℕ} (hf : 2 ≤ f) {L g m : ℕ} (hg : g ∣ 3)
    (hL : L * g = (2 ^ (2 * f)) ^ 3 * ((2 ^ (2 * f)) ^ 3 + 1) * ((2 ^ (2 * f)) ^ 2 - 1) ∨
      L * g = (2 ^ (2 * f)) ^ 3 * ((2 ^ (2 * f)) ^ 2 - 1) * ((2 ^ (2 * f)) ^ 3 - 1))
    (hm : m = (2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1)) ^ 2 ∨
      m = (2 ^ (2 * f)) ^ 2 * (((2 ^ (2 * f)) ^ 2) ^ 2 - 1)) : ¬ L ∣ m := by
  have hQ16 : 16 ≤ 2 ^ (2 * f) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcopg : Nat.Coprime ((2 ^ (2 * f)) ^ 3) g := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hg with rfl | rfl
    · exact Nat.coprime_one_right _
    · exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 2 3))
  generalize 2 ^ (2 * f) = Q at hQ16 hcopg hL hm
  intro hd
  have hQL : Q ^ 3 ∣ L := by
    have h1 : Q ^ 3 ∣ L * g := by
      rcases hL with hL | hL <;> rw [hL]
      · exact Dvd.intro ((Q ^ 3 + 1) * (Q ^ 2 - 1)) (by ring)
      · exact Dvd.intro ((Q ^ 2 - 1) * (Q ^ 3 - 1)) (by ring)
    exact hcopg.dvd_of_dvd_mul_right h1
  have hQm : Q ^ 3 ∣ m := hQL.trans hd
  have hQpos : 0 < Q := by omega
  obtain ⟨P, hP⟩ : ∃ P, Q ^ 2 = P + 1 :=
    ⟨Q ^ 2 - 1, by have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hP1 : Q ^ 2 - 1 = P := by omega
  have hP2 : (Q ^ 2) ^ 2 - 1 = P * (Q ^ 2 + 1) := by
    have : (Q ^ 2) ^ 2 = P * (Q ^ 2 + 1) + 1 := by rw [hP]; ring
    omega
  have hcopP : Nat.Coprime Q P := hP1 ▸ s39d_coprime_Q_sub (by omega)
  have hcopS : Nat.Coprime Q (Q ^ 2 + 1) := s39d_coprime_Q_add
  rw [hP1] at hm
  rw [hP2] at hm
  rcases hm with hm | hm
  · rw [hm] at hQm
    have h1 : Q ^ 2 * Q ∣ Q ^ 2 * P ^ 2 := by convert hQm using 1 <;> ring
    have h2 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    have h3 := (hcopP.pow_right 2).eq_one_of_dvd h2
    omega
  · rw [hm] at hQm
    have h1 : Q ^ 2 * Q ∣ Q ^ 2 * (P * (Q ^ 2 + 1)) := by convert hQm using 1 <;> ring
    have h2 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    have h3 := (Nat.Coprime.mul_right hcopP hcopS).eq_one_of_dvd h2
    omega

theorem s39d_ar_mix {f : ℕ} (hf : 2 ≤ f) :
    ¬ ((2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1)) ^ 2 ∣
        (2 ^ (2 * f)) ^ 2 * (((2 ^ (2 * f)) ^ 2) ^ 2 - 1)) ∧
      ¬ ((2 ^ (2 * f)) ^ 2 * (((2 ^ (2 * f)) ^ 2) ^ 2 - 1) ∣
        (2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1)) ^ 2) := by
  have hQ16 : 16 ≤ 2 ^ (2 * f) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * f) = Q at hQ16
  have hQpos : 0 < Q := by omega
  obtain ⟨P, hP⟩ : ∃ P, Q ^ 2 = P + 1 :=
    ⟨Q ^ 2 - 1, by have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hP1 : Q ^ 2 - 1 = P := by omega
  have hP2 : (Q ^ 2) ^ 2 - 1 = P * (Q ^ 2 + 1) := by
    have : (Q ^ 2) ^ 2 = P * (Q ^ 2 + 1) + 1 := by rw [hP]; ring
    omega
  have hPpos : 0 < P := by nlinarith
  rw [hP1, hP2]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : (Q ^ 2 * P) * P ∣ (Q ^ 2 * P) * (Q ^ 2 + 1) := by
      convert h using 1 <;> ring
    have h2 := Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos (by positivity) hPpos) h1
    rw [← hP1] at h2
    exact s39d_ar_e (by omega) h2
  · have h1 : (Q ^ 2 * P) * (Q ^ 2 + 1) ∣ (Q ^ 2 * P) * P := by
      convert h using 1 <;> ring
    have h2 := Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos (by positivity) hPpos) h1
    rw [← hP1] at h2
    exact s39d_ar_f (by omega) h2

end S3dArith2

section S3dE

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39d_I₁_le_H (hp : d.CaseHyp) :
    d.I₁ ≤ normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G) :=
  fun _ hx => hp.hyp.I_le_H (d.I₁_le_I hx)

theorem s39d_I₁_le_B₂ (hp : d.CaseHyp) :
    d.I₁ ≤ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G) := fun x hx =>
  ⟨mem_normalizer_fintype fun _ hb => hp.hyp.conj_mem_B₂ (s39d_I₁_le_H hp hx).1
    (s39d_I₁_le_H hp hx).2 hb, (s39d_I₁_le_H hp hx).2⟩

theorem s39d_I₁_le_E (hp : d.CaseHyp) : d.I₁ ≤ normalizer (d.E : Set G) := fun _ hx =>
  hp.hyp.normalizer_B₄_le_normalizer_E hp.gms (hp.hyp.I_le_normalizer_B₄ (d.I₁_le_I hx))

theorem s39d_I₁_le_VA (hp : d.CaseHyp) :
    d.I₁ ≤ normalizer ((d.V ⊔ d.A₂ : Subgroup G) : Set G) := fun x hx =>
  Common.mem_normalizer_sup (hp.hyp.I_le_normalizer_V (d.I₁_le_I hx))
    (mem_normalizer_fintype fun _ ha => hp.hyp.conj_mem_A₂ (s39d_I₁_le_H hp hx).1
      (s39d_I₁_le_H hp hx).2 ha)

theorem s39d_card_C_E_I₁ (hp : d.CaseHyp) :
    (2 ^ f) ^ 4 ≤ Nat.card ↥(d.E ⊓ centralizer (d.I₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : 2 ≤ f := hp.hyp.two_le
  obtain ⟨-, -, -, -, ⟨ψ, hψs, hψk, -, hψe⟩, -⟩ := hp.hyp.sec3_6 hp.gms
  obtain ⟨-, ⟨hZ₂, -⟩, -, -, ⟨hA₂, hA₂C⟩, -, -, -, hA₂A₃, -, -, -⟩ := d.sec2_1_two hf2
  set R₀ : Subgroup G := d.E ⊓ centralizer (d.I₁ : Set G) with hR₀
  set C : Subgroup G := d.P ⊓ centralizer (d.I₁ : Set G) with hC
  have hCcard : Nat.card C = (2 ^ f) ^ 2 := by rw [hC, ← d.U₁_eq hf2]; exact d.card_U₁
  have hCA₂ : C ≤ d.A₂ := hA₂ ▸ le_sup_right
  have hAE : d.A₂ ≤ d.E := hp.hyp.A₂_le_E hp.gms
  have hCE : C ≤ d.E := hCA₂.trans hAE
  have hCR : C ≤ R₀ := le_inf hCE inf_le_right
  have hZpA : d.Zp ≤ d.A₂ ⊓ d.A₃ := by
    rw [hA₂A₃]
    exact (hZ₂ ▸ le_sup_left : d.Zp ≤ d.Z₂p).trans le_sup_left
  have hZpC : d.Zp ⊓ C = ⊥ := by
    rw [eq_bot_iff, ← hA₂C]
    exact inf_le_inf_right _ hZpA
  have hVAE : d.V ⊔ d.A₂ ≤ d.E := hp.hyp.VA_le_E hp.gms
  have hEn : d.E ≤ normalizer ((d.V ⊔ d.A₂ : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVAE).1 (hψk ▸ MonoidHom.normal_ker ψ)
  haveI : Group.IsNilpotent d.E := IsPGroup.isNilpotent (hp.hyp.isPGroup_E hp.gms)
  have hsolv : Group.IsSolvable d.E := inferInstance
  have hcop : (Nat.card d.I₁).Coprime (Nat.card d.E) := by
    rw [hp.hyp.card_E hp.gms]
    have hodd : Odd (Nat.card d.I₁) :=
      (Data.odd_card_I d).of_dvd_nat (Subgroup.card_dvd_of_le (d.I₁_le_I))
    exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd))
  have hlift : ∀ u (hu : u ∈ C), ∃ c : G, c ∈ R₀ ∧ ∃ hc : c ∈ d.E,
      ψ ⟨c, hc⟩ = QuotientGroup.mk (⟨u, hCA₂ hu⟩ : d.A₂) := by
    intro u hu
    obtain ⟨e, he⟩ := hψs (QuotientGroup.mk (⟨u, hCA₂ hu⟩ : d.A₂))
    have hfix : ∀ s ∈ d.I₁, (e : G)⁻¹ * (s * e * s⁻¹) ∈ d.V ⊔ d.A₂ := by
      intro s hs
      have hsE : s * (e : G) * s⁻¹ ∈ d.E := (mem_normalizer_iff.1 (s39d_I₁_le_E hp hs) _).1 e.2
      have hsu : s * u * s⁻¹ = u := by
        have := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hu).2 s hs
        rw [this, mul_inv_cancel_right]
      have hsuA : s * u * s⁻¹ ∈ d.A₂ := by rw [hsu]; exact hCA₂ hu
      have h1 := hψe s (s39d_I₁_le_B₂ hp hs) e ⟨u, hCA₂ hu⟩ hsE hsuA he
      have h2 : ψ ⟨s * (e : G) * s⁻¹, hsE⟩ = ψ e := by
        rw [h1, he]
        congr 1
        exact Subtype.ext hsu
      have h3 : ψ (e⁻¹ * ⟨s * (e : G) * s⁻¹, hsE⟩) = 1 := by rw [map_mul, map_inv, h2, inv_mul_cancel]
      have h4 : e⁻¹ * ⟨s * (e : G) * s⁻¹, hsE⟩ ∈ ψ.ker := h3
      rw [hψk] at h4
      exact h4
    obtain ⟨c, hc, n, hn, hcn⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime hVAE hEn
      (s39d_I₁_le_E hp) (s39d_I₁_le_VA hp) hsolv hcop e.2 hfix
    have hcE : c ∈ d.E := (Subgroup.mem_inf.1 hc).1
    refine ⟨c, hc, hcE, ?_⟩
    have hnE : n ∈ d.E := hVAE hn
    have hnk : ψ ⟨n, hnE⟩ = 1 := by
      have : (⟨n, hnE⟩ : d.E) ∈ ψ.ker := by rw [hψk]; exact hn
      exact this
    have heq : e = ⟨c, hcE⟩ * ⟨n, hnE⟩ := Subtype.ext hcn
    rw [← he, heq, map_mul, hnk, mul_one]
  set ψ₀ : ↥R₀ →* d.A₂ ⧸ d.Zp.subgroupOf d.A₂ :=
    ψ.comp (Subgroup.inclusion (inf_le_left : R₀ ≤ d.E)) with hψ₀
  have hcard : Nat.card R₀ = Nat.card ψ₀.ker * Nat.card ψ₀.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hkerge : (2 ^ f) ^ 2 ≤ Nat.card ψ₀.ker := by
    have hsub : C.subgroupOf R₀ ≤ ψ₀.ker := by
      intro x hx
      have hxC : (x : G) ∈ C := hx
      have : (Subgroup.inclusion (inf_le_left : R₀ ≤ d.E) x) ∈ ψ.ker := by
        rw [hψk]
        exact mem_sup_right (hCA₂ hxC)
      exact this
    calc (2 ^ f) ^ 2 = Nat.card C := hCcard.symm
      _ = Nat.card (C.subgroupOf R₀) := (Nat.card_congr (subgroupOfEquivOfLe hCR).toEquiv).symm
      _ ≤ Nat.card ψ₀.ker := Subgroup.card_le_of_le hsub
  have hrangege : (2 ^ f) ^ 2 ≤ Nat.card ψ₀.range := by
    set Rg : Subgroup (d.A₂ ⧸ d.Zp.subgroupOf d.A₂) :=
      (C.subgroupOf d.A₂).map (QuotientGroup.mk' (d.Zp.subgroupOf d.A₂)) with hRg
    have hRgle : Rg ≤ ψ₀.range := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨c, hcR, hcE, hψc⟩ := hlift a.1 ha
      exact ⟨⟨c, hcR⟩, hψc⟩
    have hinj : Function.Injective ((QuotientGroup.mk' (d.Zp.subgroupOf d.A₂)).comp
        (C.subgroupOf d.A₂).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : (x : d.A₂) ∈ d.Zp.subgroupOf d.A₂ := (QuotientGroup.eq_one_iff _).1 hx
      have h2 : ((x : d.A₂) : G) ∈ d.Zp ⊓ C := Subgroup.mem_inf.2 ⟨h1, x.2⟩
      rw [hZpC, Subgroup.mem_bot] at h2
      exact Subtype.ext (Subtype.ext h2)
    have hRgcard : Nat.card Rg = Nat.card C := by
      have hr : ((QuotientGroup.mk' (d.Zp.subgroupOf d.A₂)).comp
          (C.subgroupOf d.A₂).subtype).range = Rg := by
        rw [MonoidHom.range_comp, range_subtype]
      rw [← hr, ← Nat.card_congr (subgroupOfEquivOfLe hCA₂).toEquiv]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    calc (2 ^ f) ^ 2 = Nat.card C := hCcard.symm
      _ = Nat.card Rg := hRgcard.symm
      _ ≤ Nat.card ψ₀.range := Subgroup.card_le_of_le hRgle
  rw [hcard]
  calc (2 ^ f) ^ 4 = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by ring
    _ ≤ Nat.card ψ₀.ker * Nat.card ψ₀.range := Nat.mul_le_mul hkerge hrangege

end S3dE

section S3dBar

variable {G : Type} [Group G] [Finite G]

theorem s39d_card_bar {A Y : Subgroup G} (hYN : Y ≤ normalizer (A : Set G)) (hYA : Y ⊓ A = ⊥) :
    Nat.card (bar A Y) = Nat.card Y := by
  have hinj : Function.Injective
      ((proj A).comp (Y.subgroupOf (normalizer (A : Set G))).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxA : ((x : normalizer (A : Set G)) : G) ∈ A := proj_eq_one_iff.1 hx
    have hxY : ((x : normalizer (A : Set G)) : G) ∈ Y := x.2
    have : ((x : normalizer (A : Set G)) : G) ∈ Y ⊓ A := ⟨hxY, hxA⟩
    rw [hYA, Subgroup.mem_bot] at this
    exact Subtype.ext (Subtype.ext this)
  have hr : ((proj A).comp (Y.subgroupOf (normalizer (A : Set G))).subtype).range = bar A Y := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hYN).toEquiv]

end S3dBar

section S3dH1

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39d_E_le_normalizer_D (hp : d.CaseHyp) (k : d.Know92) :
    d.E ≤ normalizer (d.D : Set G) := by
  obtain ⟨S, hS, hPS⟩ := s39c_exists_sylow_L₂ hp
  obtain ⟨hSED, -, hDchar⟩ := k.s9_1 S hS hPS
  have hDS : d.D ≤ S := hSED ▸ le_sup_right
  have hSN : S ≤ normalizer (d.D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDS).1 inferInstance
  exact (hSED ▸ le_sup_left : d.E ≤ S).trans hSN

variable (d)

abbrev s39dC₁ : Subgroup G := normalizer (d.D : Set G) ⊓ centralizer (d.I₁ : Set G)

abbrev s39dH₁ : Subgroup (Bar d.D) := bar d.D (s39dC₁ d)

variable {d}

theorem s39d_N₁_le_C₁ (hp : d.CaseHyp) : d.N₁ ≤ s39dC₁ d :=
  le_inf (hp.hyp.N₁_le_normalizer_D) d.N₁_le_centralizer_I₁

theorem s39d_t_mem_C₁ (hp : d.CaseHyp) : d.t ∈ s39dC₁ d :=
  ⟨hp.hyp.t_mem_normalizer_D, hp.hyp.t_mem_centralizer_I₁⟩

theorem s39d_R₀_le_C₁ (hp : d.CaseHyp) (k : d.Know92) :
    d.E ⊓ centralizer (d.I₁ : Set G) ≤ s39dC₁ d :=
  le_inf (inf_le_left.trans (s39d_E_le_normalizer_D hp k)) inf_le_right

end S3dH1

section S3dH1Std

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39d_J_le_H₁ (hp : d.CaseHyp) : bar d.D d.N₁ ≤ s39dH₁ d :=
  bar_mono (s39d_N₁_le_C₁ hp)

theorem s39d_t_mem_H₁ (hp : d.CaseHyp) (hi : d.Sec39Input) :
    proj d.D ⟨d.t, hi.t_mem⟩ ∈ s39dH₁ d := proj_mem_bar (s39d_t_mem_C₁ hp)

theorem s39d_normal_H₁ (hp : d.CaseHyp) (hi : d.Sec39Input) :
    (((bar d.D d.N₁).subgroupOf (s39dH₁ d)).subgroupOf
      (centralizer ({(⟨proj d.D ⟨d.t, hi.t_mem⟩, s39d_t_mem_H₁ hp hi⟩ : ↥(s39dH₁ d))} :
        Set ↥(s39dH₁ d)))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hnJ : ((n : ↥(s39dH₁ d)) : Bar d.D) ∈ bar d.D d.N₁ := hn
  have hcn : ((n : ↥(s39dH₁ d)) : Bar d.D) ∈
      centralizer ({proj d.D ⟨d.t, hi.t_mem⟩} : Set (Bar d.D)) := by
    have := Subgroup.mem_centralizer_singleton_iff.1 n.2
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have hcg : ((g : ↥(s39dH₁ d)) : Bar d.D) ∈
      centralizer ({proj d.D ⟨d.t, hi.t_mem⟩} : Set (Bar d.D)) := by
    have := Subgroup.mem_centralizer_singleton_iff.1 g.2
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have key := hi.normal.conj_mem ⟨_, hcn⟩ hnJ ⟨_, hcg⟩
  exact key

theorem s39d_rank_H₁ (hp : d.CaseHyp) (hi : d.Sec39Input) :
    ∀ P : Subgroup ↥(s39dH₁ d),
      P ≤ centralizer ((((bar d.D d.N₁).subgroupOf (s39dH₁ d)) : Subgroup ↥(s39dH₁ d)) :
        Set ↥(s39dH₁ d)) → IsPGroup 2 P → Nat.card P ≤ 2 := by
  intro P hPC hP2
  have h1 : P.map (s39dH₁ d).subtype ≤ centralizer ((bar d.D d.N₁ : Subgroup (Bar d.D)) :
      Set (Bar d.D)) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_centralizer_iff.2 fun j hj => ?_
    have hj' : (⟨j, s39d_J_le_H₁ hp hj⟩ : ↥(s39dH₁ d)) ∈
        (bar d.D d.N₁).subgroupOf (s39dH₁ d) := hj
    have := mem_centralizer_iff.1 (hPC hx) _ hj'
    exact congrArg Subtype.val this
  have h2 := hi.rank _ h1 (hP2.map _)
  rwa [card_map_of_injective (s39dH₁ d).subtype_injective] at h2

end S3dH1Std

section S3dH1Out

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39d_H₁_data (hp : d.CaseHyp) (hi : d.Sec39Input) :
    ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ (2 * f) ∧
      Nonempty (↥((bar d.D d.N₁).subgroupOf (s39dH₁ d)) ≃* SL(2, k)) := by
  obtain ⟨k, _, _, hk, ⟨φ⟩⟩ := hi.field
  exact ⟨k, inferInstance, inferInstance, hk,
    ⟨(subgroupOfEquivOfLe (s39d_J_le_H₁ hp)).trans φ⟩⟩

theorem s39d_ordertwo_H₁ (hp : d.CaseHyp) (hi : d.Sec39Input) :
    orderOf (⟨proj d.D ⟨d.t, hi.t_mem⟩, s39d_t_mem_H₁ hp hi⟩ : ↥(s39dH₁ d)) = 2 := by
  rw [Subgroup.orderOf_mk]
  exact hi.order_two

theorem s39d_centralizes_H₁ (hp : d.CaseHyp) (hi : d.Sec39Input) :
    (⟨proj d.D ⟨d.t, hi.t_mem⟩, s39d_t_mem_H₁ hp hi⟩ : ↥(s39dH₁ d)) ∈
      centralizer ((((bar d.D d.N₁).subgroupOf (s39dH₁ d)) : Subgroup ↥(s39dH₁ d)) :
        Set ↥(s39dH₁ d)) :=
  mem_centralizer_iff.2 fun a ha => Subtype.ext (mem_centralizer_iff.1 hi.centralizes a.1 ha)

theorem s39d_not_normal_H₁ (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e)
    (hi : d.Sec39Input) :
    ¬ (((bar d.D d.N₁).subgroupOf (s39dH₁ d)).map
      (QuotientGroup.mk' (standardComponentOddCore ↥(s39dH₁ d)))).Normal := by
  have hf2 : 2 ≤ f := hp.hyp.two_le
  obtain ⟨kf, _, _, hkf, ⟨φ₁⟩⟩ := s39d_H₁_data hp hi
  set R₀ : Subgroup G := d.E ⊓ centralizer (d.I₁ : Set G) with hR₀
  have hR₀C := s39d_R₀_le_C₁ hp k
  have hR₀N : R₀ ≤ normalizer (d.D : Set G) := hR₀C.trans inf_le_left
  have hR₀D : R₀ ⊓ d.D = ⊥ := by
    rw [eq_bot_iff, ← he.centralizer_I₁]
    exact inf_le_inf_right _ inf_le_right |>.trans (by rw [inf_comm])
  have hE2 : IsPGroup 2 d.E := hp.hyp.isPGroup_E hp.gms
  have hbR : bar d.D R₀ ≤ s39dH₁ d := bar_mono hR₀C
  have hPpg : IsPGroup 2 ((bar d.D R₀).subgroupOf (s39dH₁ d)) :=
    (isPGroup_bar (hE2.to_inf_left)).comap_subtype
  have hcard : (2 ^ f) ^ 4 ≤ Nat.card ((bar d.D R₀).subgroupOf (s39dH₁ d)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hbR).toEquiv, s39d_card_bar hR₀N hR₀D]
    exact s39d_card_C_E_I₁ hp
  have hnum := s39c_four_mul_lt f hf2
  have hbig : 2 * (2 ^ (2 * f) * (2 * f)) < Nat.card ((bar d.D R₀).subgroupOf (s39dH₁ d)) := by
    have h5 : 2 ^ (2 * f) * (4 * f) < (2 ^ f) ^ 4 :=
      calc 2 ^ (2 * f) * (4 * f) < 2 ^ (2 * f) * 2 ^ (2 * f) :=
            Nat.mul_lt_mul_of_pos_left hnum (by positivity)
        _ = (2 ^ f) ^ 4 := by ring
    calc 2 * (2 ^ (2 * f) * (2 * f)) = 2 ^ (2 * f) * (4 * f) := by ring
      _ < (2 ^ f) ^ 4 := h5
      _ ≤ _ := hcard
  exact s39c_not_normal_of_card (by omega) hkf φ₁ (s39d_ordertwo_H₁ hp hi)
    (s39d_centralizes_H₁ hp hi) (s39d_normal_H₁ hp hi) (s39d_rank_H₁ hp hi) hPpg hbig

end S3dH1Out

section S3dK

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39d_mem_bar {A X : Subgroup G} {y : Bar A} :
    y ∈ bar A X ↔ ∃ x : normalizer (A : Set G), (x : G) ∈ X ∧ proj A x = y := by
  unfold bar
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem s39d_normalClosure_le (hp : d.CaseHyp) :
    normalClosure ((((bar d.D d.N₁).subgroupOf (s39dH₁ d) : Subgroup ↥(s39dH₁ d))) :
        Set ↥(s39dH₁ d)) ≤
      (bar d.D (normalClosureIn (s39dC₁ d) d.N₁)).subgroupOf (s39dH₁ d) := by
  haveI : ((bar d.D (normalClosureIn (s39dC₁ d) d.N₁)).subgroupOf (s39dH₁ d)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : ((n : ↥(s39dH₁ d)) : Bar d.D) ∈ bar d.D (normalClosureIn (s39dC₁ d) d.N₁) := hn
    obtain ⟨z, hzY, hz⟩ := s39d_mem_bar.1 hn'
    obtain ⟨c, hcC, hc⟩ := s39d_mem_bar.1 g.2
    show ((g * n * g⁻¹ : ↥(s39dH₁ d)) : Bar d.D) ∈ bar d.D (normalClosureIn (s39dC₁ d) d.N₁)
    refine s39d_mem_bar.2 ⟨c * z * c⁻¹, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 (le_normalizer_normalClosureIn (s39dC₁ d) d.N₁ hcC) (z : G)).1
        hzY
      simpa using this
    · simp only [map_mul, map_inv, hz, hc]
      rfl
  refine normalClosure_le_normal fun a ha => ?_
  have ha' : ((a : ↥(s39dH₁ d)) : Bar d.D) ∈ bar d.D d.N₁ := ha
  obtain ⟨n, hnN, hn⟩ := s39d_mem_bar.1 ha'
  exact s39d_mem_bar.2 ⟨n, le_normalClosureIn (s39d_N₁_le_C₁ hp) hnN, hn⟩

end S3dK

section S3dLayer

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39d_Y₁_le_M₁ (d : Data G h) : normalClosureIn (s39dC₁ d) d.N₁ ≤ d.M₁ :=
  normalClosureIn_le d.N₁_le_M₁ fun _ hc =>
    d.centralizer_I₁_le_normalizer_M₁ (Subgroup.mem_inf.1 hc).2

theorem s39d_Y₁_le_C₁ (d : Data G h) : normalClosureIn (s39dC₁ d) d.N₁ ≤ s39dC₁ d :=
  normalClosureIn_le_self _ _

theorem s39d_Y₁_inf_D (he : d.Sec39e) : normalClosureIn (s39dC₁ d) d.N₁ ⊓ d.D = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ d.D ⊓ centralizer (d.I₁ : Set G) :=
    ⟨hx.2, (Subgroup.mem_inf.1 (s39d_Y₁_le_C₁ d hx.1)).2⟩
  rw [he.centralizer_I₁] at h1
  exact h1

theorem s39d_inj_of_card {X Z : Type*} [Group X] [Finite X] [Group Z] (φ : X →* Z)
    (K : Subgroup X) (hK : Nat.card (K.map φ) = Nat.card K) : ∀ x ∈ K, φ x = 1 → x = 1 := by
  set φ' : K →* Z := φ.comp K.subtype with hφ'
  have hr : φ'.range = K.map φ := by rw [hφ', MonoidHom.range_comp, range_subtype]
  have hcard : Nat.card K = Nat.card φ'.ker * Nat.card φ'.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hr, hK] at hcard
  have h1 : Nat.card φ'.ker = 1 := by
    have : Nat.card φ'.ker * Nat.card K = 1 * Nat.card K := by rw [one_mul]; exact hcard.symm
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
  have h2 : φ'.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  intro x hx hφx
  have : (⟨x, hx⟩ : K) ∈ φ'.ker := hφx
  rw [h2, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem s39d_oddCore_le {X : Type*} [Group X] [Finite X] (H₁ : Subgroup X) :
    (standardComponentOddCore X).subgroupOf H₁ ≤ standardComponentOddCore ↥H₁ := by
  have hn : ((standardComponentOddCore X).subgroupOf H₁).Normal :=
    (inferInstance : (standardComponentOddCore X).Normal).subgroupOf H₁
  have hodd : Odd (Nat.card ((standardComponentOddCore X).subgroupOf H₁)) := by
    have h1 : Nat.card ((standardComponentOddCore X).subgroupOf H₁) =
        Nat.card (((standardComponentOddCore X).subgroupOf H₁).map H₁.subtype) :=
      (card_map_of_injective H₁.subtype_injective).symm
    have h2 : ((standardComponentOddCore X).subgroupOf H₁).map H₁.subtype ≤
        standardComponentOddCore X := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    rw [h1]
    exact (GMSK.odd_card_standardComponentOddCore X).of_dvd_nat (Subgroup.card_dvd_of_le h2)
  exact le_sSup ⟨hn, hodd⟩

end S3dLayer

section S3dLayer2

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39d_H₁_layer (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e)
    (hi : d.Sec39Input) :
    ∃ L : ℕ, L ∣ Nat.card (normalClosureIn (s39dC₁ d) d.N₁) ∧
      (L = Nat.card (normalClosureIn (s39dC₁ d) d.N₁) →
        bar d.D (normalClosureIn (s39dC₁ d) d.N₁) ⊓ OD d = ⊥) ∧
      (L = (2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1)) ^ 2 ∨
        L = (2 ^ (2 * f)) ^ 2 * (((2 ^ (2 * f)) ^ 2) ^ 2 - 1) ∨
        ∃ g, g ∣ 3 ∧ (L * g = (2 ^ (2 * f)) ^ 3 * ((2 ^ (2 * f)) ^ 3 + 1) *
            ((2 ^ (2 * f)) ^ 2 - 1) ∨
          L * g = (2 ^ (2 * f)) ^ 3 * ((2 ^ (2 * f)) ^ 2 - 1) * ((2 ^ (2 * f)) ^ 3 - 1))) := by
  have hf2 : 2 ≤ f := hp.hyp.two_le
  obtain ⟨kf, _, _, hkf, ⟨φ₁⟩⟩ := s39d_H₁_data hp hi
  have hn : 2 ≤ 2 * f := by omega
  obtain ⟨hLO, hOT⟩ := s39d_sharp_outcome hp.gmsL (hi.kgroup.subgroup (s39dH₁ d)) hn hkf φ₁
    (s39d_ordertwo_H₁ hp hi) (s39d_centralizes_H₁ hp hi) (s39d_normal_H₁ hp hi)
    (s39d_rank_H₁ hp hi) (s39d_not_normal_H₁ hp k he hi)
  obtain ⟨⟨e1⟩, -, -, -⟩ := s39c_std_quotient hn hkf φ₁ (s39d_ordertwo_H₁ hp hi)
    (s39d_centralizes_H₁ hp hi) (s39d_normal_H₁ hp hi) (s39d_rank_H₁ hp hi)
  have htypes := s39d_outcome_types hf2 hkf e1 hLO
  set H₁ := s39dH₁ d with hH₁
  set Y₁ := normalClosureIn (s39dC₁ d) d.N₁ with hY₁
  set O₁ := standardComponentOddCore ↥H₁ with hO₁
  set θ₁ := QuotientGroup.mk' O₁ with hθ₁
  set A₁ : Subgroup ↥H₁ := (bar d.D d.N₁).subgroupOf H₁ with hA₁
  set KK : Subgroup ↥H₁ := normalClosure ((A₁ : Subgroup ↥H₁) : Set ↥H₁) with hKK
  have hlayer : CFSG.layer (↥H₁ ⧸ O₁) = KK.map θ₁ := by
    rw [← hOT.2.2.2.1, hKK, Subgroup.map_normalClosure _ θ₁ (QuotientGroup.mk'_surjective O₁),
      Subgroup.coe_map]
  have hYN : Y₁ ≤ normalizer (d.D : Set G) := (s39d_Y₁_le_C₁ d).trans inf_le_left
  have hbarH : bar d.D Y₁ ≤ H₁ := bar_mono (s39d_Y₁_le_C₁ d)
  have hcardbar : Nat.card (bar d.D Y₁) = Nat.card Y₁ := s39d_card_bar hYN (s39d_Y₁_inf_D he)
  have hcardsub : Nat.card ((bar d.D Y₁).subgroupOf H₁) = Nat.card Y₁ := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hbarH).toEquiv, hcardbar]
  have hKY : KK ≤ (bar d.D Y₁).subgroupOf H₁ := s39d_normalClosure_le hp
  have hKdvd : Nat.card KK ∣ Nat.card Y₁ := hcardsub ▸ Subgroup.card_dvd_of_le hKY
  obtain ⟨m, -, hmcard⟩ := s39c_card_eq_mul_map O₁ KK
  have hLK : Nat.card (CFSG.layer (↥H₁ ⧸ O₁)) ∣ Nat.card KK := by
    rw [hlayer]
    exact ⟨m, by rw [hmcard, mul_comm]⟩
  refine ⟨Nat.card (CFSG.layer (↥H₁ ⧸ O₁)), hLK.trans hKdvd, ?_, ?_⟩
  · intro hL
    have hLle : Nat.card (CFSG.layer (↥H₁ ⧸ O₁)) ≤ Nat.card KK := Nat.le_of_dvd Nat.card_pos hLK
    have hKle : Nat.card KK ≤ Nat.card Y₁ := Nat.le_of_dvd Nat.card_pos hKdvd
    have hKeq : Nat.card (KK.map θ₁) = Nat.card KK := by
      rw [← hlayer]
      omega
    have hinj := s39d_inj_of_card θ₁ KK hKeq
    have hKY' : KK = (bar d.D Y₁).subgroupOf H₁ :=
      Subgroup.eq_of_le_of_card_ge hKY (by rw [hcardsub]; omega)
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxY, hxO⟩ := Subgroup.mem_inf.1 hx
    have hxH : x ∈ H₁ := hbarH hxY
    have hxK : (⟨x, hxH⟩ : ↥H₁) ∈ KK := by rw [hKY']; exact hxY
    have hxO₁ : (⟨x, hxH⟩ : ↥H₁) ∈ O₁ := s39d_oddCore_le H₁ hxO
    have h1 : (⟨x, hxH⟩ : ↥H₁) = 1 := hinj _ hxK ((QuotientGroup.eq_one_iff _).2 hxO₁)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  · rcases htypes with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨g, hg, h1⟩ | ⟨g, hg, h1⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨g, hg, Or.inl h1⟩)
    · exact Or.inr (Or.inr ⟨g, hg, Or.inr h1⟩)

end S3dLayer2

section S3dMain

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39d_card_map_of_inf_bot {X : Type*} [Group X] [Finite X] (O : Subgroup X) [O.Normal]
    (Y : Subgroup X) (hY : Y ⊓ O = ⊥) : Nat.card (Y.map (QuotientGroup.mk' O)) = Nat.card Y := by
  have hinj : Function.Injective ((QuotientGroup.mk' O).comp Y.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : X) ∈ O := (QuotientGroup.eq_one_iff _).1 hx
    have : (x : X) ∈ Y ⊓ O := ⟨x.2, hxO⟩
    rw [hY, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hr : ((QuotientGroup.mk' O).comp Y.subtype).range = Y.map (QuotientGroup.mk' O) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem s39d_bar_Y₁_le (hp : d.CaseHyp) :
    bar d.D (normalClosureIn (s39dC₁ d) d.N₁) ≤
      normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) := by
  set NC : Subgroup (Bar d.D) :=
    normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D)) with hNC
  have hY : normalClosureIn (s39dC₁ d) d.N₁ ≤ lift NC := by
    refine normalClosureIn_le ?_ ?_
    · intro n hn
      have hnN : n ∈ normalizer (d.D : Set G) := (s39d_N₁_le_C₁ hp hn).1
      refine mem_lift_iff.2 ⟨hnN, subset_normalClosure ?_⟩
      exact s39d_mem_bar.2 ⟨⟨n, hnN⟩, hn, rfl⟩
    · intro c hc
      refine mem_normalizer_fintype fun x hx => ?_
      obtain ⟨hxN, hxK⟩ := mem_lift_iff.1 hx
      have hcN : c ∈ normalizer (d.D : Set G) := hc.1
      have hmem : c * x * c⁻¹ ∈ normalizer (d.D : Set G) :=
        mul_mem (mul_mem hcN hxN) (inv_mem hcN)
      refine mem_lift_iff.2 ⟨hmem, ?_⟩
      have e : proj d.D ⟨c * x * c⁻¹, hmem⟩ =
          proj d.D ⟨c, hcN⟩ * proj d.D ⟨x, hxN⟩ * (proj d.D ⟨c, hcN⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact (normalClosure_normal : NC.Normal).conj_mem _ hxK _
  calc bar d.D (normalClosureIn (s39dC₁ d) d.N₁) ≤ bar d.D (lift NC) := bar_mono hY
    _ = NC := bar_lift NC

theorem s39d_main (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e) (hi : d.Sec39Input)
    (ho : d.Sec39Outcome)
    (hM₁ : Nat.card d.M₁ = (2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1)) ^ 2 ∨
      Nat.card d.M₁ = (2 ^ (2 * f)) ^ 2 * (((2 ^ (2 * f)) ^ 2) ^ 2 - 1)) : d.Sec39Reduced := by
  have hf2 : 2 ≤ f := hp.hyp.two_le
  have hn : 2 ≤ 2 * f := by omega
  obtain ⟨L, hLY, hLeq, hLtype⟩ := s39d_H₁_layer hp k he hi
  set Y₁ := normalClosureIn (s39dC₁ d) d.N₁ with hY₁
  have hYM : Nat.card Y₁ ∣ Nat.card d.M₁ := Subgroup.card_dvd_of_le (s39d_Y₁_le_M₁ d)
  have hLM : L ∣ Nat.card d.M₁ := hLY.trans hYM
  have hmix := s39d_ar_mix hf2
  have hLeqM : L = Nat.card d.M₁ := by
    rcases hLtype with hL | hL | ⟨g, hg, hLg⟩
    · rcases hM₁ with hm | hm
      · rw [hL, hm]
      · rw [hL, hm] at hLM
        exact absurd hLM hmix.1
    · rcases hM₁ with hm | hm
      · rw [hL, hm] at hLM
        exact absurd hLM hmix.2
      · rw [hL, hm]
    · exact absurd hLM (s39d_ar_UL_pow hf2 hg hLg hM₁)
  have hMY : Y₁ = d.M₁ := by
    refine Subgroup.eq_of_le_of_card_ge (s39d_Y₁_le_M₁ d) ?_
    have : L ≤ Nat.card Y₁ := Nat.le_of_dvd Nat.card_pos hLY
    omega
  have hLY' : L = Nat.card Y₁ := by rw [hMY]; exact hLeqM
  have hinj := hLeq hLY'
  have hYN : Y₁ ≤ normalizer (d.D : Set G) := (s39d_Y₁_le_C₁ d).trans inf_le_left
  have hcardbar : Nat.card (bar d.D Y₁) = Nat.card Y₁ := s39d_card_bar hYN (s39d_Y₁_inf_D he)
  obtain ⟨ht, hLOH, hOTH⟩ := ho
  obtain ⟨-, -, -, hnc, -, -, -⟩ := hOTH
  obtain ⟨kf, _, _, hkf, ⟨φ⟩⟩ := hi.field
  obtain ⟨⟨eT⟩, -, -, -⟩ := s39c_std_quotient hn hkf φ hi.order_two hi.centralizes hi.normal
    hi.rank
  have htypes := s39d_outcome_types hf2 hkf eT hLOH
  have hle : (bar d.D Y₁).map (QuotientGroup.mk' (OD d)) ≤ CFSG.layer (Bar d.D ⧸ OD d) := by
    rw [← hnc]
    have h2 : (normalClosure ((bar d.D d.N₁ : Subgroup (Bar d.D)) : Set (Bar d.D))).map
        (QuotientGroup.mk' (OD d)) =
        normalClosure ((AbarD d : Subgroup (Bar d.D ⧸ OD d)) : Set (Bar d.D ⧸ OD d)) := by
      rw [Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), Subgroup.coe_map]
    rw [← h2]
    exact Subgroup.map_mono (s39d_bar_Y₁_le hp)
  have hcardθ : Nat.card ((bar d.D Y₁).map (QuotientGroup.mk' (OD d))) = Nat.card d.M₁ := by
    rw [s39d_card_map_of_inf_bot _ _ hinj, hcardbar, hMY]
  have hdvd : Nat.card d.M₁ ∣ Nat.card (CFSG.layer (Bar d.D ⧸ OD d)) := by
    rw [← hcardθ]
    exact Subgroup.card_dvd_of_le hle
  have hM₁le : d.M₁ ≤ normalizer (d.D : Set G) := by rw [← hMY]; exact hYN
  have hmap : ∀ hc : Nat.card d.M₁ = Nat.card (CFSG.layer (Bar d.D ⧸ OD d)),
      (bar d.D d.M₁).map (QuotientGroup.mk' (OD d)) = CFSG.layer (Bar d.D ⧸ OD d) := by
    intro hc
    rw [← hMY]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardθ, hc])
  rcases htypes with ⟨hA, hΛ⟩ | ⟨hB, hΛ⟩ | ⟨g, hg, hΛ⟩ | ⟨g, hg, hΛ⟩
  · have hc : Nat.card d.M₁ = Nat.card (CFSG.layer (Bar d.D ⧸ OD d)) := by
      rcases hM₁ with hm | hm
      · rw [hm, hΛ]
      · rw [hm, hΛ] at hdvd
        exact absurd hdvd hmix.2
    exact ⟨Or.inl hA, hM₁le, hmap hc⟩
  · have hc : Nat.card d.M₁ = Nat.card (CFSG.layer (Bar d.D ⧸ OD d)) := by
      rcases hM₁ with hm | hm
      · rw [hm, hΛ] at hdvd
        exact absurd hdvd hmix.1
      · rw [hm, hΛ]
    exact ⟨Or.inr hB, hM₁le, hmap hc⟩
  · exact absurd hdvd (s39d_ar_UL_dvd hf2 (Or.inl hΛ) hM₁)
  · exact absurd hdvd (s39d_ar_UL_dvd hf2 (Or.inr hΛ) hM₁)

end S3dMain

end Data

section Certified

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s39d_M₁_card (hp : d.CaseHyp) :
    Nat.card d.M₁ = (2 ^ (2 * f) * ((2 ^ (2 * f)) ^ 2 - 1)) ^ 2 ∨
      Nat.card d.M₁ = (2 ^ (2 * f)) ^ 2 * (((2 ^ (2 * f)) ^ 2) ^ 2 - 1) := by
  rcases (hp.hyp.sec3_5_three_iso_all hp.gms hp.gmsL).or with
    ⟨k, _, _, hk, ψ, -, -, -⟩ | ⟨k₂, _, _, hk₂, ψ, -, -⟩
  · left
    have hk' : Fintype.card k = 2 ^ (2 * f) := by rw [hk, ← pow_mul]; ring_nf
    rw [Nat.card_congr ψ.toEquiv, Nat.card_prod, GMSK.Sporadic.card_sl2 hk']
    ring
  · right
    have hk' : Fintype.card k₂ = 2 ^ (2 * (2 * f)) := by
      rw [hk₂, ← pow_mul, ← pow_mul]; ring_nf
    rw [Nat.card_congr ψ.toEquiv, GMSK.Sporadic.card_sl2 hk', ← pow_mul]
    ring_nf

theorem sec39_reduced (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e)
    (hi : d.Sec39Input) (hnn : d.Sec39NotNormal) (ho : d.Sec39Outcome) : d.Sec39Reduced :=
  s39d_main hp k he hi ho (s39d_M₁_card hp)

end Data

namespace CaseBParts

theorem sec39Reduced : Sec39ReducedStatement :=
  fun _ _ _ _ _ _ _ _ hp k he hi hnn ho => Data.sec39_reduced hp k he hi hnn ho

end CaseBParts

end Certified

end CFSG.LocalAnalysis.EvenBN.U5
