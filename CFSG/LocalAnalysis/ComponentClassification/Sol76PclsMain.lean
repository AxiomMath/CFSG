module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsE7
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsSpin
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsUnitary
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsTwoE
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Id
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFinal

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.CentralExt

@[expose] def F42CoverInput : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
    LieModel (Q ⧸ center Q) .F4 0 2 1 → ∀ z ∈ center Q, orderOf z = 2 → 3 ≤ CFSG.pRank 2 Q

@[expose] def SporadicCoverRankInput (s : TauCeti.SporadicName) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → Nat.card (center Q) = 2 →
    NativeSporadic.IsSporadic (Q ⧸ center Q) s → 3 ≤ CFSG.pRank 2 Q

theorem not_two_dvd_prod {a b c d : ℕ} (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b) (hc : ¬ 2 ∣ c)
    (hd : ¬ 2 ∣ d) : ¬ 2 ∣ a * b * (c * d) := by
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h1 with h2 | h2
    · exact ha h2
    · exact hb h2
  · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h1 with h2 | h2
    · exact hc h2
    · exact hd h2

theorem exceptional_odd {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2) :
    ¬ 2 ∣ (exceptionalOrders t n p f).1 ∧ ¬ 2 ∣ (exceptionalOrders t n p f).2 := by
  unfold exceptionalOrders
  split <;> simp_all

theorem twelve_of_two_dvd {t : StatedLieTag} {n f : ℕ}
    (h : 2 ∣ (exceptionalOrders t n 2 f).1 ∨ 2 ∣ (exceptionalOrders t n 2 f).2) :
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) ∨
      (t = .PSU ∧ n = 4 ∧ f = 1) ∨ (t = .PSp ∧ n = 3 ∧ f = 1) ∨ (t = .G2 ∧ n = 0 ∧ f = 2) ∨
      (t = .F4 ∧ n = 0 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨
      (t = .PSU ∧ n = 6 ∧ f = 1) ∨ (t = .twistedB2 ∧ n = 0 ∧ f = 3) ∨
      (t = .twistedE6 ∧ n = 0 ∧ f = 1) ∨ (t = .PSL ∧ n = 3 ∧ f = 2) := by
  revert h
  unfold exceptionalOrders
  split <;> simp_all

theorem generic_odd_two {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) :
    ¬ 2 ∣ (genericOrders t n 2 f).1 ∧ ¬ 2 ∣ (genericOrders t n 2 f).2 := by
  refine ⟨Hq4.not_two_dvd_generic_fst hadm, ?_⟩
  have hev : Even (2 ^ f) := (Nat.even_pow' (by have := hadm.2.1; omega)).2 even_two
  cases t <;> simp [genericOrders, hev]

theorem ringChar_ne_two_of_card {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) : ringChar K ≠ 2 := by
  have := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  rw [ringChar.eq K p]
  exact hp2

variable {Q : Type} [Group Q] [Finite Q]

theorem symplectic_of_lieModel_odd
    (hrows : Hq4.NativeRowsExceptTwistedE6Two) (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    (hr : CFSG.pRank 2 Q = 2) {t : StatedLieTag} {n p f : ℕ}
    (hL : LieModel (Q ⧸ center Q) t n p f) (hp2 : p ≠ 2) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), ringChar k ≠ 2 ∧
      Nonempty (Q ⧸ center Q ≃* StatedProj (StatedSp 2 k)) := by
  have hadm := GriessNative.admissible_of_lieModel hL
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hodd : ¬ 2 ∣ (genericOrders t n p f).1 → ¬ 2 ∣ (genericOrders t n p f).2 →
      ∃ (k : Type) (_ : Field k) (_ : Finite k), ringChar k ≠ 2 ∧
        Nonempty (Q ⧸ center Q ≃* StatedProj (StatedSp 2 k)) := fun ha hb => by
    have hne : ¬ (t = .twistedE6 ∧ p ^ f = 2) := by
      rintro ⟨-, h⟩
      have hdvd : p ∣ 2 := h ▸ dvd_pow_self p (by omega)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    exfalso
    exact not_two_dvd_prod ha hb (exceptional_odd hp2).1 (exceptional_odd hp2).2
      (two_dvd_of_griessRow hQ (hrows _ t n p f hL hne) hzZ hz2)
  have g3 : ∀ a, ¬ 2 ∣ Nat.gcd 3 a := fun a h => by
    have := h.trans (Nat.gcd_dvd_left 3 a)
    omega
  cases t
  ·
    obtain ⟨⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := GriessNative.classical_of_lieModel hL (by decide)
    have hK2 := ringChar_ne_two_of_card hp hp2 hf hK
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
    · exact absurd (pRank_le_one_of_PSL_two hQ hO hzZ hz2 hK2 e) (by omega)
    · exact absurd (three_le_pRank_of_PSL hO hzZ hz2 hn3 hK2 e) (by omega)
  ·
    obtain ⟨⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := GriessNative.classical_of_lieModel hL (by decide)
    have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (k := f * 2) (by omega) (by rw [hK, pow_mul])
    exact absurd (three_le_pRank_of_PSU hO hzZ hz2 hn hK hp2 e) (by omega)
  ·
    obtain ⟨⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := GriessNative.classical_of_lieModel hL (by decide)
    have hK2 := ringChar_ne_two_of_card hp hp2 hf hK
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
    · exact ⟨K, inferInstance, inferInstance, hK2, ⟨e⟩⟩
    · exact absurd (three_le_pRank_of_PSp hO hzZ hz2 hn3 hK2 e) (by omega)
  ·
    obtain ⟨⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := GriessNative.classical_of_lieModel hL (by decide)
    exact absurd (three_le_pRank_of_POmegaOdd hO hzZ hz2 hn
      (ringChar_ne_two_of_card hp hp2 hf hK) e) (by omega)
  ·
    obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := GriessNative.classical_of_lieModel hL (by decide)
    exact absurd (three_le_pRank_of_POmegaPlus hO hzZ hz2 (by omega)
      (ringChar_ne_two_of_card hp hp2 hf hK) e) (by omega)
  ·
    obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ :=
      GriessNative.classical_of_lieModel hL (by decide)
    exact absurd (three_le_pRank_of_POmegaMinus hO hzZ hz2 hn
      (ringChar_ne_two_of_card hp hp2 hf hK) hirr e) (by omega)
  · exact hodd (by simp [genericOrders]) (by simp [genericOrders])
  · exact hodd (by simp [genericOrders]) (by simp [genericOrders])
  · exact hodd (g3 _) (by simp [genericOrders])
  ·
    obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
    exact absurd (three_le_pRank_of_E7 hO hzZ hz2 (ringChar_ne_two_of_card hp hp2 hf hK) e)
      (by omega)
  · exact hodd (by simp [genericOrders]) (by simp [genericOrders])
  · exact hodd (g3 _) (by simp [genericOrders])
  · exact hodd (by simp [genericOrders]) (by simp [genericOrders])
  · exact absurd hadm.2.2.2.1 hp2
  · exact hodd (by simp [genericOrders]) (by simp [genericOrders])
  · exact absurd hadm.2.2.2.1 hp2
  · exact absurd hadm.2.2.2.1 hp2

theorem symplectic_of_lieModel_two
    (hrows : Hq4.NativeRowsExceptTwistedE6Two) (hF4 : F42CoverInput) (hQ : IsQuasisimple Q)
    (hO : pPrimeCore 2 Q = ⊥) (hr : CFSG.pRank 2 Q = 2) {t : StatedLieTag} {n f : ℕ}
    (hL : LieModel (Q ⧸ center Q) t n 2 f) {z : Q} (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), ringChar k ≠ 2 ∧
      Nonempty (Q ⧸ center Q ≃* StatedProj (StatedSp 2 k)) := by
  have hadm := GriessNative.admissible_of_lieModel hL
  by_cases hE6 : t = .twistedE6 ∧ 2 ^ f = 2
  · obtain ⟨rfl, h2⟩ := hE6
    obtain rfl : f = 1 := Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 1 by rw [h2, pow_one])
    obtain ⟨rfl, -⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
    exact absurd (three_le_pRank_of_twistedE6Two hO hL hzZ hz2) (by omega)
  have hrow := hrows _ t n 2 f hL hE6
  obtain ⟨ha, hb⟩ := generic_odd_two hadm
  have hexc : 2 ∣ (exceptionalOrders t n 2 f).1 ∨ 2 ∣ (exceptionalOrders t n 2 f).2 := by
    by_contra h
    push Not at h
    exact not_two_dvd_prod ha hb h.1 h.2 (two_dvd_of_griessRow hQ hrow hzZ hz2)
  rcases twelve_of_two_dvd hexc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact absurd (pRank_le_one_of_L24 hQ hO hL hzZ hz2) (by omega)
  · exact absurd (pRank_le_one_of_L32 hQ hO hL hzZ hz2) (by omega)
  · exact absurd (four_le_pRank_of_L42 hL hzZ hz2) (by omega)
  · exact exists_sp4_of_U42 hL
  · exact absurd (four_le_pRank_of_Sp62 hL hzZ hz2) (by omega)
  · exact absurd (five_le_pRank_of_G24 hQ hL hrow hzZ hz2) (by omega)
  · exact absurd (hF4 Q hQ hO hL z hzZ hz2) (by omega)
  · exact absurd (three_le_pRank_of_O82 hQ hL hrow hzZ hz2) (by omega)
  · exact absurd (three_le_pRank_of_U62 hQ hO hL) (by omega)
  · exact absurd (four_le_pRank_of_Sz8 hL hzZ hz2) (by omega)
  · exact absurd ⟨rfl, rfl⟩ hE6
  · exact absurd (three_le_pRank_of_L34 hL hzZ hz2) (by omega)

theorem three_le_pRank_of_sporadic
    (hres : SporadicCoverRankInput .M12 ∧ SporadicCoverRankInput .J2 ∧ SporadicCoverRankInput .Co1 ∧
        SporadicCoverRankInput .Fi22 ∧ SporadicCoverRankInput .Suz ∧ SporadicCoverRankInput
        .B) (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    (hS : NativeSporadic.SporadicRep (Q ⧸ center Q)) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : 3 ≤ CFSG.pRank 2 Q := by
  obtain ⟨s, ⟨e⟩⟩ := hS
  have hQ' := ((Foundations.SteinbergCA.quasisimple_iff Q).2.2.1).mp hQ
  obtain ⟨hdvd, -⟩ := EvenSporadicStandard.centralTwoBound Q hQ'
    (isPGroup_center_of_pPrimeCore_eq_bot hO) s ⟨e⟩
  have h2 : 2 ∣ Nat.card (center Q) := by
    rw [← hz2, ← Subgroup.orderOf_mk z hzZ]
    exact orderOf_dvd_natCard _
  have h2s := h2.trans hdvd
  obtain ⟨hM12, hJ2, hCo1, hFi22, hSuz, hB⟩ := hres
  cases s
  case M12 => exact hM12 Q hQ (Nat.dvd_antisymm hdvd h2) ⟨e⟩
  case M22 => exact le_trans (by norm_num) (four_le_pRank_of_m22 e hzZ hz2)
  case J2 => exact hJ2 Q hQ (Nat.dvd_antisymm hdvd h2) ⟨e⟩
  case HS => exact le_trans (by norm_num) (four_le_pRank_of_hs e hzZ hz2)
  case Ru => exact le_trans (by norm_num) (four_le_pRank_of_ru e hzZ hz2)
  case Suz => exact hSuz Q hQ (Nat.dvd_antisymm hdvd h2) ⟨e⟩
  case Co1 => exact hCo1 Q hQ (Nat.dvd_antisymm hdvd h2) ⟨e⟩
  case Fi22 => exact hFi22 Q hQ (Nat.dvd_antisymm hdvd h2) ⟨e⟩
  case B => exact hB Q hQ (Nat.dvd_antisymm hdvd h2) ⟨e⟩
  all_goals exact absurd h2s (by simp [EvenSporadicStandard.twoPartBound])

theorem quasisimpleRankTwoSymplecticInput_of_residue
    (hF4 : F42CoverInput) (hres : SporadicCoverRankInput .M12 ∧ SporadicCoverRankInput .J2 ∧
        SporadicCoverRankInput .Co1 ∧ SporadicCoverRankInput .Fi22 ∧ SporadicCoverRankInput .Suz ∧
        SporadicCoverRankInput .B) : QuasisimpleRankTwoSymplecticInput := by
  intro Q _ _ hQ hO hcat hr ⟨z, hzZ, hz2⟩
  have hrows := Hq4.nativeRowsExceptTwistedE6Two
  rcases Hq4.catalog_cases_lieModel hcat with ⟨q, -, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨t, n, p, f, hL⟩ | hS
  · exfalso
    obtain ⟨a, b, hab⟩ := hQ.2.2
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exfalso
    rcases (by omega : m = 5 ∨ m = 6 ∨ m = 7 ∨ 8 ≤ m) with rfl | rfl | rfl | h8
    · have := pRank_le_one_of_alternating_five hQ hO e hzZ hz2
      omega
    · have := pRank_le_one_of_alternating_small hQ hO le_rfl (by norm_num) e hzZ hz2
      omega
    · have := pRank_le_one_of_alternating_small hQ hO (by norm_num) le_rfl e hzZ hz2
      omega
    · have := four_le_pRank_of_alternating h8 e hzZ hz2
      omega
  · by_cases hp2 : p = 2
    · subst hp2
      exact symplectic_of_lieModel_two hrows hF4 hQ hO hr hL hzZ hz2
    · exact symplectic_of_lieModel_odd hrows hQ hO hr hL hp2 hzZ hz2
  · exfalso
    have := three_le_pRank_of_sporadic hres hQ hO hS hzZ hz2
    omega

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
