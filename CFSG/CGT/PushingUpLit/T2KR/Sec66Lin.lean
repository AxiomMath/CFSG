module

public import CFSG.CGT.PushingUpLit.T2KR.Sec66Bound
public import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.CGT.PushingUpLit.A78.L3List
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.T2KR.PairStar

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedLieTag)
open MData (QM)

theorem two_pow_dvd_card_psl {K : Type} [Field K] [Finite K] {f m : ℕ}
    (hK : Nat.card K = 2 ^ f) (hm : 2 ≤ m) :
    2 ^ (f * (m * (m - 1) / 2)) ∣ Nat.card (StatedProj (StatedSL m K)) :=
  CFSG.CGT.PushingUpLit.A78.two_pow_dvd_card_psl' hK hm

theorem two_pow_le_card_of_isSylowOf {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {k : ℕ} (hk : 2 ^ k ∣ Nat.card G) :
    2 ^ k ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hT.card_eq
  rw [Subgroup.card_top] at h1
  rw [h1]
  exact Nat.pow_le_pow_right (by norm_num)
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hk)

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

theorem false_of_psl_ge3 (hE1 : FooteNonsolvableSimple) (hs : Sec6 G L M T n)
    (hQV : QOf L M = blockU L) {m f : ℕ} (hm : 3 ≤ m)
    (hmod : StatedClassicalModel G .PSL m 2 f)
    (hcardQ : Nat.card ↥(QOf L M) = 2 ^ (f * (m - 1))) : False := by
  classical
  set H := MData.ofSec6 hE1 hs with hH
  have hF : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n H.n_ne_zero
  have hQcard : Nat.card ↥(QOf L M) = (2 ^ n) ^ 2 := by
    rw [hQV, H.card_V, hF]
  have h1 : 2 ^ (f * (m - 1)) = 2 ^ (n * 2) := by
    rw [← hcardQ, hQcard, ← pow_mul]
  have h2 : f * (m - 1) = n * 2 := Nat.pow_right_injective (le_refl 2) h1
  by_cases hm4 : 4 ≤ m
  · have hT2 : IsPGroup 2 T := hs.sec4.sylowG.isPGroup
    have hTM : T ≤ M := hs.sec4.sylow.le
    have hrel : (QOf L M).relIndex T ≤ n * 2 ^ n := by
      have := H.relIndex_Q_le hTM hT2
      have e : T ⊓ QM L M = QOf L M := inf_eq_right.2 hs.Q_le_T
      rwa [e] at this
    have hTcard : (QOf L M).relIndex T * Nat.card ↥(QOf L M) = Nat.card T := by
      have := Subgroup.relIndex_mul_card (QOf L M) T
      rwa [inf_of_le_left hs.Q_le_T] at this
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    have hdvd : 2 ^ (f * (m * (m - 1) / 2)) ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv]
      exact two_pow_dvd_card_psl hK (by omega)
    have hle : 2 ^ (f * (m * (m - 1) / 2)) ≤ Nat.card T :=
      two_pow_le_card_of_isSylowOf hs.sec4.sylowG hdvd
    have hmn : f * (m * (m - 1) / 2) = m * n := by
      have hev : 2 ∣ m * (m - 1) := (Nat.even_mul_pred_self m).two_dvd
      have h3 : 2 * (m * (m - 1) / 2) = m * (m - 1) := Nat.mul_div_cancel' hev
      have h4 : 2 * (f * (m * (m - 1) / 2)) = 2 * (m * n) := by
        calc 2 * (f * (m * (m - 1) / 2)) = f * (2 * (m * (m - 1) / 2)) := by ring
          _ = f * (m * (m - 1)) := by rw [h3]
          _ = m * (f * (m - 1)) := by ring
          _ = m * (n * 2) := by rw [h2]
          _ = 2 * (m * n) := by ring
      omega
    rw [hmn] at hle
    have hlt : n < 2 ^ n := Nat.lt_two_pow_self
    have hup : Nat.card T ≤ n * 2 ^ (3 * n) := by
      rw [← hTcard, hQcard]
      calc (QOf L M).relIndex T * (2 ^ n) ^ 2 ≤ (n * 2 ^ n) * (2 ^ n) ^ 2 :=
            Nat.mul_le_mul_right _ hrel
        _ = n * 2 ^ (3 * n) := by
          rw [mul_assoc, ← pow_mul, ← pow_add]
          congr 2
          ring
    have h3n : 2 ^ (3 * n) * 2 ^ n = 2 ^ (4 * n) := by rw [← pow_add]; ring_nf
    have hmon : 2 ^ (4 * n) ≤ 2 ^ (m * n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right n hm4)
    have hpos : 0 < 2 ^ (3 * n) := by positivity
    have hlt2 : n * 2 ^ (3 * n) < 2 ^ n * 2 ^ (3 * n) := Nat.mul_lt_mul_of_pos_right hlt hpos
    rw [mul_comm (2 ^ n)] at hlt2
    omega
  · have hm3 : m = 3 := by omega
    subst hm3
    have hfn : f = n := by
      have : f * 2 = n * 2 := by simpa using h2
      omega
    subst hfn
    obtain ⟨e⟩ := projSL_of_statedClassicalModel hmod
    exact hs.sec4.noL3 ⟨e⟩

end CFSG.CGT.PushingUpLit.T2KR
