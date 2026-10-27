module

public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedAPI
public import CFSG.GroupTheory.WeirSylow.Arith
import CFSG.GroupTheory.WeirSylow.GL
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSigma
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.Open

private theorem one_le_padicValNat_pow_orderOf_sub_one {p : ℕ} [Fact p.Prime] {q : ℕ}
    (hq : 1 < q) (hpq : ¬ p ∣ q) :
    1 ≤ padicValNat p (q ^ orderOf (q : ZMod p) - 1) := by
  have he : 0 < orderOf (q : ZMod p) := by
    rw [← ordMod_natCast]
    exact ordMod_pos (c := (q : ℤ)) (by exact_mod_cast hpq)
  refine one_le_padicValNat_of_dvd ?_ ?_
  · have h1 : 1 < q ^ orderOf (q : ZMod p) := Nat.one_lt_pow he.ne' hq
    omega
  · have h1 : ((q : ZMod p) ^ orderOf (q : ZMod p)) = 1 := pow_orderOf_eq_one _
    have h2 : ((q ^ orderOf (q : ZMod p) - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, h1, Nat.cast_one,
        sub_self]
    exact (ZMod.natCast_eq_zero_iff _ p).1 h2

theorem pRank_top_gl_eq {p : ℕ} [Fact p.Prime] (hp : Odd p) {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] [Finite K] (hpK : ¬ p ∣ Nat.card K) :
    CFSG.Open.pRank p (⊤ : Subgroup (GL ι K)) =
      Fintype.card ι / orderOf (Nat.card K : ZMod p) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hpK' : ¬ p ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hGL : CFSG.Open.pRank p (⊤ : Subgroup (GL (Fin (Fintype.card ι)) K)) =
      Fintype.card ι / orderOf (Fintype.card K : ZMod p) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.RankChevProof.pRank_eq_of_sylow_sigmaModel (p := p)
      (e := orderOf (Fintype.card K : ZMod p))
      (a := padicValNat p (Fintype.card K ^ orderOf (Fintype.card K : ZMod p) - 1))
      (N := Fintype.card ι) (one_le_padicValNat_pow_orderOf_sub_one hq hpK')
      (fun P => sylow_GL hp K hpK' (Fintype.card ι) P)
  rw [Nat.card_eq_fintype_card, ← hGL]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt
    ((Fintype.equivFin ι).reindexGL K)

theorem pRank_top_statedProj_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {p d : ℕ} [Fact p.Prime] {H : Subgroup (GL ι K)} (hd : ¬ p ∣ d)
    (hsc : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ H → c ^ d = 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj H)) = CFSG.Open.pRank p (⊤ : Subgroup H) :=
  CFSG.SectionRank.pRank_quotient_eq _
    (CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf H (Fact.out) hd hsc)

theorem three_le_ordMod_of_not_dvd_sq_sub_one {p : ℕ} [Fact p.Prime] {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) (h : ¬ (p : ℤ) ∣ c ^ 2 - 1) : 3 ≤ ordMod p c := by
  have hpos := ordMod_pos hc
  by_contra hlt
  apply h
  rw [dvd_pow_sub_one_iff]
  have : ordMod p c = 1 ∨ ordMod p c = 2 := by omega
  rcases this with h1 | h1 <;> simp [h1]

theorem not_intCast_dvd_sq_sub_one_of_not_dvd {p q : ℕ} (h : ¬ p ∣ q ^ 2 - 1) :
    ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 - 1 := by
  intro hd
  apply h
  have hq : 1 ≤ q ^ 2 := by
    by_contra hq0
    have : q ^ 2 = 0 := by omega
    apply h
    simp [this]
  have : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub hq]; push_cast; ring
  exact_mod_cast (this ▸ hd)

private theorem not_dvd_card_sub_one_of_not_dvd_sq_sub_one {p m : ℕ} (h : ¬ p ∣ m ^ 2 - 1) :
    ¬ p ∣ m - 1 := fun hd => h (hd.trans (by simpa using Nat.sub_dvd_pow_sub_pow m 1 2))

theorem pRank_top_statedProj_le_card_div_three {p : ℕ} [Fact p.Prime] (hp : Odd p) {ι : Type}
    [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] (hpK : ¬ p ∣ Nat.card K)
    (hpK2 : ¬ p ∣ Nat.card K ^ 2 - 1) (H : Subgroup (GL ι K)) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj H)) ≤ Fintype.card ι / 3 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hd : ¬ p ∣ Nat.card K - 1 := not_dvd_card_sub_one_of_not_dvd_sq_sub_one hpK2
  rw [pRank_top_statedProj_eq hd fun c _ => by
    rw [← Nat.card_units]; exact pow_card_eq_one']
  have hle : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ CFSG.Open.pRank p (⊤ : Subgroup (GL ι K)) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp1 H.subtype H.subtype_injective
  rw [pRank_top_gl_eq hp hpK] at hle
  have he : 3 ≤ orderOf (Nat.card K : ZMod p) := by
    rw [← ordMod_natCast]
    exact three_le_ordMod_of_not_dvd_sq_sub_one (by exact_mod_cast hpK)
      (not_intCast_dvd_sq_sub_one_of_not_dvd hpK2)
  exact hle.trans (Nat.div_le_div_left he (by norm_num))

private theorem orderOf_natCast_eq_two_of_dvd_add_one {p q : ℕ} [Fact p.Prime] (hp : Odd p)
    (h : p ∣ q + 1) : orderOf (q : ZMod p) = 2 := by
  have h1 : (q : ZMod p) = -1 := by
    have := (ZMod.natCast_eq_zero_iff (q + 1) p).2 h
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hp2 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hp) even_two
  rw [h1]
  have := orderOf_neg_one (R := ZMod p)
  rwa [if_neg hp2] at this

theorem pow_eq_one_of_scalar_mem_statedSL {n : ℕ} {K : Type} [Field K] {c : Kˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSL n K) : c ^ n = 1 := by
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSL h
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  exact Units.ext (by simpa using hdet)

theorem pRank_top_statedSL_le {p : ℕ} [Fact p.Prime] (hp : Odd p) {K : Type} [Field K]
    [Finite K] (hpK : ¬ p ∣ Nat.card K) (n : ℕ) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedSL n K)) ≤ n / orderOf (Nat.card K : ZMod p) := by
  have h := CFSG.SectionRank.pRank_top_le_of_injective (p := p)
    (Fact.out : p.Prime).one_lt (StatedSL n K).subtype Subtype.val_injective
  rw [pRank_top_gl_eq hp hpK, Fintype.card_fin] at h
  exact h

theorem pRank_top_statedProj_statedSL_le_div_two {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hpn : ¬ p ∣ n) (h : p ∣ Nat.card K + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL n K))) ≤ n / 2 := by
  have hpK : ¬ p ∣ Nat.card K := fun hd => by
    have h1 := (Nat.dvd_add_right hd).1 h
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h1)
  rw [pRank_top_statedProj_eq hpn fun c hc => pow_eq_one_of_scalar_mem_statedSL hc]
  have := pRank_top_statedSL_le hp hpK n
  rwa [orderOf_natCast_eq_two_of_dvd_add_one hp h] at this

end CFSG.GroupTheory.WeirSylow
