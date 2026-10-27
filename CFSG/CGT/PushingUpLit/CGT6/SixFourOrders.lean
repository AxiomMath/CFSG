module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourIdent
public import CFSG.LocalAnalysis.ComponentInitial.SER1CatalogModels
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS6
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedLieTag)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eight_sl_not_sz {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal]
    (h : EightCtx Y T R) {n : ℕ} (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n)
    (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification) {a : ℕ}
    (hsz : CFSG.Blueprint.LieModel
      (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) .twistedB2 0 2 (2 * a + 1)) :
    False := by
  have hdvd := eight_sl_card_dvd h hn hnat hS h215 hL
  obtain ⟨-, K', hK'f, hK'fin, hK'c, ⟨e⟩⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.lieModel_twistedB2_iff _ a).mp hsz
  have hcard : Nat.card (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK'c]
  rw [hcard] at hdvd
  have h3n : 3 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    have : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    have h4 : 4 ^ n % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have hpos : 0 < 4 ^ n := by positivity
    omega
  have h3 := h3n.trans hdvd
  have hq3 : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hpos : 0 < 2 ^ (2 * a + 1) := by positivity
  have hp3 : Nat.Prime 3 := Nat.prime_three
  rcases (Nat.Prime.dvd_mul hp3).mp h3 with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp3).mp h1 with h2 | h2
    · have := hp3.dvd_of_dvd_pow h2
      omega
    · omega
  · have hmod : ((2 ^ (2 * a + 1)) ^ 2 + 1) % 3 = 2 := by
      rw [Nat.add_mod, Nat.pow_mod, hq3]
    omega

section Sporadic


theorem card_nativeM23 : Nat.card CFSG.Blueprint.NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans
    CFSG.M23.M23Group.card_M23

theorem eight_sl_not_m2j {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n)
    (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hM : CFSG.Blueprint.NativeSporadic.IsSporadic
        (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic
        (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic
        (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) .M24) : False := by
  have hdvd := eight_sl_card_dvd h hn hnat hS h215 hL
  obtain ⟨hn2, -, -, hstd, hcardTh, -⟩ := eight_sl_ident h hn hnat hS h215 hL
  have h16 := hstd.card_sporadic hM
  have hn4 : n = 4 := by
    have : 2 ^ n = 2 ^ 4 := by rw [← hcardTh, h16]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  subst hn4
  have h17 : 17 ∣ 2 ^ 4 * ((2 ^ 4) ^ 2 - 1) := by norm_num
  have h17' := h17.trans hdvd
  have hc22 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  have hc23 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M23) = 10200960 := card_nativeM23
  have hc24 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 244823040 :=
    CFSG.Sporadic.Mathieu.card_M24
  rcases hM with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, hc22] at h17'
    norm_num at h17'
  · rw [Nat.card_congr e.toEquiv, hc23] at h17'
    norm_num at h17'
  · rw [Nat.card_congr e.toEquiv, hc24] at h17'
    norm_num at h17'

end Sporadic

end CFSG.CGT.PushingUpLit.CGT6
