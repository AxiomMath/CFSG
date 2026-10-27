module

public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4

private theorem orderA_two_eq (q : ℕ) :
    orderA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  have h : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  simp [orderA, h, Finset.prod_pair]

private theorem ordTwistedA_two_eq {q : ℕ} (hq : 1 ≤ q) :
    ordTwistedA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  have h : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  have h2 : (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h1]
      ring
    rw [this, Int.toNat_natCast]
  have h3 : (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  rw [ordTwistedA, h, Finset.prod_pair (by norm_num), h2, h3]

private theorem orderA_two_gt_720 {q : ℕ} (hq : 4 ≤ q) : 720 < orderA 2 q := by
  rw [orderA_two_eq]
  set X := q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) with hX
  have hgpos : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hgle : Nat.gcd 3 (q - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hdiv : X / 3 ≤ X / Nat.gcd 3 (q - 1) := Nat.div_le_div_left hgle hgpos
  have h1 : 64 ≤ q ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 15 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have h3 : 63 ≤ q ^ 3 - 1 := by omega
  have hXlow : 60480 ≤ X := by
    calc 60480 = 64 * (15 * 63) := by norm_num
      _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  have hmain : 2163 ≤ X / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    omega
  have : 721 ≤ X / Nat.gcd 3 (q - 1) :=
    le_trans (by norm_num : 721 ≤ 2163) (hmain.trans hdiv)
  omega

private theorem ordTwistedA_two_gt_720 {q : ℕ} (hq : 4 ≤ q) : 720 < ordTwistedA 2 q := by
  rw [ordTwistedA_two_eq (by omega)]
  set X := q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) with hX
  have hgpos : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hgle : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hdiv : X / 3 ≤ X / Nat.gcd 3 (q + 1) := Nat.div_le_div_left hgle hgpos
  have h1 : 64 ≤ q ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 15 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have h3 : 65 ≤ q ^ 3 + 1 := by omega
  have hXlow : 62400 ≤ X := by
    calc 62400 = 64 * (15 * 65) := by norm_num
      _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  have hmain : 2163 ≤ X / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    omega
  have : 721 ≤ X / Nat.gcd 3 (q + 1) :=
    le_trans (by norm_num : 721 ≤ 2163) (hmain.trans hdiv)
  omega

theorem k1419ClsSympCard {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hc : catalogIs X l3u3Index) : 720 < Nat.card X := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hc
  cases i with
  | cyclic _ _ => simp [l3u3Index, onLie] at hi
  | alternating _ _ => simp [l3u3Index, onLie] at hi
  | sporadic _ => simp [l3u3Index, onLie] at hi
  | lie d =>
    obtain ⟨ld, hv⟩ := d
    cases ld with
    | A r q =>
      by_cases hr : r = 2
      · subst hr
        obtain ⟨hp2, -⟩ :
            q.p = 2 ∧ (q.exponent % 6 = 2 ∨ q.exponent % 6 = 4) := hi
        have hcard : Nat.card X =
            Nat.card (TauCeti.ValidLieTypeIndex.Group
              ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩) := Nat.card_congr e.toEquiv
        have hvalid := hv
        rw [TauCeti.LieTypeIndex.valid_iff] at hvalid
        have hdup := hvalid.2
        have hcardne : q.card ≠ 2 := by
          intro hc2
          exact hdup (by
            rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
            exact Or.inr (Or.inl ⟨rfl, hc2⟩))
        have hcardeq : q.card = 2 ^ q.exponent := by
          rw [TauCeti.PrimePower.card_def, hp2]
        have hexp : 0 < q.exponent := q.exponent_pos
        have he2 : 2 ≤ q.exponent := by
          rcases Nat.lt_or_ge q.exponent 2 with hlt | hge
          · have he1 : q.exponent = 1 := by omega
            exfalso
            exact hcardne (by rw [hcardeq, he1]; norm_num)
          · exact hge
        have hq4' : 4 ≤ 2 ^ q.exponent := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) he2
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        have hK : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
          rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp2]
        have hPSL : Nat.card X =
            Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (2 + 1))
              (GaloisField q.p q.exponent)) := by
          rw [hcard]
          exact Nat.card_congr
            (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).toEquiv
        have hord : Nat.card X = orderA 2 (Nat.card (GaloisField q.p q.exponent)) := by
          rw [hPSL, CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear_eq_orderA
            (GaloisField q.p q.exponent) 2]
        rw [hord, hK]
        exact orderA_two_gt_720 hq4'
      · simp [l3u3Index, onLie, hr] at hi
    | twistedA r q =>
      by_cases hr : r = 2
      · subst hr
        obtain ⟨hp2, -⟩ :
            q.p = 2 ∧ (q.exponent % 6 = 1 ∨ q.exponent % 6 = 5) := hi
        have hvalid := hv
        rw [TauCeti.LieTypeIndex.valid_iff] at hvalid
        have h3le : 3 ≤ q.card :=
          ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvalid.1).2 rfl
        have hcardeq : q.card = 2 ^ q.exponent := by
          rw [TauCeti.PrimePower.card_def, hp2]
        have hexp : 0 < q.exponent := q.exponent_pos
        have he2 : 2 ≤ q.exponent := by
          rcases Nat.lt_or_ge q.exponent 2 with hlt | hge
          · have he1 : q.exponent = 1 := by omega
            exfalso
            rw [hcardeq, he1] at h3le
            norm_num at h3le
          · exact hge
        have hq4' : 4 ≤ 2 ^ q.exponent := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) he2
        haveI : Fact q.p.Prime := ⟨q.prime_p⟩
        have hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 q.exponent := by
          rw [← hp2]
          exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
        have hord : Nat.card X = ordTwistedA 2 (2 ^ q.exponent) := by
          have := (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.1 rfl
          simpa using this
        rw [hord]
        exact ordTwistedA_two_gt_720 hq4'
      · simp [l3u3Index, onLie, hr] at hi
    | _ => simp [l3u3Index, onLie] at hi

end CFSG.LocalAnalysis.GLTheoremA.K1419
