module

public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed

theorem gcd_four_pow_sub_one_of_mod_four_eq_one {q : ℕ} (hq : q % 4 = 1) (m : ℕ) :
    Nat.gcd 4 (q ^ m - 1) = 4 := by
  have h : q ^ m % 4 = 1 := by
    simp [Nat.pow_mod, hq]
  have hpos : 1 ≤ q ^ m := Nat.one_le_iff_ne_zero.2 fun h0 => by rw [h0] at h; simp at h
  exact Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by omega))

theorem gcd_four_pow_sub_one_of_mod_four_eq_three {q : ℕ} (hq : q % 4 = 3) {m : ℕ} (hm : Odd m) :
    Nat.gcd 4 (q ^ m - 1) = 2 := by
  obtain ⟨k, rfl⟩ := hm
  have h : q ^ (2 * k + 1) % 4 = 3 := by
    rw [Nat.pow_mod, hq, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hpos : 1 ≤ q ^ (2 * k + 1) := Nat.one_le_iff_ne_zero.2 fun h0 => by rw [h0] at h; simp at h
  rw [Nat.gcd_rec, show (q ^ (2 * k + 1) - 1) % 4 = 2 by omega]
  norm_num

variable {n : ℕ} {K : Type} [Field K]

theorem nonempty_scalarSpin_mulEquiv_generic [Finite K] {p f : ℕ} (hn : 3 ≤ n)
    (hK : Nat.card K = p ^ f) :
    Nonempty (scalarSpin n K ≃* generic .POmegaPlus n p f) := by
  suffices h : ∃ a b : ℕ, genericOrders .POmegaPlus n p f = (a, b) ∧
      Nonempty (scalarSpin n K ≃* Multiplicative (ZMod a) × Multiplicative (ZMod b)) by
    obtain ⟨a, b, hab, ⟨e⟩⟩ := h
    have h1 : a = (genericOrders .POmegaPlus n p f).1 := by rw [hab]
    have h2 : b = (genericOrders .POmegaPlus n p f).2 := by rw [hab]
    exact ⟨e.trans (MulEquiv.prodCongr
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr h1).toAddEquiv)
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr h2).toAddEquiv))⟩
  by_cases hq : Even (Nat.card K)
  · refine ⟨1, 1, ?_, ?_⟩
    · simp only [genericOrders]
      exact ite_eq_left (by rw [← hK]; exact hq)
    have hbot := comap_statedScalars_quadPlus_eq_bot (K := K) hn (SpinTorus.two_eq_zero_iff_even_card.2 hq)
    have : Unique (scalarSpin n K) := by
      rw [hbot]
      infer_instance
    let _ : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) := Unique.mk' _
    exact ⟨MulEquiv.ofUnique⟩
  have h2 : (2 : K) ≠ 0 := fun h => hq (SpinTorus.two_eq_zero_iff_even_card.1 h)
  by_cases he : Even n
  · refine ⟨2, 2, ?_, ?_⟩
    · simp only [genericOrders]
      rw [ite_eq_right (by rw [← hK]; exact hq), ite_eq_left he]
    have := isKleinFour_scalarSpin (K := K) hn h2 he
    obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := scalarSpin n K)
      (G₂ := Multiplicative (ZMod 2 × ZMod 2))
    exact ⟨e.trans (MulEquiv.prodMultiplicative _ _)⟩
  refine ⟨Nat.gcd 4 (Nat.card K ^ n - 1), 1, ?_, ?_⟩
  · simp only [genericOrders]
    rw [ite_eq_right (by rw [← hK]; exact hq), ite_eq_right he, hK]
  have : Fintype K := Fintype.ofFinite K
  have ho : Odd n := Nat.not_even_iff_odd.1 he
  have hcyc_card : IsCyclic (scalarSpin n K) ∧
      Nat.card (scalarSpin n K) = Nat.gcd 4 (Nat.card K ^ n - 1) := by
    by_cases hsq : IsSquare (-1 : K)
    · obtain ⟨r, hr⟩ := hsq
      have hr0 : r ≠ 0 := fun h => by rw [h, mul_zero] at hr; exact one_ne_zero (neg_eq_zero.1 hr)
      have hι : Units.mk0 r hr0 ^ 2 = -1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, pow_two, ← hr, Units.val_neg, Units.val_one])
      obtain ⟨hc, hcyc⟩ := card_scalarSpin_of_isSquare (K := K) hn h2 ho hι
      have h4 : Nat.card K % 4 = 1 := by
        have := (FiniteField.isSquare_neg_one_iff (F := K)).1 ⟨r, hr⟩
        have hodd : Nat.card K % 2 = 1 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hq)
        rw [← Nat.card_eq_fintype_card] at this
        omega
      exact ⟨hcyc, by rw [hc, gcd_four_pow_sub_one_of_mod_four_eq_one h4]⟩
    · have hc := card_scalarSpin_of_not_isSquare (K := K) hn h2 ho hsq
      have h4 : Nat.card K % 4 = 3 := by
        have := mt (FiniteField.isSquare_neg_one_iff (F := K)).2 hsq
        rw [← Nat.card_eq_fintype_card] at this
        omega
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact ⟨isCyclic_of_prime_card hc, by rw [hc, gcd_four_pow_sub_one_of_mod_four_eq_three h4 ho]⟩
  obtain ⟨hcyc, hcard⟩ := hcyc_card
  exact ⟨((zmodCyclicMulEquiv hcyc).symm.trans
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard).toAddEquiv)).trans
      MulEquiv.prodUnique.symm⟩

theorem pomegaPlus_hopfMultiplier [Finite K] {p f : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = p ^ f)
    (hK4 : 4 ≤ Nat.card K) :
    commutator (StatedProj (StatedOmega (StatedQuadPlus n K))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadPlus n K))) ≃*
        generic .POmegaPlus n p f) := by
  set q := spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn)
  obtain ⟨hq, hkerZ, hker⟩ := spinToStatedProj_quadPlus (K := K) hn
  have : Group.IsPerfect (spinGroup (quadPlus n K)) := isPerfect_spinGroup_quadPlus hn
  have hperf : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
    Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedOmega (StatedQuadPlus n K))) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker.le
      fun π hπ hcen => spinPlus_exists_section_of_central hn hK4 hπ hcen)
  obtain ⟨e3⟩ := nonempty_scalarSpin_mulEquiv_generic (K := K) hn hK
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hkerZ).trans e3))⟩

end CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed
