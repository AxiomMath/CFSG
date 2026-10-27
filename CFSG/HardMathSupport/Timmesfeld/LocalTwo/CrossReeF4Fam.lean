module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicReeG2
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.RankThree.PartOne.K128.ReeShape

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

section ReeF4

@[expose] def ReeF4InnerPlaneBalance : Prop :=
  ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], 1 ≤ a →
    Nat.card K = 2 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 5 < p →
      p ∣ (2 ^ (2 * a + 1)) ^ 4 - 1 → InnerPlaneBalance p (ReeTag.F4.reeGamma K a)

theorem innerPlaneBalance_reeGamma_F4_of_not_dvd {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hnd : ¬ p ∣ (2 ^ (2 * a + 1)) ^ 4 - 1) :
    InnerPlaneBalance p (ReeTag.F4.reeGamma K a) := by
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hQ1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hfac : (2 ^ (2 * a + 1)) ^ 4 - 1 =
      (2 ^ (2 * a + 1) - 1) * (2 ^ (2 * a + 1) + 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    have h4 : 1 ≤ (2 ^ (2 * a + 1)) ^ 4 := Nat.one_le_pow _ _ hQ1
    zify [hQ1, h4]
    ring
  have h1 : ¬ p ∣ 2 ^ (2 * a + 1) - 1 := fun h => hnd (by
    rw [hfac]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have h2 : ¬ p ∣ 2 ^ (2 * a + 1) + 1 := fun h => hnd (by
    rw [hfac]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
  have h4 : ¬ p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := fun h => hnd (by
    rw [hfac]
    exact dvd_mul_of_dvd_right h _)
  have hpQ : ¬ p ∣ 2 ^ (2 * a + 1) := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hsq : (2 ^ (2 * a + 1)) ^ 2 - 1 ∣ (2 ^ (2 * a + 1)) ^ 4 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow ((2 ^ (2 * a + 1)) ^ 2) 1 2
    rwa [one_pow, ← pow_mul (2 ^ (2 * a + 1)) 2 2] at h
  have hp5 : 5 ≤ p := five_le_of_not_dvd_sq_sub_one hp hp2 hpQ fun h => hnd (h.trans hsq)
  have hR : CFSG.LieType.SeitzGeneration.RankLE1 p (ReeTag.F4.reeGamma K a) := rankLE1_of_pRank hp fun hdvd => by
    rcases (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      a K hK).2 p hp (by omega) hdvd with h | h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h4
    · exact CFSG.RankThree.PartOne.K128.pRank_le_one_ree_phi6 hK hp hp5 h
    · exact CFSG.RankThree.PartOne.K128.pRank_le_one_ree_phi12 hK hp hp5 h
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  intro E hEin hE hEc H hH
  refine (CFSG.LieType.SeitzGeneration.false_of_inner_plane_of_no_plane hinj
    (fun F hF hFc => ?_) hE hEc hEin).elim
  have := hR F hF
  rw [hFc] at this
  have h2p := hp.two_le
  nlinarith

end ReeF4

section Cat

theorem isLocallyBalancedAbs_two_reeF4_cat_of_inner {m : ℕ}
    (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hin : ∀ (X : Type) [Field X] [Finite X] [CharP X ReeTag.F4.prime],
      Nat.card X = 2 ^ (2 * m + 1) → InnerPlaneBalance p (ReeTag.F4.reeGamma X m)) :
    IsLocallyBalancedAbs p 2 (CatT ⟨.reeF4 m, hv⟩) := by
  obtain ⟨X, _, _, _, hm1, hX, -, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_reeGamma_F4_of_inner hm1 hX hp (by omega) (hin X hX))

theorem crossCharTwoFamCat_reeF4_of_inner (h : ReeF4InnerPlaneBalance) :
    CrossCharTwoFamCat .reeF4 := by
  rintro ⟨d, hv⟩ ⟨m, rfl⟩ p hp hp5 _ _
  refine isLocallyBalancedAbs_two_reeF4_cat_of_inner hv hp hp5 fun X _ _ _ hX => ?_
  have hm1 : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  by_cases hdvd : p ∣ (2 ^ (2 * m + 1)) ^ 4 - 1
  · exact h m X hm1 hX p hp hp5 hdvd
  · exact innerPlaneBalance_reeGamma_F4_of_not_dvd hX hp (by omega) hdvd

end Cat

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
