module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.OrderFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.CatArith
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOFamily
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicThree
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithAltSporSporadic

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open


theorem ordA_two_pow_gt (n : ℕ) (hn : 3 ≤ n) : 95040 < ordA 2 (2 ^ n) := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [ordA_two]
  have hd3 : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hdpos : 0 < Nat.gcd 3 (2 ^ n - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hnum : 16482816 ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
    have h1 : 512 ≤ (2 ^ n) ^ 3 := by
      calc 512 = 8 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h8 3
    have h2 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h8 2
      omega
    have h3 : 511 ≤ (2 ^ n) ^ 3 - 1 := by omega
    calc 16482816 = 512 * (63 * 511) := by norm_num
      _ ≤ _ := by
        have : 512 * (63 * 511) ≤
            (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
          gcongr
        omega
  calc 95040 < 16482816 / 3 := by norm_num
    _ ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) / 3 := Nat.div_le_div_right hnum
    _ ≤ _ := Nat.div_le_div_left hd3 hdpos

theorem ordG2_two_pow_gt (n : ℕ) (hn : 2 ≤ n) : 95040 < ordG2 (2 ^ n) := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  unfold ordG2
  have h6 : 4096 ≤ (2 ^ n) ^ 6 := by
    calc 4096 = 4 ^ 6 := by norm_num
      _ ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left h4 6
  have h2 : 15 ≤ (2 ^ n) ^ 2 - 1 := by
    have : 16 ≤ (2 ^ n) ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h4 2
    omega
  have h5 : 4095 ≤ (2 ^ n) ^ 6 - 1 := by omega
  calc 95040 < 4096 * 4095 * 15 := by norm_num
    _ ≤ (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) := by gcongr

theorem card_of_lieModel_g_two_two_pow {X : Type} [Group X] {n : ℕ}
    (h : LieModel X .G2 0 2 n) : Nat.card X = ordG2 (2 ^ n) := by
  rcases h with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem thm46_suz_gt (X : Type) [Group X] (h : IsSporadic X .Suz) : 95040 < Nat.card X := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card (Carrier .Suz) = 448345497600 := CFSG.Sporadic.Suz.card_Suz
  rw [Nat.card_congr e.toEquiv, hcard]
  norm_num

theorem two_pow_mul_dvd_ordA (n : ℕ) (hn : 1 ≤ n) : 2 ^ (3 * n) ∣ ordA 2 (2 ^ n) := by
  have h := pow_padicValNat_dvd (p := 2) (n := ordA 2 (2 ^ n))
  rwa [padicValNat_ordA hn] at h

theorem ne_of_dvd_check {Q : ℕ → ℕ} {k N lo : ℕ} (hk0 : 0 < k)
    (hk : ∀ n, lo ≤ n → 2 ^ (k * n) ∣ Q n) (h47 : ¬ 2 ^ 47 ∣ N)
    (hcheck : ∀ n ∈ Finset.Icc lo (46 / k), Q n ≠ N) :
    ∀ n, lo ≤ n → Q n ≠ N := by
  intro n hn hQN
  have hdvd : 2 ^ (k * n) ∣ N := by rw [← hQN]; exact hk n hn
  have hkn : k * n ≤ 46 := by
    by_contra h
    have h47le : 47 ≤ k * n := by omega
    exact h47 ((Nat.pow_dvd_pow 2 h47le).trans hdvd)
  have hle : n ≤ 46 / k := by
    rw [Nat.le_div_iff_mul_le hk0]
    calc n * k = k * n := Nat.mul_comm n k
      _ ≤ 46 := hkn
  exact hcheck n (Finset.mem_Icc.mpr ⟨hn, hle⟩) hQN

theorem ordA_two_pow_ne_of_not_dvd {N : ℕ} (h47 : ¬ 2 ^ 47 ∣ N)
    (hcheck : ∀ m ∈ Finset.Icc 3 15, ordA 2 (2 ^ m) ≠ N) :
    ∀ m, 3 ≤ m → ordA 2 (2 ^ m) ≠ N :=
  ne_of_dvd_check (Q := fun m => ordA 2 (2 ^ m)) (k := 3) (lo := 3) (by norm_num)
    (fun m hm => two_pow_mul_dvd_ordA m (by omega)) h47 hcheck

theorem ordG2_two_pow_ne_of_not_dvd {N : ℕ} (h47 : ¬ 2 ^ 47 ∣ N)
    (hcheck : ∀ m ∈ Finset.Icc 2 7, ordG2 (2 ^ m) ≠ N) :
    ∀ m, 2 ≤ m → ordG2 (2 ^ m) ≠ N :=
  ne_of_dvd_check (Q := fun m => ordG2 (2 ^ m)) (k := 6) (lo := 2) (by norm_num)
    (fun m hm => two_pow_six_mul_dvd_ordG2 (by omega)) h47 hcheck

theorem ordG2_two_pow_ne_sporadicCarrier_of_ne_M (s : TauCeti.SporadicName) (hs : s ≠ .M) :
    ∀ m, 2 ≤ m → ordG2 (2 ^ m) ≠ Nat.card (Carrier s) := by
  have gen : ∀ N : ℕ, Nat.card (Carrier s) = N → ¬ 2 ^ 47 ∣ N →
      (∀ m ∈ Finset.Icc 2 7, ordG2 (2 ^ m) ≠ N) →
      (∀ m, 2 ≤ m → ordG2 (2 ^ m) ≠ Nat.card (Carrier s)) :=
    fun N hN h47 hcheck => by
      rw [hN]
      exact ordG2_two_pow_ne_of_not_dvd h47 hcheck
  cases s
  case M => exact absurd rfl hs
  case M11 => exact gen _ CFSG.Sporadic.Mathieu.card_M11 (by decide) (by decide)
  case M12 => exact gen _ CFSG.Sporadic.Mathieu.card_M12 (by decide) (by decide)
  case M22 => exact gen _ CFSG.Sporadic.Mathieu.card_M22 (by decide) (by decide)
  case M23 => exact gen _ CFSG.EvenSmallLie.CatalogOrders.card_M23 (by decide) (by decide)
  case M24 => exact gen _ CFSG.Sporadic.Mathieu.card_M24 (by decide) (by decide)
  case J1 => exact gen _ CFSG.Sporadic.J1.card_J1 (by decide) (by decide)
  case J2 => exact gen _ CFSG.Sporadic.J2.card_J2 (by decide) (by decide)
  case J3 => exact gen _ CFSG.Sporadic.J3.card_J3 (by decide) (by decide)
  case J4 => exact gen _ CFSG.Sporadic.J4.card_J4 (by decide) (by decide)
  case HS => exact gen _ CFSG.Sporadic.HS.card_HS (by decide) (by decide)
  case McL => exact gen _ CFSG.Sporadic.McL.card_McL (by decide) (by decide)
  case He => exact gen _ CFSG.Sporadic.He.fam_he_order.1 (by decide) (by decide)
  case Ru => exact gen _ CFSG.Sporadic.Ru.card_Ru (by decide) (by decide)
  case Suz => exact gen _ CFSG.Sporadic.Suz.card_Suz (by decide) (by decide)
  case ONan => exact gen _ CFSG.Sporadic.ON.card_ON (by decide) (by decide)
  case Co1 => exact gen _ CFSG.Sporadic.Co1.card_Co1 (by decide) (by decide)
  case Co2 => exact gen _ CFSG.Sporadic.Co2.card_Co2 (by decide) (by decide)
  case Co3 => exact gen _ CFSG.Sporadic.Co3.card_Co3 (by decide) (by decide)
  case Fi22 => exact gen _ CFSG.Sporadic.Fi22.card_Fi22 (by decide) (by decide)
  case Fi23 => exact gen _ CFSG.Sporadic.Fi23.card_Fi23 (by decide) (by decide)
  case Fi24Prime => exact gen _ CFSG.Sporadic.Fi24.card_Fi24prime (by decide) (by decide)
  case HN => exact gen _ CFSG.Sporadic.HN.card_HN (by decide) (by decide)
  case Ly => exact gen _ CFSG.Sporadic.Ly.card_Ly (by decide) (by decide)
  case Th => exact gen _ CFSG.Monster.Existence.Compat.card_nativeTh (by decide) (by decide)
  case B => exact gen _ CFSG.Monster.Existence.card_nativeB (by decide) (by decide)

theorem thm46_psl3_not_sporadic (X : Type) [Group X] [IsSimpleGroup X] (n : ℕ) (hn : 3 ≤ n)
    (h : LieModel X .PSL 3 2 n) : ¬ SporadicRep X := by
  rintro ⟨s, ⟨e⟩⟩
  have hcard : Nat.card X = ordA 2 (2 ^ n) := card_of_lieModel_psl_three h
  by_cases hsM : s = .M
  · subst hsM
    have hM : Nat.card X = CFSG.Open.monsterOrder :=
      CFSG.SeitzReduction.RankOne.card_of_mulEquiv_nativeM (T := X)
        (show X ≃* CFSG.Blueprint.NativeSporadic.M from e)
    have heqM : ordA 2 (2 ^ n) = CFSG.Open.monsterOrder := by
      rw [← hcard]
      exact hM
    exact (ordA_two_pow_ne_of_not_dvd (N := CFSG.Open.monsterOrder) (by decide) (by decide) n hn)
      heqM
  · have hdvd : ordA 2 (2 ^ n) ∣ Nat.card (Carrier s) := by
      refine ⟨1, ?_⟩
      rw [mul_one, ← hcard]
      exact (Nat.card_congr e.toEquiv).symm
    have hres :=
      CFSG.SeitzReduction.LinearPilot.sl3SporadicResidual_of_dvd (f := n) (by omega) hsM hdvd
    rcases hres with h1 | ⟨h2, -⟩ | ⟨h4, hs⟩
    · omega
    · omega
    · subst h4
      rcases hs with rfl | rfl | rfl
      · have hEq : ordA 2 (2 ^ 4) = Nat.card (Carrier .Fi23) := by
          rw [← hcard]
          exact Nat.card_congr e.toEquiv
        have hval : ordA 2 (2 ^ 4) = 1425715200 := by rw [ordA_two]; norm_num
        have hcardF : Nat.card (Carrier .Fi23) = 4089470473293004800 :=
          CFSG.Sporadic.Fi23.card_Fi23
        rw [hval, hcardF] at hEq
        norm_num at hEq
      · have hEq : ordA 2 (2 ^ 4) = Nat.card (Carrier .Fi24Prime) := by
          rw [← hcard]
          exact Nat.card_congr e.toEquiv
        have hval : ordA 2 (2 ^ 4) = 1425715200 := by rw [ordA_two]; norm_num
        have hcardF : Nat.card (Carrier .Fi24Prime) = 1255205709190661721292800 :=
          CFSG.Sporadic.Fi24.card_Fi24prime
        rw [hval, hcardF] at hEq
        norm_num at hEq
      · have hEq : ordA 2 (2 ^ 4) = Nat.card (Carrier .B) := by
          rw [← hcard]
          exact Nat.card_congr e.toEquiv
        have hval : ordA 2 (2 ^ 4) = 1425715200 := by rw [ordA_two]; norm_num
        have hcardB : Nat.card (Carrier .B) = CFSG.Open.monsterBabyOrder :=
          CFSG.Monster.Existence.card_nativeB
        rw [hval, hcardB] at hEq
        norm_num [CFSG.Open.monsterBabyOrder] at hEq

theorem thm46_g2_not_sporadic (X : Type) [Group X] [IsSimpleGroup X] (n : ℕ) (hn : 2 ≤ n)
    (h : LieModel X .G2 0 2 n) : ¬ SporadicRep X := by
  rintro ⟨s, ⟨e⟩⟩
  have hcard : Nat.card X = ordG2 (2 ^ n) := card_of_lieModel_g_two_two_pow h
  have heq : ordG2 (2 ^ n) = Nat.card (Carrier s) := by
    rw [← hcard]
    exact Nat.card_congr e.toEquiv
  by_cases hsM : s = .M
  · subst hsM
    have hM : Nat.card X = CFSG.Open.monsterOrder :=
      CFSG.SeitzReduction.RankOne.card_of_mulEquiv_nativeM (T := X)
        (show X ≃* CFSG.Blueprint.NativeSporadic.M from e)
    have heqM : ordG2 (2 ^ n) = CFSG.Open.monsterOrder :=
      heq.trans ((Nat.card_congr e.toEquiv).symm.trans hM)
    exact (ordG2_two_pow_ne_of_not_dvd (N := CFSG.Open.monsterOrder) (by decide) (by decide) n hn)
      heqM
  · exact (ordG2_two_pow_ne_sporadicCarrier_of_ne_M s hsM n hn) heq

theorem thm46Orders_proved : Thm46Orders where
  psl3_gt := fun X _ n hn h => by
    rw [card_of_lieModel_psl_three h]
    exact ordA_two_pow_gt n hn
  g2_gt := fun X _ n hn h => by
    rw [card_of_lieModel_g_two_two_pow h]
    exact ordG2_two_pow_gt n hn
  suz_gt := fun X _ h => thm46_suz_gt X h
  psl3_not_sporadic := fun X _ _ n hn h => thm46_psl3_not_sporadic X n hn h
  g2_not_sporadic := fun X _ _ n hn h => thm46_g2_not_sporadic X n hn h
  psl3_ne_he := fun X _ n hn h => by
    rw [card_of_lieModel_psl_three h]
    exact ordA_two_pow_ne_of_not_dvd (N := 4030387200) (by decide) (by decide) n hn
  g2_ne_he := fun X _ n hn h => by
    rw [card_of_lieModel_g_two_two_pow h]
    exact ordG2_two_pow_ne_of_not_dvd (N := 4030387200) (by decide) (by decide) n hn

end CFSG.EvenSporadicStandard.Induction

