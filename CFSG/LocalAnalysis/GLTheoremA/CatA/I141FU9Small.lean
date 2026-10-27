module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Pre
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018CoreField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Trans
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatSingle
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LemRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge lieOrderBridge_holds)

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

open CFSG.LocalAnalysis.GLTheoremA.I2018 (catalogIs_congr' fixSubgroup_one_eq_top)


@[expose] def u9FamTwF4Eight : TauCeti.CFSGIndex → Prop :=
  onLie fun | .reeF4 1 => True | _ => False

theorem u9_not_three_dvd_suzuki (m : ℕ) : ¬ 3 ∣ orderSuzuki (2 ^ (2 * m + 1)) := by
  have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
    induction m with
    | zero => norm_num
    | succ k ih =>
      have : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by ring
      omega
  generalize 2 ^ (2 * m + 1) = q at hq ⊢
  unfold orderSuzuki
  intro h
  have h3 : Nat.Prime 3 := Nat.prime_three
  rcases (Nat.Prime.dvd_mul h3).1 h with h | h
  · rcases (Nat.Prime.dvd_mul h3).1 h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow h3 h
      omega
    · have h1 : q ^ 2 % 3 = 1 := by
        rw [Nat.pow_mod, hq]
      omega
  · omega

theorem u9_not_two_pow_nine_dvd_ree (m : ℕ) : ¬ 2 ^ 9 ∣ orderRee (3 ^ (2 * m + 1)) := by
  have hq : 3 ^ (2 * m + 1) % 16 = 3 ∨ 3 ^ (2 * m + 1) % 16 = 11 := by
    induction m with
    | zero => norm_num
    | succ k ih =>
      have : 3 ^ (2 * (k + 1) + 1) = 9 * 3 ^ (2 * k + 1) := by ring
      omega
  generalize 3 ^ (2 * m + 1) = q at hq ⊢
  have h8 : orderRee q % 16 = 8 := by
    unfold orderRee
    rcases hq with hq | hq
    · have h1 : (q - 1) % 16 = 2 := by omega
      have h2 : q ^ 3 % 16 = 11 := by rw [Nat.pow_mod, hq]
      have h3 : (q ^ 3 + 1) % 16 = 12 := by omega
      rw [Nat.mul_mod, Nat.mul_mod (q ^ 3), h2, h3, h1]
    · have h1 : (q - 1) % 16 = 10 := by omega
      have h2 : q ^ 3 % 16 = 3 := by rw [Nat.pow_mod, hq]
      have h3 : (q ^ 3 + 1) % 16 = 4 := by omega
      rw [Nat.mul_mod, Nat.mul_mod (q ^ 3), h2, h3, h1]
  intro h
  have h16 : 16 ∣ orderRee q := (show 16 ∣ 2 ^ 9 by norm_num).trans h
  omega

theorem u9_three_dvd_of_seven_dvd_twF4 (m : ℕ) (h : 7 ∣ orderTwistedF4 (2 ^ (2 * m + 1))) :
    3 ∣ 2 * m + 1 := by
  by_contra hk
  have hq : 2 ^ (2 * m + 1) % 7 = 2 ∨ 2 ^ (2 * m + 1) % 7 = 4 := by
    have h1 : ∀ n : ℕ, 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by
      intro n
      conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul]
      rw [Nat.mul_mod, Nat.pow_mod]
      norm_num
    rw [h1]
    have : (2 * m + 1) % 3 = 1 ∨ (2 * m + 1) % 3 = 2 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num
  generalize 2 ^ (2 * m + 1) = q at hq h
  unfold orderTwistedF4 at h
  have h7 : Nat.Prime 7 := by norm_num
  rcases hq with hq | hq
  · rcases (Nat.Prime.dvd_mul h7).1 h with h | h
    · rcases (Nat.Prime.dvd_mul h7).1 h with h | h
      · rcases (Nat.Prime.dvd_mul h7).1 h with h | h
        · rcases (Nat.Prime.dvd_mul h7).1 h with h | h
          · have := Nat.Prime.dvd_of_dvd_pow h7 h
            omega
          · have h1 : q ^ 6 % 7 = 1 := by rw [Nat.pow_mod, hq]
            omega
        · have h1 : q ^ 4 % 7 = 2 := by rw [Nat.pow_mod, hq]
          omega
      · have h1 : q ^ 3 % 7 = 1 := by rw [Nat.pow_mod, hq]
        omega
    · omega
  · rcases (Nat.Prime.dvd_mul h7).1 h with h | h
    · rcases (Nat.Prime.dvd_mul h7).1 h with h | h
      · rcases (Nat.Prime.dvd_mul h7).1 h with h | h
        · rcases (Nat.Prime.dvd_mul h7).1 h with h | h
          · have := Nat.Prime.dvd_of_dvd_pow h7 h
            omega
          · have h1 : q ^ 6 % 7 = 1 := by rw [Nat.pow_mod, hq]
            omega
        · have h1 : q ^ 4 % 7 = 4 := by rw [Nat.pow_mod, hq]
          omega
      · have h1 : q ^ 3 % 7 = 1 := by rw [Nat.pow_mod, hq]
        omega
    · omega

theorem u9_not_dvd_tits : ¬ 5515776 ∣ orderTits := by
  unfold orderTits
  norm_num

theorem u9_twF4_gt (m : ℕ) (hm : 1 ≤ m) : 5515776 < orderTwistedF4 (2 ^ (2 * m + 1)) := by
  have hq : 8 ≤ 2 ^ (2 * m + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * m + 1) = q at hq ⊢
  unfold orderTwistedF4
  have h1 : 8 ^ 12 ≤ q ^ 12 := Nat.pow_le_pow_left hq 12
  have h2 : 1 ≤ q ^ 6 + 1 := by omega
  have h3 : 1 ≤ q ^ 4 - 1 := by
    have : 8 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    omega
  have h4 : 1 ≤ q ^ 3 + 1 := by omega
  have h5 : 1 ≤ q - 1 := by omega
  calc 5515776 < 8 ^ 12 := by norm_num
    _ ≤ q ^ 12 := h1
    _ = q ^ 12 * 1 * 1 * 1 * 1 := by ring
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) := by gcongr

theorem u9_dvd_card {S : Type} [Group S] [Finite S] {I : Subgroup S} (hb : LieOrderBridge)
    (hU : catalogIs (PSimple 3 I) S9.isU3eight) : 5515776 ∣ Nat.card S := by
  have h1 : Nat.card (PSimple 3 I) = 5515776 := CatSingle.card_isU3eight hb hU
  rw [← h1]
  exact (Subgroup.card_dvd_of_surjective (f := chevQuotHom 3 I) (chevQuotHom_surjective 3 I)).trans
    (Subgroup.card_subgroup_dvd_card I)

section Certs


theorem i141U9Fam_small (hF4 : I141U9Fam u9FamTwF4Eight) : I141U9Fam u9FamSmall := by
  intro Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  obtain ⟨hs, hna⟩ := u9_simple_nonabelian hI1
  obtain ⟨α, hα3, hJ', ⟨eJ⟩⟩ := u9_transfer hx hI1 hJ
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 K J)) S9.isU3eight := catalogIs_congr' eJ hJU
  have hdvd0 : 5515776 ∣ Nat.card (PSimple 3 K) := u9_dvd_card lieOrderBridge_holds hU'
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | lie d' =>
    obtain ⟨d, hv⟩ := d'
    have hord : Nat.card (PSimple 3 K) = lieOrderFormula d := lieOrderBridge_holds ⟨d, hv⟩ _ ⟨e⟩
    rw [hord] at hdvd0
    cases d with
    | suzuki m =>
      exact (u9_not_three_dvd_suzuki m ((show 3 ∣ 5515776 by norm_num).trans hdvd0)).elim
    | reeG2 m =>
      exact (u9_not_two_pow_nine_dvd_ree m ((show 2 ^ 9 ∣ 5515776 by norm_num).trans hdvd0)).elim
    | tits => exact (u9_not_dvd_tits hdvd0).elim
    | reeF4 m =>
      have hm1 : 1 ≤ m := by simpa using hv
      by_cases h3 : 3 ∣ 2 * m + 1
      · by_cases hα1 : α = 1
        · exfalso
          haveI := hs
          have hI : GLAPComponent 3 (⊤ : Subgroup (PSimple 3 K)) (chevTransfer 3 K J) := by
            rw [hα1, fixSubgroup_one_eq_top] at hJ'
            exact hJ'
          obtain ⟨eT⟩ := chevQ_pSimple_top_equiv Nat.prime_three hna hI
          have hcard : Nat.card (PSimple 3 K) = 5515776 := by
            rw [← Nat.card_congr eT.toEquiv]
            exact CatSingle.card_isU3eight lieOrderBridge_holds hU'
          have := u9_twF4_gt m hm1
          rw [hord] at hcard
          exact absurd hcard (by
            show orderTwistedF4 (2 ^ (2 * m + 1)) ≠ 5515776
            omega)
        · have hFB := CFSG.LocalAnalysis.GLTheoremA.I2018Core.field_bound hs hna ⟨.reeF4 m, hv⟩
            (TauCeti.LieTypeIndex.characteristic_reeF4 m) e hα3 hα1 hJ' hU'
          obtain ⟨-, -, -, -, hdiv | ⟨hPSU, -⟩⟩ := hFB
          · have hle : 2 * m + 1 ≤ 3 := Nat.le_of_dvd (by norm_num) hdiv
            have hm : m = 1 := by omega
            subst hm
            exact hF4 Γ K J x a ⟨.lie ⟨.reeF4 1, hv⟩, by simp [u9FamTwF4Eight, onLie], ⟨e⟩⟩ hx ha hxa hxna hI1 hI2
              hJ hJU hZ hF
          · exact absurd hPSU (by simp [CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf])
      · exact (h3 (u9_three_dvd_of_seven_dvd_twF4 m
          ((show 7 ∣ 5515776 by norm_num).trans hdvd0))).elim
    | _ => exact hi.elim
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
