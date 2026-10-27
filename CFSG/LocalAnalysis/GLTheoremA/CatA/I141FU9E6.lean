module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Char
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Small
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Lab
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgE6Res2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge lieOrderBridge_holds)

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

open CFSG.LocalAnalysis.GLTheoremA.I2018 (catalogIs_congr' fixSubgroup_one_eq_top)


@[expose] def u9FamTwE6Two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedE6 q => q.card = 2 | _ => False

theorem u9_orderE6_gt {q : ℕ} (hq : 2 ≤ q) : 5515776 < orderE6 q := by
  unfold orderE6
  have h36 : 2 ^ 36 ≤ q ^ 36 := Nat.pow_le_pow_left hq 36
  have hf : ∀ k : ℕ, 1 ≤ k → 1 ≤ q ^ k - 1 := fun k hk => by
    have : 2 ^ k ≤ q ^ k := Nat.pow_le_pow_left hq k
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hP : 2 ^ 36 ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1) :=
    calc 2 ^ 36 ≤ q ^ 36 := h36
      _ = q ^ 36 * 1 * 1 * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by
        gcongr
        exacts [hf 12 (by norm_num), hf 9 (by norm_num), hf 8 (by norm_num), hf 6 (by norm_num),
          hf 5 (by norm_num), hf 2 (by norm_num)]
  have hg : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  calc 5515776 < 2 ^ 36 / 3 := by norm_num
    _ ≤ (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)) / 3 :=
        Nat.div_le_div_right hP
    _ ≤ _ := Nat.div_le_div_left hg hg0

theorem u9_orderTwistedE6_gt {q : ℕ} (hq : 2 ≤ q) : 5515776 < orderTwistedE6 q := by
  unfold orderTwistedE6
  have h36 : 2 ^ 36 ≤ q ^ 36 := Nat.pow_le_pow_left hq 36
  have hf : ∀ k : ℕ, 1 ≤ k → 1 ≤ q ^ k - 1 := fun k hk => by
    have : 2 ^ k ≤ q ^ k := Nat.pow_le_pow_left hq k
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hP : 2 ^ 36 ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1) :=
    calc 2 ^ 36 ≤ q ^ 36 := h36
      _ = q ^ 36 * 1 * 1 * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by
        gcongr
        exacts [hf 12 (by norm_num), by omega, hf 8 (by norm_num), hf 6 (by norm_num),
          by omega, hf 2 (by norm_num)]
  have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  calc 5515776 < 2 ^ 36 / 3 := by norm_num
    _ ≤ (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)) / 3 :=
        Nat.div_le_div_right hP
    _ ≤ _ := Nat.div_le_div_left hg hg0

theorem u9_not_nineteen_dvd_orderE6_two : ¬ 19 ∣ orderE6 2 := by
  unfold orderE6
  norm_num

section Certs


theorem i141U9Fam_e6 (hG2 : U9Gf8Absurd) (hTwE6 : I141U9Fam u9FamTwE6Two) : I141U9Fam u9FamE6 := by
  intro Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  obtain ⟨hs, hna⟩ := u9_simple_nonabelian hI1
  obtain ⟨hα3, hJ', ⟨eJ⟩⟩ := u9_transfer_chev hx hI1 hJ
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 K J)) S9.isU3eight := catalogIs_congr' eJ hJU
  have hdvd0 : 5515776 ∣ Nat.card (PSimple 3 K) := u9_dvd_card lieOrderBridge_holds hU'
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | lie d' =>
    obtain ⟨d, hv⟩ := d'
    have hord : Nat.card (PSimple 3 K) = lieOrderFormula d := lieOrderBridge_holds ⟨d, hv⟩ _ ⟨e⟩
    have hchar2 : (⟨d, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic = 2 := by
      rcases u9_char_two hI1 e with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd Nat.card_pos hdvd0) (by omega)
    haveI := hs
    by_cases hα1 : chevAut 3 K ⟨x, hI1.1 (Subgroup.mem_zpowers x)⟩ = 1
    ·
      exfalso
      have hI : GLAPComponent 3 (⊤ : Subgroup (PSimple 3 K)) (chevTransfer 3 K J) := by
        rw [hα1, fixSubgroup_one_eq_top] at hJ'
        exact hJ'
      obtain ⟨eT⟩ := chevQ_pSimple_top_equiv Nat.prime_three hna hI
      have hcard : Nat.card (PSimple 3 K) = 5515776 := by
        rw [← Nat.card_congr eT.toEquiv]
        exact CatSingle.card_isU3eight lieOrderBridge_holds hU'
      rw [hord] at hcard
      cases d with
      | E6 q =>
        have hq2 : 2 ≤ q.card := by
          have := q.prime_p.two_le
          calc 2 ≤ q.p := this
            _ = q.p ^ 1 := (pow_one _).symm
            _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
            _ = q.card := (TauCeti.PrimePower.card_def q).symm
        have := u9_orderE6_gt hq2
        exact absurd hcard (by show orderE6 q.card ≠ 5515776; omega)
      | twistedE6 q =>
        have hq2 : 2 ≤ q.card := by
          have := q.prime_p.two_le
          calc 2 ≤ q.p := this
            _ = q.p ^ 1 := (pow_one _).symm
            _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
            _ = q.card := (TauCeti.PrimePower.card_def q).symm
        have := u9_orderTwistedE6_gt hq2
        exact absurd hcard (by show orderTwistedE6 q.card ≠ 5515776; omega)
      | _ => exact hi.elim
    · cases d with
      | E6 q =>
        have hq2 : q.p = 2 := by simpa using hchar2
        obtain ⟨-, -, -, -, hdiv | ⟨hPSU, -⟩⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.I2018Core.field_bound hs hna ⟨.E6 q, hv⟩ hchar2 e hα3 hα1 hJ' hU'
        · have hdiv' : q.exponent ∣ 3 := by simpa [CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf] using hdiv
          rcases (Nat.dvd_prime Nat.prime_three).1 hdiv' with h1 | h3
          · have hc : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hq2, h1]; norm_num
            rw [hord] at hdvd0
            have h19 : 19 ∣ orderE6 2 := by
              have := (show 19 ∣ 5515776 by norm_num).trans hdvd0
              rwa [show lieOrderFormula (.E6 q) = orderE6 q.card from rfl, hc] at this
            exact absurd h19 u9_not_nineteen_dvd_orderE6_two
          · have hc : q.card = 8 := by rw [TauCeti.PrimePower.card_def, hq2, h3]; norm_num
            exact (hG2 Γ K J x a hx ha hxa hI1 hI2 hJ hJU hF ⟨.E6 q, hv⟩ ⟨e⟩ hchar2
              (by simpa [KD264Lie.fieldSize] using hc)
              (KD264Lie.lieCompAlg_excUntwisted_kd264e6 ⟨.E6 q, hv⟩ (by simp [KD264Lie.isExcUntwistedIdx])
                (by simpa [KD264Lie.fieldSize] using hc)) hα1).elim
        · exact absurd hPSU (by simp [CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf])
      | twistedE6 q =>
        have hq2 : q.p = 2 := by simpa using hchar2
        obtain ⟨-, -, -, -, hdiv | ⟨hPSU, -⟩⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.I2018Core.field_bound hs hna ⟨.twistedE6 q, hv⟩ hchar2 e hα3 hα1 hJ' hU'
        · have hdiv' : q.exponent ∣ 3 := by simpa [CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf] using hdiv
          rcases (Nat.dvd_prime Nat.prime_three).1 hdiv' with h1 | h3
          · have hc : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hq2, h1]; norm_num
            exact hTwE6 Γ K J x a ⟨.lie ⟨.twistedE6 q, hv⟩, by simpa [u9FamTwE6Two, onLie] using hc, ⟨e⟩⟩ hx ha
              hxa hxna hI1 hI2 hJ hJU hZ hF
          · have hc : q.card = 8 := by rw [TauCeti.PrimePower.card_def, hq2, h3]; norm_num
            exact (hG2 Γ K J x a hx ha hxa hI1 hI2 hJ hJU hF ⟨.twistedE6 q, hv⟩ ⟨e⟩ hchar2
              (by simpa [KD264Lie.fieldSize] using hc)
              (KD264Lie.lieCompAlg_excTwisted_kd264e6 ⟨.twistedE6 q, hv⟩ (by simp [KD264Lie.isExcTwistedIdx])
                (by simpa [KD264Lie.fieldSize] using hc)) hα1).elim
        · exact absurd hPSU (by simp [CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf])
      | _ => exact hi.elim
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
