module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.I1420

private theorem four_dvd_two_pow_pow {e N : ℕ} (h : 2 ≤ e * N) : 4 ∣ (2 ^ e) ^ N := by
  rw [← pow_mul]
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact Nat.pow_dvd_pow 2 h

private theorem four_dvd_two_pow {e : ℕ} (h : 2 ≤ e) : 4 ∣ 2 ^ e := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact Nat.pow_dvd_pow 2 h

private theorem four_dvd_mul_div {a Y g : ℕ} (hg : g ∣ Y) (ha : 4 ∣ a) : 4 ∣ a * Y / g := by
  apply Nat.dvd_div_of_mul_dvd
  rw [mul_comm g 4]
  exact mul_dvd_mul ha hg

private theorem sub_one_dvd_sq_sub_one (Q : ℕ) : Q - 1 ∣ Q ^ 2 - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow Q 1 2

private theorem add_one_dvd_sq_sub_one (Q : ℕ) : Q + 1 ∣ Q ^ 2 - 1 := by
  cases Q with
  | zero => simp
  | succ k =>
    refine ⟨k, ?_⟩
    have h : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
    rw [h, Nat.add_sub_cancel]

private theorem card_eq_two_pow {q : TauCeti.PrimePower} (hq : q.p = 2) :
    1 ≤ q.exponent ∧ q.card = 2 ^ q.exponent := by
  refine ⟨q.exponent_pos, ?_⟩
  rw [TauCeti.PrimePower.card_def, hq]

private theorem four_dvd_card_pow {q : TauCeti.PrimePower} (hq : q.p = 2) {N : ℕ} (hN : 2 ≤ N) :
    4 ∣ q.card ^ N := by
  obtain ⟨he, hQ⟩ := card_eq_two_pow hq
  rw [hQ]
  exact four_dvd_two_pow_pow (le_trans (by norm_num) (Nat.mul_le_mul he hN))

private theorem four_dvd_card {q : TauCeti.PrimePower} (hq : q.p = 2) (h4 : 4 ≤ q.card) :
    4 ∣ q.card := by
  obtain ⟨he, hQ⟩ := card_eq_two_pow hq
  have h2 : 2 ≤ q.exponent := by
    by_contra hlt
    have he1 : q.exponent = 1 := by omega
    rw [he1, pow_one] at hQ
    omega
  rw [hQ]
  exact four_dvd_two_pow h2

private theorem four_dvd_lieOrderFormula (d : TauCeti.LieTypeIndex) (hv : d.Valid)
    (hc : d.characteristic = 2) : 4 ∣ lieOrderFormula d := by
  have hs := (TauCeti.LieTypeIndex.inStandardRange_iff d).1
    ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
  cases d with
  | A r q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_A] using hc
    have hs' : 1 ≤ r ∧ (r = 1 → 4 ≤ q.card) := hs
    have hr1 : 1 ≤ r := hs'.1
    have hmem : (2 : ℕ) ∈ Finset.Icc 2 (r + 1) := Finset.mem_Icc.2 ⟨le_refl _, by omega⟩
    have hY : Nat.gcd (r + 1) (q.card - 1) ∣ ∏ i ∈ Finset.Icc 2 (r + 1), (q.card ^ i - 1) :=
      dvd_trans (Nat.gcd_dvd_right _ _)
        (dvd_trans (sub_one_dvd_sq_sub_one q.card)
          (Finset.dvd_prod_of_mem (fun i : ℕ => q.card ^ i - 1) hmem))
    have h4 : 4 ∣ q.card ^ (r * (r + 1) / 2) := by
      rcases Nat.lt_or_ge r 2 with hr | hr
      · obtain rfl : r = 1 := by omega
        have hN : 1 * (1 + 1) / 2 = 1 := by norm_num
        rw [hN, pow_one]
        exact four_dvd_card hq (hs'.2 rfl)
      · apply four_dvd_card_pow hq
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        nlinarith
    unfold lieOrderFormula orderA
    exact four_dvd_mul_div hY h4
  | twistedA r q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_twistedA] using hc
    have hs' : 2 ≤ r ∧ (r = 2 → 3 ≤ q.card) := hs
    have hr2 : 2 ≤ r := hs'.1
    have hmem : (2 : ℕ) ∈ Finset.Icc 2 (r + 1) := Finset.mem_Icc.2 ⟨le_refl _, by omega⟩
    have hsq : q.card + 1 ∣
        ∏ i ∈ Finset.Icc 2 (r + 1), (if Even i then q.card ^ i - 1 else q.card ^ i + 1) := by
      refine dvd_trans (add_one_dvd_sq_sub_one q.card) ?_
      have := Finset.dvd_prod_of_mem
        (fun i : ℕ => if Even i then q.card ^ i - 1 else q.card ^ i + 1) hmem
      simpa using this
    have hY := dvd_trans (Nat.gcd_dvd_right (r + 1) (q.card + 1)) hsq
    have h4 : 4 ∣ q.card ^ (r * (r + 1) / 2) := by
      apply four_dvd_card_pow hq
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      nlinarith
    unfold lieOrderFormula orderTwistedA
    exact four_dvd_mul_div hY h4
  | B r q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_B] using hc
    have hs' : 2 ≤ r ∧ ¬(r = 2 ∧ q.card = 2) := hs
    have hr2 : 2 ≤ r := hs'.1
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 r := Finset.mem_Icc.2 ⟨le_refl _, by omega⟩
    have hsq : q.card ^ 2 - 1 ∣ ∏ i ∈ Finset.Icc 1 r, (q.card ^ (2 * i) - 1) := by
      have := Finset.dvd_prod_of_mem (fun i : ℕ => q.card ^ (2 * i) - 1) hmem
      simpa using this
    have hY := dvd_trans (Nat.gcd_dvd_right 2 (q.card - 1))
      (dvd_trans (sub_one_dvd_sq_sub_one q.card) hsq)
    have h4 : 4 ∣ q.card ^ (r * r) := four_dvd_card_pow hq (by nlinarith)
    unfold lieOrderFormula orderBC
    exact four_dvd_mul_div hY h4
  | C r q =>
    have hs' : 3 ≤ r ∧ q.p ≠ 2 := hs
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_C] using hc
    exact absurd hq hs'.2
  | D r q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_D] using hc
    have hr : 4 ≤ r := hs
    have hY : Nat.gcd 4 (q.card ^ r - 1) ∣
        (q.card ^ r - 1) * ∏ i ∈ Finset.Icc 1 (r - 1), (q.card ^ (2 * i) - 1) :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
    have h4 : 4 ∣ q.card ^ (r * (r - 1)) := by
      apply four_dvd_card_pow hq
      have h := Nat.mul_le_mul hr (show 3 ≤ r - 1 by omega)
      exact le_trans (by norm_num) h
    show 4 ∣ orderD r q.card
    unfold orderD
    rw [mul_assoc]
    exact four_dvd_mul_div hY h4
  | twistedD r q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_twistedD] using hc
    have hr : 4 ≤ r := hs
    have hY : Nat.gcd 4 (q.card ^ r + 1) ∣
        (q.card ^ r + 1) * ∏ i ∈ Finset.Icc 1 (r - 1), (q.card ^ (2 * i) - 1) :=
      dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
    have h4 : 4 ∣ q.card ^ (r * (r - 1)) := by
      apply four_dvd_card_pow hq
      have h := Nat.mul_le_mul hr (show 3 ≤ r - 1 by omega)
      exact le_trans (by norm_num) h
    show 4 ∣ orderTwistedD r q.card
    unfold orderTwistedD
    rw [mul_assoc]
    exact four_dvd_mul_div hY h4
  | E6 q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_E6] using hc
    have h36 : 4 ∣ q.card ^ 36 := four_dvd_card_pow hq (by norm_num)
    have hY : Nat.gcd 3 (q.card - 1) ∣ q.card ^ 2 - 1 :=
      dvd_trans (Nat.gcd_dvd_right _ _) (sub_one_dvd_sq_sub_one q.card)
    have h4 : 4 ∣ q.card ^ 36 * (q.card ^ 12 - 1) * (q.card ^ 9 - 1) * (q.card ^ 8 - 1) *
        (q.card ^ 6 - 1) * (q.card ^ 5 - 1) :=
      ((((h36.mul_right _).mul_right _).mul_right _).mul_right _).mul_right _
    unfold lieOrderFormula orderE6
    exact four_dvd_mul_div hY h4
  | E7 q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_E7] using hc
    have h63 : 4 ∣ q.card ^ 63 := four_dvd_card_pow hq (by norm_num)
    have hY : Nat.gcd 2 (q.card - 1) ∣ q.card ^ 2 - 1 :=
      dvd_trans (Nat.gcd_dvd_right _ _) (sub_one_dvd_sq_sub_one q.card)
    have h4 : 4 ∣ q.card ^ 63 * (q.card ^ 18 - 1) * (q.card ^ 14 - 1) * (q.card ^ 12 - 1) *
        (q.card ^ 10 - 1) * (q.card ^ 8 - 1) * (q.card ^ 6 - 1) :=
      ((((((h63.mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _)
    unfold lieOrderFormula orderE7
    exact four_dvd_mul_div hY h4
  | E8 q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_E8] using hc
    have h120 : 4 ∣ q.card ^ 120 := four_dvd_card_pow hq (by norm_num)
    unfold lieOrderFormula orderE8
    exact ((((((((h120.mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _)
  | F4 q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_F4] using hc
    have h24 : 4 ∣ q.card ^ 24 := four_dvd_card_pow hq (by norm_num)
    unfold lieOrderFormula orderF4
    exact (((h24.mul_right _).mul_right _).mul_right _).mul_right _
  | G2 q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_G2] using hc
    have h6 : 4 ∣ q.card ^ 6 := four_dvd_card_pow hq (by norm_num)
    unfold lieOrderFormula orderG2
    exact (h6.mul_right _).mul_right _
  | twistedE6 q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_twistedE6] using hc
    have h36 : 4 ∣ q.card ^ 36 := four_dvd_card_pow hq (by norm_num)
    have hY : Nat.gcd 3 (q.card + 1) ∣ q.card ^ 2 - 1 :=
      dvd_trans (Nat.gcd_dvd_right _ _) (add_one_dvd_sq_sub_one q.card)
    have h4 : 4 ∣ q.card ^ 36 * (q.card ^ 12 - 1) * (q.card ^ 9 + 1) * (q.card ^ 8 - 1) *
        (q.card ^ 6 - 1) * (q.card ^ 5 + 1) :=
      ((((h36.mul_right _).mul_right _).mul_right _).mul_right _).mul_right _
    unfold lieOrderFormula orderTwistedE6
    exact four_dvd_mul_div hY h4
  | trialityD4 q =>
    have hq : q.p = 2 := by simpa [TauCeti.LieTypeIndex.characteristic_trialityD4] using hc
    have h12 : 4 ∣ q.card ^ 12 := four_dvd_card_pow hq (by norm_num)
    unfold lieOrderFormula orderTrialityD4
    exact ((h12.mul_right _).mul_right _).mul_right _
  | suzuki m =>
    have hm : 1 ≤ m := hs
    have h4 : 4 ∣ (2 ^ (2 * m + 1)) ^ 2 := four_dvd_two_pow_pow (by omega)
    unfold lieOrderFormula orderSuzuki
    exact (h4.mul_right _).mul_right _
  | reeG2 m =>
    simp [TauCeti.LieTypeIndex.characteristic_reeG2] at hc
  | reeF4 m =>
    have hm : 1 ≤ m := hs
    have h12 : 4 ∣ (2 ^ (2 * m + 1)) ^ 12 := four_dvd_two_pow_pow (by omega)
    unfold lieOrderFormula orderTwistedF4
    exact (((h12.mul_right _).mul_right _).mul_right _).mul_right _
  | tits =>
    unfold lieOrderFormula orderTits
    norm_num

private theorem four_dvd_ambiguous_lie (d : TauCeti.LieTypeIndex) (hv : d.Valid)
    (hi : ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) : 4 ∣ lieOrderFormula d := by
  cases d
  case A r q =>
    rcases r with _ | _ | r
    · simp [ambiguousChev] at hi
    · have h7 : q.card = 7 := by
        simp only [ambiguousChev] at hi
        omega
      show 4 ∣ orderA (0 + 1) q.card
      rw [h7]
      decide
    · exact (hi : False).elim
  case twistedA r q =>
    rcases r with _ | _ | _ | r
    · simp [ambiguousChev] at hi
    · simp [ambiguousChev] at hi
    · have h3 : q.card = 3 := by
        simp only [ambiguousChev] at hi
        omega
      show 4 ∣ orderTwistedA (0 + 1 + 1) q.card
      rw [h3]
      decide
    · simp only [ambiguousChev] at hi
      split at hi <;> simp_all
  all_goals simp [ambiguousChev] at hi

theorem chevTwoFourDvd_body :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsChevSimple 2 S → 4 ∣ Nat.card S := by
  intro S _ _ _ hch
  rcases hch with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  ·
    cases i with
    | cyclic p hp => exact (hi : False).elim
    | alternating n h => exact (hi : False).elim
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      have hc : d.characteristic = 2 := hi
      rw [lieOrderBridge_holds ⟨d, hv⟩ S ⟨e⟩]
      exact four_dvd_lieOrderFormula d hv hc
    | sporadic s => exact (hi : False).elim
  ·
    cases i with
    | cyclic p hp => exact (hi : False).elim
    | alternating n h =>
      have hn : n = 5 ∨ n = 6 ∨ n = 8 := by
        simp [ambiguousChev] at hi
        omega
      rcases hn with rfl | rfl | rfl
      · have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
          rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
          decide
        rw [Nat.card_congr e.toEquiv]
        change 4 ∣ Nat.card (alternatingGroup (Fin 5))
        rw [hA]
        norm_num
      · have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
          rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
          decide
        rw [Nat.card_congr e.toEquiv]
        change 4 ∣ Nat.card (alternatingGroup (Fin 6))
        rw [hA]
        norm_num
      · have hA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
          rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
          decide
        rw [Nat.card_congr e.toEquiv]
        change 4 ∣ Nat.card (alternatingGroup (Fin 8))
        rw [hA]
        norm_num
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      rw [lieOrderBridge_holds ⟨d, hv⟩ S ⟨e⟩]
      exact four_dvd_ambiguous_lie d hv hi
    | sporadic s => exact (hi : False).elim

theorem chevTwoFourDvd_holds :
    ChevTwoFourDvd :=
  chevTwoFourDvd_body

end CFSG.LocalAnalysis.GLTheoremA
