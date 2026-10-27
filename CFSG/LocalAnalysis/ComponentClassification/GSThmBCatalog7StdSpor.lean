module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdArith
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdInputs
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.Suz.Simple

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup

theorem ordL2sq_dvd_J1 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 175560) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 9) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

theorem ordL2sq_dvd_J2 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 604800) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 12) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

theorem ordL2sq_dvd_J3 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 50232960) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 25) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

theorem ordL2sq_dvd_M12 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 95040) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 9) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

theorem ordL2sq_dvd_HS {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 44352000) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 25) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

theorem ordL2sq_dvd_ON {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 460815505920) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 111) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

theorem ordL2sq_dvd_He {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 4030387200) : Q = 7 := by
  have hQ := lt_of_ordL2sq_dvd (B := 51) (by norm_num) (by decide) h
  interval_cases Q <;> first | rfl | (revert h; decide)

theorem ordL2sq_dvd_Suz {Q : ℕ} (h5 : 5 ≤ Q) (hQo : Odd Q) (h : ordL2sq Q ∣ 448345497600) :
    Q = 5 := by
  have hQ := lt_of_ordL2sq_dvd (B := 111) (by norm_num) (by decide) h
  interval_cases Q <;> first | rfl | (revert h hQo; decide)

theorem eq_of_pow_eq_prime {p f s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hs : s < 9) (h : p ^ f = s) : f = 1 ∧ p = s := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hf1 : f = 1 := by
    by_contra hne
    have : 3 ^ 2 ≤ p ^ f :=
      (Nat.pow_le_pow_left hp3 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  subst hf1
  exact ⟨rfl, by rw [← h, pow_one]⟩

variable {H : Type} [Group H] [Finite H]

theorem rowSporadic
    (hHe : HeL2Input) (hSuz : SuzL2Input) : RowSporadic := by
  intro H _ _ c hs
  have h5 := c.five_le
  rcases hs with hs | hs | hs | hs | hs | hs | hs | hs
  · have h := c.ordL2sq_dvd_of_equiv (Classical.choice hs)
    rw [show Nat.card (Blueprint.NativeSporadic.Carrier .J1) = _ from
      CFSG.Sporadic.J1.card_J1] at h
    exact ordL2sq_dvd_J1 h5 h
  · have h := c.ordL2sq_dvd_of_equiv (Classical.choice hs)
    rw [show Nat.card (Blueprint.NativeSporadic.Carrier .J2) = _ from
      CFSG.Sporadic.J2.card_J2] at h
    exact ordL2sq_dvd_J2 h5 h
  · have h := c.ordL2sq_dvd_of_equiv (Classical.choice hs)
    rw [show Nat.card (Blueprint.NativeSporadic.Carrier .J3) = _ from
      CFSG.Sporadic.J3.card_J3] at h
    exact ordL2sq_dvd_J3 h5 h
  · have h := c.ordL2sq_dvd_of_equiv (Classical.choice hs)
    rw [show Nat.card (Blueprint.NativeSporadic.Carrier .M12) = _ from
      CFSG.Sporadic.Mathieu.card_M12] at h
    exact ordL2sq_dvd_M12 h5 h
  · have h := c.ordL2sq_dvd_of_equiv (Classical.choice hs)
    rw [show Nat.card (Blueprint.NativeSporadic.Carrier .HS) = _ from
      CFSG.Sporadic.HS.card_HS] at h
    exact ordL2sq_dvd_HS h5 h
  · have h := c.ordL2sq_dvd_of_equiv (Classical.choice hs)
    rw [show Nat.card (Blueprint.NativeSporadic.Carrier .He) = _ from
      CFSG.Sporadic.He.card_He] at h
    obtain ⟨hf1, hp7⟩ := eq_of_pow_eq_prime c.prime c.ne_two c.one_le (by norm_num)
      (ordL2sq_dvd_He h5 h)
    have hK := c.type_K
    rw [hf1, hp7] at hK
    exact hHe H c.simple c.centralizer_eq_bot hs c.b c.orderOf_b c.K c.K_le c.isPComponent_K hK
  · have h := c.ordL2sq_dvd_of_equiv (Classical.choice hs)
    rw [show Nat.card (Blueprint.NativeSporadic.Carrier .ONan) = _ from
      CFSG.Sporadic.ON.card_ON] at h
    exact ordL2sq_dvd_ON h5 h
  · have h := c.ordL2sq_dvd_of_equiv (Classical.choice hs)
    rw [show Nat.card (Blueprint.NativeSporadic.Carrier .Suz) = _ from
      CFSG.Sporadic.Suz.card_Suz] at h
    obtain ⟨hf1, hp5⟩ := eq_of_pow_eq_prime c.prime c.ne_two c.one_le (by norm_num)
      (ordL2sq_dvd_Suz h5 c.odd_q h)
    have hK := c.type_K
    rw [hf1, hp5] at hK
    exact hSuz H c.simple c.centralizer_eq_bot hs c.b c.orderOf_b c.K c.K_le c.isPComponent_K hK

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
