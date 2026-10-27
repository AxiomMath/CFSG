module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Ord
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open CFSG.Blueprint

theorem ordObs {N : ℕ} (hN : N ≤ 50232960)
    (hdvd : ∀ q : ℕ, 5 ≤ q → q < 20 → ¬ (q * (q ^ 2 - 1)) ^ 2 / 2 ∣ N) :
    ∀ q : ℕ, 5 ≤ q → ∀ m : ℕ, m ∣ N → 2 * m ≤ N →
      2 * m ≠ (q * (q ^ 2 - 1)) ^ 2 ∧
        2 * m ≠ (q ^ 3 * ((q ^ 3) ^ 2 - 1)) * (q * (q ^ 2 - 1)) := by
  intro q hq m hm hm2
  have h125 : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h25 : 25 ≤ q ^ 2 := by
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have ha : 5 * 24 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq (by omega)
  constructor
  · intro h
    have hq20 : q < 20 := by
      by_contra hge
      have hge : 20 ≤ q := Nat.le_of_not_lt hge
      have h400 : 400 ≤ q ^ 2 := by
        calc 400 = 20 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hge 2
      have h1 : 20 * 399 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hge (by omega)
      have h2 : (20 * 399) ^ 2 ≤ (q * (q ^ 2 - 1)) ^ 2 := Nat.pow_le_pow_left h1 2
      norm_num at h2
      omega
    refine hdvd q hq hq20 ?_
    have hm' : m = (q * (q ^ 2 - 1)) ^ 2 / 2 := by omega
    rw [← hm']
    exact hm
  · intro h
    have h125' : 125 ^ 2 ≤ (q ^ 3) ^ 2 := Nat.pow_le_pow_left h125 2
    have h1 : 125 * (125 ^ 2 - 1) ≤ q ^ 3 * ((q ^ 3) ^ 2 - 1) :=
      Nat.mul_le_mul h125 (by omega)
    have h2 := Nat.mul_le_mul h1 ha
    norm_num at h2
    omega

theorem eight_dvd_sq_sub_one {n : ℕ} (hn : n % 2 = 1) : 8 ∣ n ^ 2 - 1 := by
  have h : n ^ 2 % 8 = 1 := by
    have h8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
    rcases h8 with h | h | h | h <;> simp [pow_two, Nat.mul_mod, h]
  omega

theorem ordRee_pow_three_mod (k : ℕ) : CFSG.Open.ordRee (3 ^ (2 * k + 1)) % 16 = 8 := by
  have hQ : ∀ j : ℕ, 3 ^ (2 * j + 1) % 16 = 3 ∨ 3 ^ (2 * j + 1) % 16 = 11 := by
    intro j
    induction j with
    | zero => left; norm_num
    | succ n ih =>
      have e : 3 ^ (2 * (n + 1) + 1) = 9 * 3 ^ (2 * n + 1) := by ring
      rw [e]
      omega
  obtain ⟨R, hR⟩ : ∃ R, 3 ^ (2 * k + 1) = R + 1 :=
    ⟨3 ^ (2 * k + 1) - 1, (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))).symm⟩
  have hR' : R % 16 = 2 ∨ R % 16 = 10 := by
    have := hQ k
    omega
  rw [hR, CFSG.Open.ordRee, Nat.add_sub_cancel]
  rcases hR' with h | h
  · have e1 : R + 1 ≡ 3 [MOD 16] := by unfold Nat.ModEq; omega
    have e2 : R ≡ 2 [MOD 16] := h
    have := ((e1.pow 3).mul ((e1.pow 3).add_right 1)).mul e2
    unfold Nat.ModEq at this
    rw [this]
    norm_num
  · have e1 : R + 1 ≡ 11 [MOD 16] := by unfold Nat.ModEq; omega
    have e2 : R ≡ 10 [MOD 16] := h
    have := ((e1.pow 3).mul ((e1.pow 3).add_right 1)).mul e2
    unfold Nat.ModEq at this
    rw [this]
    norm_num

theorem k94_small :
    K94Excl fun K _ => LieModel K .PSL 2 2 3 ∨ LieModel K .PSL 2 2 4 ∨ LieModel K .PSL 3 2 2 ∨
      LieModel K .twistedB2 0 2 3 := by
  have h1 : K94Excl fun K _ => LieModel K .PSL 2 2 3 :=
    k94Excl_of_card (N := 504)
      (fun K _ _ h => by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide)
      (ordObs (by norm_num) (by decide))
  have h2 : K94Excl fun K _ => LieModel K .PSL 2 2 4 :=
    k94Excl_of_card (N := 4080)
      (fun K _ _ h => by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide)
      (ordObs (by norm_num) (by decide))
  have h3 : K94Excl fun K _ => LieModel K .PSL 3 2 2 :=
    k94Excl_of_card (N := 20160)
      (fun K _ _ h => by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide)
      (ordObs (by norm_num) (by decide))
  have h4 : K94Excl fun K _ => LieModel K .twistedB2 0 2 3 :=
    k94Excl_of_card (N := 29120)
      (fun K _ _ h => by rw [CFSG.GH74.card_of_lieModel_twistedB2 h]; decide)
      (ordObs (by norm_num) (by decide))
  exact k94Excl_or h1 (k94Excl_or h2 (k94Excl_or h3 h4))

theorem k94_g2_three :
    K94Excl fun K _ => LieModel K .G2 0 3 1 :=
  k94Excl_of_card (N := 4245696)
    (fun K _ _ h => by rw [CFSG.GH74.card_of_lieModel_G2 (by norm_num) h]; decide)
    (ordObs (by norm_num) (by decide))

theorem k94_spor_ord :
    K94Excl fun K _ =>
      NativeSporadic.IsSporadic K .M12 ∨ NativeSporadic.IsSporadic K .M22 ∨
        NativeSporadic.IsSporadic K .M23 ∨ NativeSporadic.IsSporadic K .J1 ∨
        NativeSporadic.IsSporadic K .J3 := by
  have h1 : K94Excl fun K _ => NativeSporadic.IsSporadic K .M12 :=
    k94Excl_of_card (N := 95040)
      (fun K _ _ h => by rw [CFSG.GH74.card_of_isSporadic_M12 h]; norm_num)
      (ordObs (by norm_num) (by decide))
  have h2 : K94Excl fun K _ => NativeSporadic.IsSporadic K .M22 :=
    k94Excl_of_card (N := 443520)
      (fun K _ _ h => by rw [CFSG.GH74.card_of_isSporadic_M22 h]; norm_num)
      (ordObs (by norm_num) (by decide))
  have h3 : K94Excl fun K _ => NativeSporadic.IsSporadic K .M23 :=
    k94Excl_of_card (N := 10200960)
      (fun K _ _ h => by rw [CFSG.GH74.card_of_isSporadic_M23 h]; norm_num)
      (ordObs (by norm_num) (by decide))
  have h4 : K94Excl fun K _ => NativeSporadic.IsSporadic K .J1 :=
    k94Excl_of_card (N := 175560)
      (fun K _ _ h => by rw [CFSG.GH74.card_of_isSporadic_J1 h]; norm_num)
      (ordObs (by norm_num) (by decide))
  have h5 : K94Excl fun K _ => NativeSporadic.IsSporadic K .J3 :=
    k94Excl_of_card (N := 50232960)
      (fun K _ _ h => by rw [CFSG.GH74.card_of_isSporadic_J3 h]; norm_num)
      (ordObs (by norm_num) (by decide))
  exact k94Excl_or h1 (k94Excl_or h2 (k94Excl_or h3 (k94Excl_or h4 h5)))

theorem k94_ree :
    K94Excl fun K _ => ∃ f : ℕ, LieModel K .twistedG2 0 3 f := by
  intro K _ _ hs hnab _ _ hPK z I₁ I₂ F₁ F₂ _ _ _ _ cfg
  obtain ⟨f, hf⟩ := hPK
  obtain ⟨k, -, hcard⟩ := CFSG.GH74.card_of_lieModel_twistedG2 hf
  obtain ⟨m, -, hm, -, p, e, hp, hp2, -, hmq⟩ := cfg.exists_order_data hs hnab
  have hodd : p ^ e % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  have hodd3 : (p ^ e) ^ 3 % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hodd).pow)
  have ha : 8 ∣ p ^ e * ((p ^ e) ^ 2 - 1) := Dvd.dvd.mul_left (eight_dvd_sq_sub_one hodd) _
  have hb : 8 ∣ (p ^ e) ^ 3 * (((p ^ e) ^ 3) ^ 2 - 1) :=
    Dvd.dvd.mul_left (eight_dvd_sq_sub_one hodd3) _
  have h64 : 64 ∣ 2 * m := by
    rcases hmq with h | h
    · rw [h, pow_two]
      exact mul_dvd_mul ha ha
    · rw [h]
      exact mul_dvd_mul hb ha
  have h32 : 32 ∣ m := by omega
  have hK : 32 ∣ Nat.card K := h32.trans hm
  rw [hcard] at hK
  have := ordRee_pow_three_mod k
  omega

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
