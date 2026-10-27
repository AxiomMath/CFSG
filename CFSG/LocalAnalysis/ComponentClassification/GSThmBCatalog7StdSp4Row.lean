module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdSp4

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup CatFactsSp4
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

theorem mul_sq_sub_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have h1 : a ^ 2 - 1 ≤ b ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hab.le 2) 1
  have h2 : 0 < b ^ 2 - 1 := by
    have : 2 ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  calc a * (a ^ 2 - 1) ≤ a * (b ^ 2 - 1) := Nat.mul_le_mul_left _ h1
    _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hab h2

theorem eq_of_mul_sq_sub_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (mul_sq_sub_lt ha hab))
  · exact hab
  · exact absurd h (ne_of_gt (mul_sq_sub_lt hb hab))

theorem mul_sq_sub_lt_psp {k : ℕ} (hk : 2 ≤ k) :
    k * (k ^ 2 - 1) < k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) := by
  have h1 : k < k ^ 4 := by
    calc k = k ^ 1 := (pow_one k).symm
      _ < k ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have h2 : 1 ≤ k ^ 4 - 1 := by omega
  have h3 : 0 < k ^ 2 - 1 := by
    have : 2 ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hk 2
    omega
  calc k * (k ^ 2 - 1) < k ^ 4 * (k ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right h1 h3
    _ = k ^ 4 * ((k ^ 2 - 1) * 1) := by rw [mul_one]
    _ ≤ k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)

theorem mul_sq_sub_sq_lt_psp {k : ℕ} (hk : 3 ≤ k) :
    k ^ 2 * ((k ^ 2) ^ 2 - 1) < k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) := by
  have e : (k ^ 2) ^ 2 = k ^ 4 := by ring
  rw [e]
  have hk4 : 1 ≤ k ^ 4 - 1 := by
    have : 3 ^ 4 ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
    omega
  have hk2 : 8 ≤ k ^ 2 - 1 := by
    have : 9 ≤ k ^ 2 := by nlinarith
    omega
  have hk2' : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hB : 0 < k ^ 4 * (k ^ 4 - 1) := Nat.mul_pos (by positivity) (by omega)
  calc k ^ 2 * (k ^ 4 - 1) ≤ k ^ 4 * (k ^ 4 - 1) := Nat.mul_le_mul_right _ hk2'
    _ < 8 * (k ^ 4 * (k ^ 4 - 1)) := lt_mul_of_one_lt_left hB (by norm_num)
    _ = k ^ 4 * (8 * (k ^ 4 - 1)) := by ring
    _ ≤ k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk2)

theorem psp_lt_mul_sq_sub {k : ℕ} (hk : 2 ≤ k) :
    k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) < k ^ 4 * ((k ^ 4) ^ 2 - 1) := by
  apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
  have h4 : 2 ^ 4 ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
  have h2 : 2 ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hk 2
  have h24 : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hle : k ^ 2 - 1 < k ^ 4 + 1 := by omega
  have e : (k ^ 4) ^ 2 - 1 = (k ^ 4 - 1) * (k ^ 4 + 1) := by
    have : 1 ≤ k ^ 4 := by omega
    zify [this, Nat.one_le_pow 2 (k ^ 4) (by omega)]
    ring
  rw [e, mul_comm (k ^ 2 - 1)]
  exact Nat.mul_lt_mul_of_pos_left hle (by omega)

theorem eq_of_psp4_orders {q r : ℕ} (hq : 5 ≤ q) (hr : 5 ≤ r)
    (hK : q ^ 2 * ((q ^ 2) ^ 2 - 1) = r * (r ^ 2 - 1) ∨
      q ^ 2 * ((q ^ 2) ^ 2 - 1) = r ^ 2 * ((r ^ 2) ^ 2 - 1) ∨
      ∃ k : ℕ, k ^ 2 = r ∧ 3 ≤ k ∧ q ^ 2 * ((q ^ 2) ^ 2 - 1) = k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)))
    (hJ : q * (q ^ 2 - 1) = r * (r ^ 2 - 1) ∨ q * (q ^ 2 - 1) = r ^ 2 * ((r ^ 2) ^ 2 - 1) ∨
      ∃ k : ℕ, k ^ 2 = r ∧ 3 ≤ k ∧ q * (q ^ 2 - 1) = k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1))) :
    q = r := by
  have hq2 : q < q ^ 2 := by nlinarith
  have hr2 : r < r ^ 2 := by nlinarith
  have hr4 : r ^ 2 < (r ^ 2) ^ 2 := by nlinarith
  rcases hJ with hJ | hJ | ⟨k, hk, hk3, hJ⟩
  · exact eq_of_mul_sq_sub_eq (by omega) (by omega) hJ
  ·
    have hqr : q = r ^ 2 := eq_of_mul_sq_sub_eq (by omega) (by nlinarith) hJ
    exfalso
    subst hqr
    rcases hK with hK | hK | ⟨k, hk, hk3, hK⟩
    · have := eq_of_mul_sq_sub_eq (by nlinarith) (by omega) hK
      omega
    · have := eq_of_mul_sq_sub_eq (by nlinarith) (by nlinarith) hK
      omega
    ·
      subst hk
      have e : ((k ^ 2) ^ 2) ^ 2 = (k ^ 4) ^ 2 := by ring
      rw [e] at hK
      have h1 := psp_lt_mul_sq_sub (k := k) (by omega)
      have h2 : k ^ 4 < (k ^ 4) ^ 2 := by
        have : 1 < k ^ 4 := by nlinarith
        nlinarith
      have h3 := mul_sq_sub_lt (a := k ^ 4) (by nlinarith) h2
      omega
  ·
    exfalso
    subst hk
    rcases hK with hK | hK | ⟨k', hk', hk3', hK⟩
    · have hqk : q ^ 2 = k ^ 2 := eq_of_mul_sq_sub_eq (by nlinarith) (by nlinarith) hK
      have hqk' : q = k := Nat.pow_left_injective two_ne_zero hqk
      subst hqk'
      have := mul_sq_sub_lt_psp (k := q) (by omega)
      omega
    · have hqk : q ^ 2 = (k ^ 2) ^ 2 := eq_of_mul_sq_sub_eq (by nlinarith) (by nlinarith) hK
      have hqk' : q = k ^ 2 := Nat.pow_left_injective two_ne_zero hqk
      subst hqk'
      have := mul_sq_sub_sq_lt_psp (k := k) hk3
      omega
    · have hkk : k' = k := Nat.pow_left_injective two_ne_zero hk'
      subst hkk
      have := eq_of_mul_sq_sub_eq (by nlinarith) (by omega) (hK.trans hJ.symm)
      omega

theorem ordL2sq_dvd_PSp43 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 25920) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 7) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

variable {H : Type} [Group H] [Finite H]

theorem pComponent_of_psp4 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (hs : IsSimpleGroup (StatedProj (StatedSp 2 K)))
    (hC : centralizer (generalizedFitting H : Set H) = ⊥)
    (e : ↥(generalizedFitting H) ≃* StatedProj (StatedSp 2 K)) {x : H} (hx : orderOf x = 2)
    {L : Subgroup H} (hLx : L ≤ centralizer ({x} : Set H)) (hLG : L ≤ generalizedFitting H)
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set H)))) :
    (∃ z ∈ L, orderOf z = 2 ∧ ∀ y ∈ L, y * z = z * y) ∨
      (IsSimpleGroup L ∧ (Nat.card L * 2 = p ^ f * ((p ^ f) ^ 2 - 1) ∨
        Nat.card L * 2 = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) ∨
        ∃ k : ℕ, k ^ 2 = p ^ f ∧ 3 ≤ k ∧
          Nat.card L * 2 = k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)))) := by
  obtain ⟨α, hα2, hα1, L', hL'α, hL'c, ⟨φ⟩⟩ := exists_fixed_pComponent hC hx hLx hLG hL e
  rcases pComponent_P hp hp2 hf hK h5 hs α (by rw [← pow_two]; exact hα2) hα1 hL'α hL'c with
    ⟨z, hz, hzo, hzc⟩ | ⟨hsimp, hcard⟩
  · left
    refine ⟨(φ ⟨z, hz⟩ : H), (φ ⟨z, hz⟩).2, ?_, fun y hy => ?_⟩
    · exact (Subgroup.orderOf_coe _).trans ((MulEquiv.orderOf_eq φ _).trans
        ((Subgroup.orderOf_coe (⟨z, hz⟩ : L')).symm.trans hzo))
    · obtain ⟨w, hw⟩ := φ.surjective ⟨y, hy⟩
      have h2 : w * ⟨z, hz⟩ = ⟨z, hz⟩ * w := Subtype.ext (hzc w w.2)
      have h3 := congrArg φ h2
      rw [map_mul, map_mul, hw] at h3
      exact congrArg Subtype.val h3
  · right
    exact ⟨φ.isSimpleGroup_congr.mp hsimp, by rw [← Nat.card_congr φ.toEquiv]; exact hcard⟩

theorem rowPSp4 : RowPSp4 := by
  intro H _ _ c p f hp hp2 hf hm
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hm
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hr3 : 3 ≤ p ^ f :=
    hp3.trans ((pow_one p).symm.le.trans (Nat.pow_le_pow_right hp.pos hf))
  have h5 : 5 ≤ p ^ f := by
    by_contra hlt
    have hodd' : Odd (p ^ f) := hK ▸ hodd
    obtain ⟨m, hm'⟩ := hodd'
    have h3 : p ^ f = 3 := by omega
    have hP := two_mul_card_P h2
    rw [hK, h3] at hP
    have hc : Nat.card (StatedProj (StatedSp 2 K)) = 25920 := by norm_num at hP; omega
    have hd := c.ordL2sq_dvd_of_equiv e
    rw [hc] at hd
    exact ordL2sq_dvd_PSp43 c.five_le hd
  have hs : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr (by omega)))
  have hKc := pComponent_of_psp4 hp hp2 hf hK h5 hs c.centralizer_eq_bot e c.orderOf_b c.K_le
    c.K_le_G c.isPComponent_K
  have hJc := pComponent_of_psp4 hp hp2 hf hK h5 hs c.centralizer_eq_bot e c.orderOf_a c.J_le
    c.J_le_G c.isPComponent_J
  obtain ⟨-, -, -, -, FK, _, _, hFK, ⟨eK⟩⟩ := AutL2Facts.lieModel_psl2_data c.type_K
  obtain ⟨-, -, -, -, FJ, _, _, hFJ, ⟨eJ⟩⟩ := AutL2Facts.lieModel_psl2_data c.type_J
  rcases hKc with ⟨z, hz, hzo, hzc⟩ | ⟨hKs, hKo⟩
  · exact (false_of_central_involution eK hz hzo hzc).elim
  rcases hJc with ⟨z, hz, hzo, hzc⟩ | ⟨hJs, hJo⟩
  · exact (false_of_central_involution eJ hz hzo hzc).elim
  have hf1 := c.one_le
  have hq5 := c.five_le
  have hhalf : ∀ x : ℕ, x * (x ^ 2 - 1) / 2 * 2 = x * (x ^ 2 - 1) := fun x =>
    Nat.div_mul_cancel (two_dvd_mul_sq_sub x)
  have hQK : Nat.card FK = (c.p ^ c.f) ^ 2 := by rw [hFK, ← pow_mul, mul_comm]
  have hKb : Nat.card (c.K ⧸ pPrimeCore 2 c.K) * 2 =
      (c.p ^ c.f) ^ 2 * (((c.p ^ c.f) ^ 2) ^ 2 - 1) := by
    rw [Nat.card_congr eK.toEquiv, GorensteinWalter.psl2_card_formula FK
      (AutL2Facts.isOddPrimePower_of c.prime c.ne_two (by omega) hFK), hQK, hhalf]
  have hJb : Nat.card (c.J ⧸ pPrimeCore 2 c.J) * 2 = c.p ^ c.f * ((c.p ^ c.f) ^ 2 - 1) := by
    rw [Nat.card_congr eJ.toEquiv, GorensteinWalter.psl2_card_formula FJ
      (AutL2Facts.isOddPrimePower_of c.prime c.ne_two c.one_le hFJ), hFJ, hhalf]
  have hq2 : 2 * 1 < (c.p ^ c.f) * ((c.p ^ c.f) ^ 2 - 1) := by
    have := mul_sq_sub_lt (a := 2) (by norm_num) (show 2 < c.p ^ c.f by omega)
    omega
  have hq2' : 2 * 1 < (c.p ^ c.f) ^ 2 * (((c.p ^ c.f) ^ 2) ^ 2 - 1) := by
    have := mul_sq_sub_lt (a := c.p ^ c.f) (by omega) (show c.p ^ c.f < (c.p ^ c.f) ^ 2 by
      nlinarith)
    omega
  have hK1 := card_quot_eq_of_simple hKs (fun h => by rw [h] at hKb; omega)
  have hJ1 := card_quot_eq_of_simple hJs (fun h => by rw [h] at hJb; omega)
  rw [hK1] at hKb
  rw [hJ1] at hJb
  have hqr : c.p ^ c.f = p ^ f := by
    apply eq_of_psp4_orders c.five_le h5
    · rcases hKo with h | h | ⟨k, hk, hk3, h⟩
      · exact Or.inl (hKb.symm.trans h)
      · exact Or.inr (Or.inl (hKb.symm.trans h))
      · exact Or.inr (Or.inr ⟨k, hk, hk3, hKb.symm.trans h⟩)
    · rcases hJo with h | h | ⟨k, hk, hk3, h⟩
      · exact Or.inl (hJb.symm.trans h)
      · exact Or.inr (Or.inl (hJb.symm.trans h))
      · exact Or.inr (Or.inr ⟨k, hk, hk3, hJb.symm.trans h⟩)
  have hpp : p = c.p := by
    rw [← hp.pow_minFac (show f ≠ 0 by omega), ← hqr,
      c.prime.pow_minFac (show c.f ≠ 0 by omega)]
  subst hpp
  exact ⟨rfl, (Nat.pow_right_injective hp.two_le hqr).symm⟩

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
