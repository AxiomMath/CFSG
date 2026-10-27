module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Inner82

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.Open

theorem prod_Icc_two_four (g : ℕ → ℕ) : ∏ i ∈ Finset.Icc 2 4, g i = g 2 * g 3 * g 4 := by
  rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

theorem ordA_one_le (Q : ℕ) : ordA 1 Q ≤ Q ^ 3 := by
  unfold ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  calc Q * (Q ^ 2 - 1) / Nat.gcd (1 + 1) (Q - 1) ≤ Q * (Q ^ 2 - 1) := Nat.div_le_self _ _
    _ ≤ Q * Q ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = Q ^ 3 := by ring

theorem ordA_one_sq_lt_ordA_three {q : ℕ} (hq : 3 ≤ q) : ordA 1 (q ^ 2) < ordA 3 q := by
  have h1 := ordA_one_le (q ^ 2)
  have hg : 0 < Nat.gcd (3 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg4 : Nat.gcd (3 + 1) (q - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have h2 : 2 * q ^ 6 < ordA 3 q := by
    unfold ordA
    rw [show 3 * (3 + 1) / 2 = 6 by rfl, show 3 + 1 = 4 by rfl, prod_Icc_two_four]
    have hq2 : 8 ≤ q ^ 2 - 1 := by
      have : 9 ≤ q ^ 2 := by nlinarith
      omega
    have hq3 : 26 ≤ q ^ 3 - 1 := by
      have : 27 ≤ q ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
      omega
    have hq4 : 80 ≤ q ^ 4 - 1 := by
      have : 81 ≤ q ^ 4 := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
      omega
    have hprod : 8 * 26 * 80 ≤ (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hq2 hq3) hq4
    set P := (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) with hP
    have hpos : 0 < q ^ 6 := pow_pos (by omega) 6
    have key : (2 * q ^ 6 + 1) ≤ q ^ 6 * P / Nat.gcd 4 (q - 1) := by
      rw [Nat.le_div_iff_mul_le hg]
      calc (2 * q ^ 6 + 1) * Nat.gcd 4 (q - 1) ≤ (2 * q ^ 6 + 1) * 4 :=
            Nat.mul_le_mul_left _ hg4
        _ ≤ q ^ 6 * P := by nlinarith
    omega
  calc ordA 1 (q ^ 2) ≤ (q ^ 2) ^ 3 := h1
    _ = q ^ 6 := by ring
    _ < 2 * q ^ 6 := by have : 0 < q ^ 6 := pow_pos (by omega) 6; omega
    _ < ordA 3 q := h2

theorem ordA_one_sq_lt_ordTwistedA_three {q : ℕ} (hq : 3 ≤ q) :
    ordA 1 (q ^ 2) < ordTwistedA 3 q := by
  have h1 := ordA_one_le (q ^ 2)
  have hg : 0 < Nat.gcd (3 + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg4 : Nat.gcd (3 + 1) (q + 1) ≤ 4 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have h2 : 2 * q ^ 6 < ordTwistedA 3 q := by
    unfold ordTwistedA
    rw [show 3 * (3 + 1) / 2 = 6 by rfl, show 3 + 1 = 4 by rfl, prod_Icc_two_four]
    have h1q2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h1q4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    have e2 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
      have : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub h1q2, Nat.cast_pow]
        ring
      rw [this, Int.toNat_natCast]
    have e3 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
      have : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [this, Int.toNat_natCast]
    have e4 : ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4).toNat = q ^ 4 - 1 := by
      have : ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4) = ((q ^ 4 - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub h1q4, Nat.cast_pow]
        ring
      rw [this, Int.toNat_natCast]
    rw [e2, e3, e4]
    have hq2 : 8 ≤ q ^ 2 - 1 := by
      have : 9 ≤ q ^ 2 := by nlinarith
      omega
    have hq3 : 28 ≤ q ^ 3 + 1 := by
      have : 27 ≤ q ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
      omega
    have hq4 : 80 ≤ q ^ 4 - 1 := by
      have : 81 ≤ q ^ 4 := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
      omega
    have hprod : 8 * 28 * 80 ≤ (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hq2 hq3) hq4
    set P := (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) with hP
    have hpos : 0 < q ^ 6 := pow_pos (by omega) 6
    have key : (2 * q ^ 6 + 1) ≤ q ^ 6 * P / Nat.gcd 4 (q + 1) := by
      rw [Nat.le_div_iff_mul_le hg]
      calc (2 * q ^ 6 + 1) * Nat.gcd 4 (q + 1) ≤ (2 * q ^ 6 + 1) * 4 :=
            Nat.mul_le_mul_left _ hg4
        _ ≤ q ^ 6 * P := by nlinarith
    omega
  calc ordA 1 (q ^ 2) ≤ (q ^ 2) ^ 3 := h1
    _ = q ^ 6 := by ring
    _ < 2 * q ^ 6 := by have : 0 < q ^ 6 := pow_pos (by omega) 6; omega
    _ < ordTwistedA 3 q := h2

theorem ordA_one_sq_ne_A10 {q : ℕ} (hq : Odd q) : ordA 1 (q ^ 2) ≠ 1814400 := by
  intro h
  have h2 := two_mul_ordA_one (hq.pow (n := 2))
  rw [h] at h2
  have hq12 : q ≤ 12 := by
    by_contra hlt
    push Not at hlt
    have h13 : 13 ≤ q := hlt
    have e1 : 169 ≤ q ^ 2 := by nlinarith
    have e2 : 28561 ≤ (q ^ 2) ^ 2 := by nlinarith
    have : 169 * 28560 ≤ q ^ 2 * ((q ^ 2) ^ 2 - 1) := Nat.mul_le_mul e1 (by omega)
    omega
  obtain ⟨t, rfl⟩ := hq
  have ht : t ≤ 5 := by omega
  interval_cases t <;> norm_num at h2

theorem A6_ne : (360 : ℕ) ≠ ordA 3 3 ∧ (360 : ℕ) ≠ ordTwistedA 3 3 ∧ (360 : ℕ) ≠ 1814400 := by
  refine ⟨?_, ?_, by norm_num⟩
  · unfold ordA
    rw [prod_Icc_two_four]
    norm_num
  · unfold ordTwistedA
    rw [prod_Icc_two_four]
    norm_num

theorem card_alternatingGroup_ten : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem false_of_isSec8JType {L Y : Type} [Group L] [Group Y] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hL : IsSec82LType L p f) (hY : IsSec8JType Y p f)
    (e : Y ≃* L) : False := by
  have hcard := Nat.card_congr e.toEquiv
  have hq3 : 3 ≤ p ^ f := by
    have : 3 ≤ p := by have := hp.two_le; omega
    calc 3 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hcL : Nat.card L = ordA 3 (p ^ f) ∨ Nat.card L = ordTwistedA 3 (p ^ f) ∨
      Nat.card L = 1814400 := by
    rcases hL with hL | hL | hA
    · exact Or.inl ((ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL)).1 rfl)
    · exact Or.inr (Or.inl ((ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL)).2.1 rfl))
    · obtain ⟨eA⟩ := hA
      exact Or.inr (Or.inr ((Nat.card_congr eA.toEquiv).trans card_alternatingGroup_ten))
  rcases hY with hY | ⟨rfl, rfl, hY⟩
  · have hcY : Nat.card Y = ordA 1 ((p ^ f) ^ 2) := by
      rw [card_of_lieModel_psl_two hp2 hY, ← pow_mul, mul_comm]
    rw [hcY] at hcard
    rcases hcL with h | h | h <;> rw [h] at hcard
    · exact absurd hcard (ordA_one_sq_lt_ordA_three hq3).ne
    · exact absurd hcard (ordA_one_sq_lt_ordTwistedA_three hq3).ne
    · exact ordA_one_sq_ne_A10 ((hp.odd_of_ne_two hp2).pow) hcard
  · obtain ⟨eY⟩ := hY
    rw [Nat.card_congr eY.toEquiv, AZ.card_alternatingGroup_six] at hcard
    obtain ⟨h1, h2, h3⟩ := A6_ne
    rcases hcL with h | h | h <;> rw [h] at hcard
    · exact h1 (by simpa using hcard)
    · exact h2 (by simpa using hcard)
    · exact h3 hcard

theorem false_of_isPComponent_one {H : Type} [Group H] [Finite H] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) [hsimp : IsSimpleGroup ↥(generalizedFitting H)]
    (htype : IsSec82LType ↥(generalizedFitting H) p f)
    (hperf : ∀ J : Subgroup H, ⁅J, J⁆ = J → J ≤ generalizedFitting H) {J₁ : Subgroup H}
    (hJC : J₁ ≤ centralizer ({1} : Set H))
    (hcomp : IsPComponent 2 (J₁.subgroupOf (centralizer ({1} : Set H))))
    (hJtype : IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f) : False := by
  classical
  set L := generalizedFitting H with hLdef
  have hJp : ⁅J₁, J₁⁆ = J₁ := commutator_eq_self_of_isPComponent hJC hcomp
  have hJL := hperf J₁ hJp
  have hCtop : centralizer ({1} : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_centralizer_singleton_iff, mul_one, one_mul]
  obtain ⟨-, -, hsub, -, -⟩ := hcomp
  have hsubH : J₁.IsSubnormal := by
    have hsurj : Function.Surjective (centralizer ({1} : Set H)).subtype := by
      intro x
      exact ⟨⟨x, hCtop ▸ mem_top x⟩, rfl⟩
    have := hsub.map hsurj
    rwa [map_subgroupOf_eq_of_le hJC] at this
  have hsubL : (J₁.subgroupOf L).IsSubnormal := hsubH.subgroupOf
  rcases hsubL.eq_bot_or_top_of_isSimpleGroup hsimp with h0 | h0
  ·
    have hJ1 : J₁ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hJL hx⟩ : L) ∈ J₁.subgroupOf L := mem_subgroupOf.mpr hx
      rw [h0, mem_bot] at this
      rw [mem_bot]
      exact congrArg Subtype.val this
    have hY1 : Nat.card (↥J₁ ⧸ pPrimeCore 2 ↥J₁) = 1 := by
      have hc : Nat.card J₁ = 1 := by rw [hJ1, card_bot]
      have := Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥J₁)
      rw [hc] at this
      exact Nat.dvd_one.mp this
    have h2 := AZ.two_mul_card_of_isSec8JType hp hp2 hJtype
    rw [hY1] at h2
    have hq3 : 3 ≤ p ^ f := by
      have : 3 ≤ p := by have := hp.two_le; omega
      calc 3 ≤ p := this
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    have : 9 ≤ (p ^ f) ^ 2 := by nlinarith
    have : 81 ≤ (p ^ f) ^ 4 := by nlinarith
    have : 9 * 80 ≤ (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  ·
    have hJeq : J₁ = L := by
      apply le_antisymm hJL
      intro x hx
      have : (⟨x, hx⟩ : L) ∈ J₁.subgroupOf L := by rw [h0]; exact mem_top _
      exact mem_subgroupOf.mp this
    set e₀ : ↥J₁ ≃* ↥L := MulEquiv.subgroupCongr hJeq
    have : IsSimpleGroup ↥J₁ := e₀.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥J₁) with hO | hO
    · have e₁ : (↥J₁ ⧸ pPrimeCore 2 ↥J₁) ≃* ↥L :=
        (QuotientGroup.quotientMulEquivOfEq hO).trans (QuotientGroup.quotientBot.trans e₀)
      exact false_of_isSec8JType hp hp2 hf htype hJtype e₁
    · have hY1 : Nat.card (↥J₁ ⧸ pPrimeCore 2 ↥J₁) = 1 := by
        rw [hO, ← Subgroup.index_eq_card, Subgroup.index_top]
      have h2 := AZ.two_mul_card_of_isSec8JType hp hp2 hJtype
      rw [hY1] at h2
      have hq3 : 3 ≤ p ^ f := by
        have : 3 ≤ p := by have := hp.two_le; omega
        calc 3 ≤ p := this
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
      have : 9 ≤ (p ^ f) ^ 2 := by nlinarith
      have : 81 ≤ (p ^ f) ^ 4 := by nlinarith
      have : 9 * 80 ≤ (p ^ f) ^ 2 * ((p ^ f) ^ 4 - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega

end Inner82

end CFSG.ComponentClassification.CatFactsL4U4
