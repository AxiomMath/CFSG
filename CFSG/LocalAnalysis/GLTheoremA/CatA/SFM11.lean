module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM11Cross3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM11Same
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM11Orders

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM11

theorem B3_lieModel {H : Type} [Group H] {Q' : TauCeti.PrimePower}
    (hvB : (TauCeti.LieTypeIndex.B 3 Q').Valid)
    (eB : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 3 Q', hvB⟩) :
    ∃ t : CFSG.Open.StatedLieTag, CFSG.Blueprint.LieModel H t 3 Q'.p Q'.exponent ∧
      (t = .PSp ∨ t = .POmegaOdd) := by
  rcases CFSG.Models.lieModel_B 3 Q' hvB eB with h | h
  · exact ⟨_, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) h, Or.inl rfl⟩
  · exact ⟨_, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) h, Or.inr rfl⟩

theorem prime_pow_two_le {Q : TauCeti.PrimePower} : 2 ≤ Q.p ^ Q.exponent :=
  le_trans Q.prime_p.two_le (Nat.le_self_pow Q.exponent_pos.ne' Q.p)

section Cert

theorem core_A3_B {H : Type} [Group H] (Q Q' : TauCeti.PrimePower)
    (hvA : (TauCeti.LieTypeIndex.A 3 Q).Valid) (eA : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 3 Q, hvA⟩)
    (hvB : (TauCeti.LieTypeIndex.B 3 Q').Valid) (eB : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 3 Q', hvB⟩) :
    False := by
  obtain ⟨hbX, hEX, hfX⟩ := YS05NonIso.orderEq_A3 Q hvA eA
  obtain ⟨t', hbY, ht'⟩ := B3_lieModel hvB eB
  obtain ⟨d, hd4, hd1, hEY, hfY⟩ := orderEq_B3 hbY ht'
  have hq2 : 2 ≤ Q.p ^ Q.exponent := prime_pow_two_le
  have hs2 : 2 ≤ Q'.p ^ Q'.exponent := prime_pow_two_le
  have hg4 : Nat.gcd 4 (Q.p ^ Q.exponent - 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hg1 : Nat.gcd 4 (Q.p ^ Q.exponent - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) hg4
  refine YS05NonIso.dispatch hbX hbY ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨-, h⟩
    norm_num at h
  · rintro ⟨-, h⟩
    norm_num at h
  · rintro ⟨h, -⟩
    cases h
  · rintro ⟨h, -⟩
    rcases ht' with rfl | rfl <;> cases h
  · intro hpr
    rw [← hpr] at hEY hfY
    have hab : 6 * Q.exponent = 9 * Q'.exponent := hfX.symm.trans hfY
    exact same_B_A3_pab Q.prime_p Q.exponent_pos Q'.exponent_pos hab hg1 hd1 hEX hEY
  · intro hpr hp2 hr2
    have hpP := Q.prime_p
    have hpR := Q'.prime_p
    have hsodd : Odd (Q'.p ^ Q'.exponent) := Odd.pow (hpR.odd_of_ne_two hr2)
    have hps : ¬ Q.p ∣ Q'.p ^ Q'.exponent := YS05NonIso.pn_pow hpP hpR hpr
    by_cases h3 : Q.p = 3
    · have hfac : (Nat.card H).factorization 3 = 6 * Q.exponent := h3 ▸ hfX
      have hs3 : ¬ 3 ∣ Q'.p ^ Q'.exponent :=
        YS05NonIso.pn_pow (by norm_num) hpR (by omega)
      exact cross_p3_B hs2 hs3 hd4 hd1 hfac hEY
    · have hp5 : 5 ≤ Q.p := YS05NonIso.five_le hpP hp2 h3
      exact cross_ge5_B hpP hp5 hs2 hsodd hps hg4 hd4 (fx_A3_pos hq2) (fx_A3_lt hq2) hEX hEY

theorem core_A3_D {H : Type} [Group H] (Q Q' : TauCeti.PrimePower)
    (hvA : (TauCeti.LieTypeIndex.A 3 Q).Valid) (eA : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 3 Q, hvA⟩)
    (hvD : (TauCeti.LieTypeIndex.D 4 Q').Valid) (eD : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D 4 Q', hvD⟩) :
    False := by
  obtain ⟨hbX, hEX, hfX⟩ := YS05NonIso.orderEq_A3 Q hvA eA
  have hbY := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (t := .POmegaPlus) (by decide)
    (CFSG.Models.lieModel_D 4 Q' hvD eD)
  obtain ⟨d, hd4, hd1, hEY, hfY⟩ := orderEq_D4 hbY
  have hq2 : 2 ≤ Q.p ^ Q.exponent := prime_pow_two_le
  have hs2 : 2 ≤ Q'.p ^ Q'.exponent := prime_pow_two_le
  have hg4 : Nat.gcd 4 (Q.p ^ Q.exponent - 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hg1 : Nat.gcd 4 (Q.p ^ Q.exponent - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) hg4
  refine YS05NonIso.dispatch hbX hbY ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨-, h⟩
    norm_num at h
  · rintro ⟨h, -⟩
    cases h
  · rintro ⟨h, -⟩
    cases h
  · rintro ⟨h, -⟩
    cases h
  · intro hpr
    rw [← hpr] at hEY hfY
    have hab : 6 * Q.exponent = 12 * Q'.exponent := hfX.symm.trans hfY
    exact same_D_A3_pab Q.prime_p Q'.exponent_pos hab hg1 hd1 hEX hEY
  · intro hpr hp2 hr2
    have hpP := Q.prime_p
    have hpR := Q'.prime_p
    have hsodd : Odd (Q'.p ^ Q'.exponent) := Odd.pow (hpR.odd_of_ne_two hr2)
    have hps : ¬ Q.p ∣ Q'.p ^ Q'.exponent := YS05NonIso.pn_pow hpP hpR hpr
    by_cases h3 : Q.p = 3
    · have hfac : (Nat.card H).factorization 3 = 6 * Q.exponent := h3 ▸ hfX
      have hs3 : ¬ 3 ∣ Q'.p ^ Q'.exponent :=
        YS05NonIso.pn_pow (by norm_num) hpR (by omega)
      exact cross_p3_D hs2 hs3 hd4 hd1 hfac hEY
    · have hp5 : 5 ≤ Q.p := YS05NonIso.five_le hpP hp2 h3
      exact cross_ge5_D hpP hp5 hs2 hsodd hps hg4 hd4 (fx_A3_pos hq2) (fx_A3_lt hq2) hEX hEY

theorem core_A3_D2 {H : Type} [Group H] (Q Q' : TauCeti.PrimePower)
    (hvA : (TauCeti.LieTypeIndex.A 3 Q).Valid) (eA : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 3 Q, hvA⟩)
    (hvD : (TauCeti.LieTypeIndex.twistedD 4 Q').Valid)
    (eD : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedD 4 Q', hvD⟩) : False := by
  obtain ⟨hbX, hEX, hfX⟩ := YS05NonIso.orderEq_A3 Q hvA eA
  have hbY := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (t := .POmegaMinus) (by decide)
    (CFSG.Models.lieModel_twistedD 4 Q' hvD eD)
  obtain ⟨d, hd4, hd1, hEY, hfY⟩ := orderEq_D2_4 hbY
  have hq2 : 2 ≤ Q.p ^ Q.exponent := prime_pow_two_le
  have hs2 : 2 ≤ Q'.p ^ Q'.exponent := prime_pow_two_le
  have hg4 : Nat.gcd 4 (Q.p ^ Q.exponent - 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hg1 : Nat.gcd 4 (Q.p ^ Q.exponent - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) hg4
  refine YS05NonIso.dispatch hbX hbY ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨-, h⟩
    norm_num at h
  · rintro ⟨h, -⟩
    cases h
  · rintro ⟨h, -⟩
    cases h
  · rintro ⟨h, -⟩
    cases h
  · intro hpr
    rw [← hpr] at hEY hfY
    have hab : 6 * Q.exponent = 12 * Q'.exponent := hfX.symm.trans hfY
    exact same_D2_A3_pab Q.prime_p Q'.exponent_pos hab hg1 hd1 hEX hEY
  · intro hpr hp2 hr2
    have hpP := Q.prime_p
    have hpR := Q'.prime_p
    have hsodd : Odd (Q'.p ^ Q'.exponent) := Odd.pow (hpR.odd_of_ne_two hr2)
    have hps : ¬ Q.p ∣ Q'.p ^ Q'.exponent := YS05NonIso.pn_pow hpP hpR hpr
    by_cases h3 : Q.p = 3
    · have hfac : (Nat.card H).factorization 3 = 6 * Q.exponent := h3 ▸ hfX
      have hs3 : ¬ 3 ∣ Q'.p ^ Q'.exponent :=
        YS05NonIso.pn_pow (by norm_num) hpR (by omega)
      exact cross_p3_D2 hs2 hs3 hd4 hd1 hfac hEY
    · have hp5 : 5 ≤ Q.p := YS05NonIso.five_le hpP hp2 h3
      exact cross_ge5_D2 hpP hp5 hs2 hsodd hps hg4 hd4 (fx_A3_pos hq2) (fx_A3_lt hq2) hEX hEY

theorem core_U4_B {H : Type} [Group H] (Q Q' : TauCeti.PrimePower)
    (hvU : (TauCeti.LieTypeIndex.twistedA 3 Q).Valid)
    (eU : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 Q, hvU⟩)
    (hvB : (TauCeti.LieTypeIndex.B 3 Q').Valid) (eB : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 3 Q', hvB⟩) :
    False := by
  obtain ⟨hbX, hEX, hfX⟩ := YS05NonIso.orderEq_U4 Q hvU eU
  obtain ⟨t', hbY, ht'⟩ := B3_lieModel hvB eB
  obtain ⟨d, hd4, hd1, hEY, hfY⟩ := orderEq_B3 hbY ht'
  have hq2 : 2 ≤ Q.p ^ Q.exponent := prime_pow_two_le
  have hs2 : 2 ≤ Q'.p ^ Q'.exponent := prime_pow_two_le
  have hg4 : Nat.gcd 4 (Q.p ^ Q.exponent + 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hg1 : Nat.gcd 4 (Q.p ^ Q.exponent + 1) ≤ 4 := Nat.le_of_dvd (by norm_num) hg4
  refine YS05NonIso.dispatch hbX hbY ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨h, -⟩
    cases h
  · rintro ⟨-, h⟩
    norm_num at h
  · rintro ⟨-, -, -, h⟩
    norm_num at h
  · rintro ⟨h, -⟩
    rcases ht' with rfl | rfl <;> cases h
  · intro hpr
    rw [← hpr] at hEY hfY
    have hab : 6 * Q.exponent = 9 * Q'.exponent := hfX.symm.trans hfY
    exact same_B_U4_pab Q.prime_p Q.exponent_pos Q'.exponent_pos hab hg1 hd1 hEX hEY
  · intro hpr hp2 hr2
    have hpP := Q.prime_p
    have hpR := Q'.prime_p
    have hsodd : Odd (Q'.p ^ Q'.exponent) := Odd.pow (hpR.odd_of_ne_two hr2)
    have hps : ¬ Q.p ∣ Q'.p ^ Q'.exponent := YS05NonIso.pn_pow hpP hpR hpr
    by_cases h3 : Q.p = 3
    · have hfac : (Nat.card H).factorization 3 = 6 * Q.exponent := h3 ▸ hfX
      have hs3 : ¬ 3 ∣ Q'.p ^ Q'.exponent :=
        YS05NonIso.pn_pow (by norm_num) hpR (by omega)
      exact cross_p3_B hs2 hs3 hd4 hd1 hfac hEY
    · have hp5 : 5 ≤ Q.p := YS05NonIso.five_le hpP hp2 h3
      exact cross_ge5_B hpP hp5 hs2 hsodd hps hg4 hd4 (fx_U4_pos hq2) (fx_U4_lt hq2) hEX hEY

theorem core_U4_D {H : Type} [Group H] (Q Q' : TauCeti.PrimePower)
    (hvU : (TauCeti.LieTypeIndex.twistedA 3 Q).Valid)
    (eU : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 Q, hvU⟩)
    (hvD : (TauCeti.LieTypeIndex.D 4 Q').Valid) (eD : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D 4 Q', hvD⟩) :
    False := by
  obtain ⟨hbX, hEX, hfX⟩ := YS05NonIso.orderEq_U4 Q hvU eU
  have hbY := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (t := .POmegaPlus) (by decide)
    (CFSG.Models.lieModel_D 4 Q' hvD eD)
  obtain ⟨d, hd4, hd1, hEY, hfY⟩ := orderEq_D4 hbY
  have hq2 : 2 ≤ Q.p ^ Q.exponent := prime_pow_two_le
  have hs2 : 2 ≤ Q'.p ^ Q'.exponent := prime_pow_two_le
  have hg4 : Nat.gcd 4 (Q.p ^ Q.exponent + 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hg1 : Nat.gcd 4 (Q.p ^ Q.exponent + 1) ≤ 4 := Nat.le_of_dvd (by norm_num) hg4
  refine YS05NonIso.dispatch hbX hbY ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨h, -⟩
    cases h
  · rintro ⟨h, -⟩
    cases h
  · rintro ⟨-, -, h, -⟩
    cases h
  · rintro ⟨h, -⟩
    cases h
  · intro hpr
    rw [← hpr] at hEY hfY
    have hab : 6 * Q.exponent = 12 * Q'.exponent := hfX.symm.trans hfY
    exact same_D_U4_pab Q.prime_p Q'.exponent_pos hab hg1 hd1 hEX hEY
  · intro hpr hp2 hr2
    have hpP := Q.prime_p
    have hpR := Q'.prime_p
    have hsodd : Odd (Q'.p ^ Q'.exponent) := Odd.pow (hpR.odd_of_ne_two hr2)
    have hps : ¬ Q.p ∣ Q'.p ^ Q'.exponent := YS05NonIso.pn_pow hpP hpR hpr
    by_cases h3 : Q.p = 3
    · have hfac : (Nat.card H).factorization 3 = 6 * Q.exponent := h3 ▸ hfX
      have hs3 : ¬ 3 ∣ Q'.p ^ Q'.exponent :=
        YS05NonIso.pn_pow (by norm_num) hpR (by omega)
      exact cross_p3_D hs2 hs3 hd4 hd1 hfac hEY
    · have hp5 : 5 ≤ Q.p := YS05NonIso.five_le hpP hp2 h3
      exact cross_ge5_D hpP hp5 hs2 hsodd hps hg4 hd4 (fx_U4_pos hq2) (fx_U4_lt hq2) hEX hEY

theorem core_U4_D2 {H : Type} [Group H] (Q Q' : TauCeti.PrimePower)
    (hvU : (TauCeti.LieTypeIndex.twistedA 3 Q).Valid)
    (eU : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 Q, hvU⟩)
    (hvD : (TauCeti.LieTypeIndex.twistedD 4 Q').Valid)
    (eD : H ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedD 4 Q', hvD⟩) : False := by
  obtain ⟨hbX, hEX, hfX⟩ := YS05NonIso.orderEq_U4 Q hvU eU
  have hbY := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (t := .POmegaMinus) (by decide)
    (CFSG.Models.lieModel_twistedD 4 Q' hvD eD)
  obtain ⟨d, hd4, hd1, hEY, hfY⟩ := orderEq_D2_4 hbY
  have hq2 : 2 ≤ Q.p ^ Q.exponent := prime_pow_two_le
  have hs2 : 2 ≤ Q'.p ^ Q'.exponent := prime_pow_two_le
  have hg4 : Nat.gcd 4 (Q.p ^ Q.exponent + 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hg1 : Nat.gcd 4 (Q.p ^ Q.exponent + 1) ≤ 4 := Nat.le_of_dvd (by norm_num) hg4
  refine YS05NonIso.dispatch hbX hbY ?_ ?_ ?_ ?_ ?_ ?_
  · rintro ⟨h, -⟩
    cases h
  · rintro ⟨h, -⟩
    cases h
  · rintro ⟨-, -, h, -⟩
    cases h
  · rintro ⟨h, -⟩
    cases h
  · intro hpr
    rw [← hpr] at hEY hfY
    have hab : 6 * Q.exponent = 12 * Q'.exponent := hfX.symm.trans hfY
    exact same_D2_U4_pab Q.prime_p Q'.exponent_pos hab hg1 hd1 hEX hEY
  · intro hpr hp2 hr2
    have hpP := Q.prime_p
    have hpR := Q'.prime_p
    have hsodd : Odd (Q'.p ^ Q'.exponent) := Odd.pow (hpR.odd_of_ne_two hr2)
    have hps : ¬ Q.p ∣ Q'.p ^ Q'.exponent := YS05NonIso.pn_pow hpP hpR hpr
    by_cases h3 : Q.p = 3
    · have hfac : (Nat.card H).factorization 3 = 6 * Q.exponent := h3 ▸ hfX
      have hs3 : ¬ 3 ∣ Q'.p ^ Q'.exponent :=
        YS05NonIso.pn_pow (by norm_num) hpR (by omega)
      exact cross_p3_D2 hs2 hs3 hd4 hd1 hfac hEY
    · have hp5 : 5 ≤ Q.p := YS05NonIso.five_le hpP hp2 h3
      exact cross_ge5_D2 hpP hp5 hs2 hsodd hps hg4 hd4 (fx_U4_pos hq2) (fx_U4_lt hq2) hEX hEY

theorem _root_.CFSG.LocalAnalysis.GLTheoremA.H81FamilyDisjoint_holds : H81FamilyDisjoint := by
  intro H _ _ Q Q' hcat
  obtain ⟨hX, hY⟩ := hcat
  rcases hX with hA | hU
  · obtain ⟨hvA, ⟨eA⟩⟩ := YS05NonIso.catalogIs_onLie_eq hA
    rcases hY with hB | hD2 | hD
    · obtain ⟨hvB, ⟨eB⟩⟩ := YS05NonIso.catalogIs_onLie_eq hB
      exact core_A3_B Q Q' hvA eA hvB eB
    · obtain ⟨hvD2, ⟨eD2⟩⟩ := YS05NonIso.catalogIs_onLie_eq hD2
      exact core_A3_D2 Q Q' hvA eA hvD2 eD2
    · obtain ⟨hvD, ⟨eD⟩⟩ := YS05NonIso.catalogIs_onLie_eq hD
      exact core_A3_D Q Q' hvA eA hvD eD
  · obtain ⟨hvU, ⟨eU⟩⟩ := YS05NonIso.catalogIs_onLie_eq hU
    rcases hY with hB | hD2 | hD
    · obtain ⟨hvB, ⟨eB⟩⟩ := YS05NonIso.catalogIs_onLie_eq hB
      exact core_U4_B Q Q' hvU eU hvB eB
    · obtain ⟨hvD2, ⟨eD2⟩⟩ := YS05NonIso.catalogIs_onLie_eq hD2
      exact core_U4_D2 Q Q' hvU eU hvD2 eD2
    · obtain ⟨hvD, ⟨eD⟩⟩ := YS05NonIso.catalogIs_onLie_eq hD
      exact core_U4_D Q Q' hvU eU hvD eD

end Cert

end CFSG.LocalAnalysis.GLTheoremA.SFM11
