module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsBase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSU
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dTitsProof

open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Open

section SU

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

theorem rankOne_not_solvable_su (hf : 2 ≤ f) {n : ℕ} (hn : 3 ≤ n) (i : Fin (n / 2)) :
    ¬ Group.IsSolvable (rankOne (rootDatum hF n).rootGroup i) := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  by_cases hk : i.val + 1 < n / 2
  · have hF4 : 4 ≤ Nat.card F := by
      rw [hF]
      nlinarith
    exact rankOne_not_solvable_of_hasSL2Node hF4 (hasSL2Node_su_short hF hk)
  · obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
    have hcard : Nat.card (fixedSubfield F 2 f) = 2 ^ f := card_fixedSubfield hF
    have hF4 : 4 ≤ Nat.card (fixedSubfield F 2 f) := by
      rw [hcard]
      exact hq4
    by_cases he : Even n
    · obtain ⟨e⟩ := nonempty_rankOne_last_even_mulEquiv hF he (by omega) hk
      exact not_isSolvable_of_sl2_hom hF4
        (e.symm.toMonoidHom.comp (hypEquiv hζ0 hζ).toMonoidHom)
        (e.symm.injective.comp (hypEquiv hζ0 hζ).injective)
    · obtain ⟨e⟩ := nonempty_rankOne_last_odd_mulEquiv hF he hn hk
      have hk' : ∀ c ∈ fixedSubfield F 2 f, unitaryInvolution F 2 f c = c := fun c hc =>
        mem_fixedSubfield.1 hc
      exact not_isSolvable_of_sl2_hom hF4
        (e.symm.toMonoidHom.comp (blk3Hom (fixedSubfield F 2 f) hk'))
        (e.symm.injective.comp (blk3Hom_injective (fixedSubfield F 2 f) hk'))

end SU

open CFSG.AGLEmbedding.ParabHub in
theorem solvOver_of_model_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel Y .PSU n 2 f) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    NQCat.SolvOver Y U := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  exact solvOver_of_borelQuotient (borelQuotient_su hcard (by omega) ζ hζ e)
    (fun i => rankOne_not_solvable_su hcard hf hn i) hU

theorem p_eq_two_of_card_four {Q : TauCeti.PrimePower} (hQ4 : Q.card = 4) :
    Q.p = 2 ∧ Q.exponent = 2 := by
  have hpe : Q.p ^ Q.exponent = 4 := by rw [← TauCeti.PrimePower.card_def, hQ4]
  have hp2 : Q.p = 2 := by
    have hdvd : Q.p ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = Q.p ^ Q.exponent by rw [hpe]; norm_num]
      exact dvd_pow_self _ Q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq Q.prime_p Nat.prime_two).1 (Q.prime_p.dvd_of_dvd_pow hdvd)
  refine ⟨hp2, ?_⟩
  rw [hp2] at hpe
  exact Nat.pow_right_injective (le_refl 2) (by rw [hpe]; norm_num : 2 ^ Q.exponent = 2 ^ 2)

theorem solvOver_of_typeTwistedA3 {S : Type} [Group S] [Finite S] {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 Q).Valid) (hQ : Q.p = 2) (hQ2 : Q.card ≠ 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 3 Q, hv⟩) {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) : NQCat.SolvOver S U := by
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 Q hv e
  rw [hQ] at hm
  exact solvOver_of_model_psu (two_le_exponent_of_p_two hQ hQ2) hm hU

theorem solvOver_of_typeTwistedA4 {S : Type} [Group S] [Finite S] {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 4 Q).Valid) (hQ4 : Q.card = 4)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 4 Q, hv⟩) {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) : NQCat.SolvOver S U := by
  obtain ⟨hp2, he2⟩ := p_eq_two_of_card_four hQ4
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 Q hv e
  rw [hp2, he2] at hm
  exact solvOver_of_model_psu le_rfl hm hU

end K21dTitsProof

end CFSG.LocalAnalysis.RankThreeUC.S15
