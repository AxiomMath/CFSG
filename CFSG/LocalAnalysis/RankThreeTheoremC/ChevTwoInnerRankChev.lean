module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankCover
public import CFSG.LieType.Chevalley.CharTwoRank
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeF4
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeE6E7

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley

section SL2

variable {K : Type} [Field K]

theorem sl2Upper_one_mul_self (h2 : (1 : K) + 1 = 0) :
    sl2Upper (1 : K) * sl2Upper 1 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper]
  simp only [Matrix.mul_fin_two]
  simp [h2]
  exact Matrix.one_fin_two.symm

theorem sl2Lower_one_mul_self (h2 : (1 : K) + 1 = 0) :
    sl2Lower (1 : K) * sl2Lower 1 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower]
  simp only [Matrix.mul_fin_two]
  simp [h2]
  exact Matrix.one_fin_two.symm

theorem sl2Upper_conj_upper_mul_lower (h2 : (1 : K) + 1 = 0) :
    sl2Upper (1 : K) * (sl2Upper 1 * sl2Lower 1) * (sl2Upper 1)⁻¹ =
      (sl2Upper 1 * sl2Lower 1)⁻¹ := by
  have hu : (sl2Upper (1 : K))⁻¹ = sl2Upper 1 :=
    inv_eq_of_mul_eq_one_right (sl2Upper_one_mul_self h2)
  have hl : (sl2Lower (1 : K))⁻¹ = sl2Lower 1 :=
    inv_eq_of_mul_eq_one_right (sl2Lower_one_mul_self h2)
  rw [mul_inv_rev, hu, hl, ← mul_assoc, sl2Upper_one_mul_self h2, one_mul]

end SL2

section Inversion

variable {τ : Tag} {K : Type} [Field K]

theorem rankOne_conj_rankOneZ {i k : Fin τ.rank} (hk : τ.cartan i k = -1)
    (h2 : (1 : K) + 1 = 0) :
    (rootOperatorFamily τ).eltElement (simpleRoot τ i) 1 * rankOneZ (K := K) i *
      ((rootOperatorFamily τ).eltElement (simpleRoot τ i) 1)⁻¹ = (rankOneZ (K := K) i)⁻¹ := by
  obtain ⟨φ, -, hu, hl⟩ := exists_sl2_hom (K := K) (rootOperatorFamily τ) hk
  have hz : rankOneZ (K := K) i = φ (sl2Upper 1 * sl2Lower 1) := by
    rw [map_mul, hu, hl]
    rfl
  rw [hz, ← hu]
  have := congrArg φ (sl2Upper_conj_upper_mul_lower h2)
  simpa only [map_mul, map_inv] using this

theorem elemA_conj_elemZ {n : ℕ} (W : RootWitness τ n) (i : Fin n) {k : Fin τ.rank}
    (hk : τ.cartan (W.simple i) k = -1) (h2 : (1 : K) + 1 = 0) :
    W.elemA K i * W.elemZ K i * (W.elemA K i)⁻¹ = (W.elemZ K i)⁻¹ := by
  have h := rankOne_conj_rankOneZ (K := K) hk h2
  set nn := nrep τ K ((coxeterSystem τ).wordProd (W.word i))
  change nn * (rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1 * nn⁻¹ *
    (nn * rankOneZ (W.simple i) * nn⁻¹) *
    (nn * (rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1 * nn⁻¹)⁻¹ =
    (nn * rankOneZ (W.simple i) * nn⁻¹)⁻¹
  calc _ = nn * ((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1 *
        rankOneZ (K := K) (W.simple i) *
        ((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1)⁻¹) * nn⁻¹ := by
        group
    _ = nn * (rankOneZ (K := K) (W.simple i))⁻¹ * nn⁻¹ := by rw [h]
    _ = _ := by group

end Inversion

section CharTwo

theorem centralCoverFour_adjointGroup_of_witness {τ : Tag} (W : RootWitness τ 4)
    (hW : W.check = true) (hO : W.orthoCheck = true) (nbr : Fin 4 → Fin τ.rank)
    (hnbr : ∀ i, τ.cartan (W.simple i) (nbr i) = -1) {K : Type} [Field K] [CharP K 2] :
    CentralCoverFour (adjointGroup τ K) := by
  have h2 : (1 : K) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact CharP.cast_eq_zero K 2
  obtain ⟨hf, hZA, hZZ⟩ := RootWitness.charTwo_facts hW hO nbr hnbr (K := K)
  refine centralCoverFour_of_inverters (W.elemZ K) (W.elemA K) (fun i j => ?_) (fun i => ?_)
    (fun i => elemA_conj_elemZ W i (hnbr i) h2) (fun i j hij => ?_)
  · by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact hZZ i j hij
  · refine orderOf_eq_prime (hf i).1 fun h => (hf i).2.1 ?_
    rw [h]
    exact Commute.one_left _
  · rw [mul_inv_eq_iff_eq_mul]
    exact (hZA i j hij).eq.symm

theorem centralCoverFour_adjointGroup_of_charTwo {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [CharP K 2] :
    CentralCoverFour (adjointGroup τ K) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact centralCoverFour_adjointGroup_of_witness witnessF4 witnessF4_check witnessF4_orthoCheck
      ![(0 : Fin 4), (0 : Fin 4), (0 : Fin 4), (1 : Fin 4)] (by decide)
  · exact centralCoverFour_adjointGroup_of_witness witnessE6 witnessE6_check witnessE6_orthoCheck
      ![(1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (2 : Fin 6)] (by decide)
  · exact centralCoverFour_adjointGroup_of_witness witnessE7 witnessE7_check witnessE7_orthoCheck
      ![(5 : Fin 7), (3 : Fin 7), (0 : Fin 7), (3 : Fin 7)] (by decide)
  · exact centralCoverFour_adjointGroup_of_witness witnessE8 witnessE8_check witnessE8_orthoCheck
      ![(6 : Fin 8), (4 : Fin 8), (1 : Fin 8), (3 : Fin 8)] (by decide)

theorem centralCoverFour_adjointQuotient_of_charTwo {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2] :
    CentralCoverFour (AdjointQuotient τ K) :=
  CentralCoverFour.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot).symm (centralCoverFour_adjointGroup_of_charTwo hτ)

end CharTwo

section F4Two

theorem centralCoverFour_F4Two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    CentralCoverFour (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.F4 q, hv⟩) := by
  have hK : Nat.card (ZMod 2) = q.card := by
    rw [Nat.card_zmod, TauCeti.PrimePower.card_def, hp, he, pow_one]
  obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hp (ZMod 2) hK
  exact CentralCoverFour.of_mulEquiv e (centralCoverFour_adjointQuotient_of_charTwo (Or.inl rfl))

end F4Two

section E6Two

theorem centralCoverFour_E6Two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    CentralCoverFour (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.E6 q, hv⟩) := by
  have hK : Nat.card (ZMod 2) = q.card := by
    rw [Nat.card_zmod, TauCeti.PrimePower.card_def, hp, he, pow_one]
  obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hp (ZMod 2) hK
  exact CentralCoverFour.of_mulEquiv e
    (centralCoverFour_adjointQuotient_of_charTwo (Or.inr (Or.inl rfl)))

end E6Two

end CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank
