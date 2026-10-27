module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432WitG2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Yardstones.Md0ec50421ce4 CFSG.Open

abbrev TD4Model : Type :=
  DerivedCentralQuotient
    (twistedFixedGroup TwistTag.D4 (GaloisField 3 3) (frobenius (GaloisField 3 3) 3))

@[expose] def TD4Res : Prop :=
  ∃ V E : Subgroup TD4Model, V ≠ ⊥ ∧ IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set TD4Model) ∧
    IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4

theorem hasTwoLocalWitness_of_mulEquiv_exists {S T : Type} [Group S] [Group T] [Finite S] {r : ℕ}
    (e : S ≃* T)
    (h : ∃ V E : Subgroup T, V ≠ ⊥ ∧ IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set T) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r) :
    HasTwoLocalWitness S r := by
  obtain ⟨V, E, hV, hV2, hE, hEab, hEc⟩ := h
  refine ⟨V.map e.symm.toMonoidHom, E.map e.symm.toMonoidHom, ?_, hV2.map _, ?_, ?_, ?_⟩
  · exact fun hbot => hV ((Subgroup.map_eq_bot_iff_of_injective V e.symm.injective).1 hbot)
  · calc E.map e.symm.toMonoidHom
        ≤ (Subgroup.normalizer (V : Set T)).map e.symm.toMonoidHom := Subgroup.map_mono hE
      _ = Subgroup.normalizer ((V.map e.symm.toMonoidHom : Subgroup S) : Set S) :=
          Subgroup.map_equiv_normalizer_eq V e.symm
  · exact CFSG.LocalAnalysis.GLTheoremA.H1420.WitD4.isElemAbelian_map_inj _ hEab
  · rw [Subgroup.card_map_of_injective e.symm.injective]; exact hEc

theorem i1432WitTD4_of_residual
    (hres : TD4Res) : ∀ (S : Type) [Group S] [Finite S], catalogIs S (isTD4of 3) →
      HasTwoLocalWitness S 4 := by
  intro S _ _ hS
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex
    (P := fun | .trialityD4 q => q.card = 3 | _ => False) hS
  cases d with
  | trialityD4 q =>
    have hq : q.card = 3 := hP
    have hp2 : q.p ≠ 2 := by
      intro h2
      have hdvd : 2 ∣ q.card := by
        rw [TauCeti.PrimePower.card_def, h2]
        exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.1 q.exponent_pos)
      rw [hq] at hdvd
      norm_num at hdvd
    have hK : Nat.card (GaloisField 3 3) = q.card ^ TwistTag.D4.order := by
      rw [GaloisField.card 3 3 (by norm_num), hq]
      rfl
    obtain ⟨eK⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2
      (GaloisField 3 3) hK (frobenius (GaloisField 3 3) 3)
      (fun x => by rw [frobenius_def, hq])
    exact hasTwoLocalWitness_of_mulEquiv_exists (e.trans eK.symm) hres
  | _ => exact (hP : False).elim

theorem i1432WitG2_of_residuals
    (hcomm : CFSG.LocalAnalysis.GLTheoremA.H1420.WitG2.G2CommRes)
    (hdir : CFSG.LocalAnalysis.GLTheoremA.H1420.WitG2.G2DirectRes) (hres : TD4Res) :
    I1432WitG2 := by
  intro S _ _ h
  rcases h with h | h | h
  · exact CFSG.LocalAnalysis.GLTheoremA.H1420.WitG2.i1432WitG2_G2 hcomm hdir S h
  · exact i1432WitD4Three S h
  · exact i1432WitTD4_of_residual hres S h

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
