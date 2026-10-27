module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalHub
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeG2
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank

theorem radicalSelfNormOver_of_model_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 f) : RadicalSelfNormOver Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact radicalSelfNormOver_of_borelQuotient
    (borelQuotient_sl ((projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm))

theorem radicalSelfNormOver_of_model_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) : RadicalSelfNormOver Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact radicalSelfNormOver_of_borelQuotient (borelQuotient_sp e)

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
theorem radicalSelfNormOver_of_model_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) : RadicalSelfNormOver Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 f) n) := Finite.of_injective _ Subtype.val_injective
  exact radicalSelfNormOver_of_borelQuotient (borelQuotient_su hcard (by omega) ζ hζ e)

open CFSG.LieType.Universal.Spin in
theorem radicalSelfNormOver_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) : RadicalSelfNormOver Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact radicalSelfNormOver_of_borelQuotient (borelQuotient_spinPlus hn3 e)

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted in
theorem radicalSelfNormOver_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) : RadicalSelfNormOver Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact radicalSelfNormOver_of_borelQuotient (borelQuotient_spinMinus hirr hn e)

theorem radicalSelfNormOver_alt_eight {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* alternatingGroup (Fin 8)) : RadicalSelfNormOver Y := by
  rcases (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff Y).2 ⟨e⟩ with
    ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact radicalSelfNormOver_of_model_psl h
  all_goals exact absurd h0 (by norm_num)

section Catalog


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem radicalSelfNormOver_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type}
    [Group Y] [Finite Y] (e : Y ≃* AdjointQuotient .G2 K) : RadicalSelfNormOver Y := by
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  exact radicalSelfNormOver_of_borelQuotient (borelQuotient_g2 e)

theorem radicalSelfNormOver_of_index {Y : Type} [Group Y] [Finite Y]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : RadicalSelfNormOver Y := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hd] at h
    exact radicalSelfNormOver_of_model_psl h
  | twistedA r q =>
    change q.p = 2 at hd
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hd] at h
    exact radicalSelfNormOver_of_model_psu h
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact radicalSelfNormOver_of_model_psp h
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact radicalSelfNormOver_of_model_psp h
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact radicalSelfNormOver_of_model_pomegaPlus h
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact radicalSelfNormOver_of_model_pomegaMinus h
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    exact radicalSelfNormOver_g2 (e.trans b.symm)
  | _ => exact hd.elim

end Catalog

end CFSG.AGLEmbedding.ToralCensus
