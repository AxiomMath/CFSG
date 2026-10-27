module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFacts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactBorel
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TenFifteenKFactSmall
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Families

theorem parabolicClassFixed_sl {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} {Y : Type}
    [Group Y] [Finite Y] [IsSimpleGroup Y]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) : ParabolicClassFixed Y :=
  parabolicClassFixed_of_borelQuotient (borelQuotient_sl e)

theorem parabolicClassFixed_sl_index {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] (r : ℕ)
    (q : TauCeti.PrimePower) (hq : q.p = 2) (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (e : Y ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A r q, hv⟩) :
    ParabolicClassFixed Y := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  exact parabolicClassFixed_sl
    ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans e.symm)

theorem parabolicClassFixed_of_model_psu {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) : ParabolicClassFixed Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  exact parabolicClassFixed_of_borelQuotient (borelQuotient_su hcard (by omega) ζ hζ e)

theorem parabolicClassFixed_of_model_psp {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) : ParabolicClassFixed Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact parabolicClassFixed_of_borelQuotient (borelQuotient_sp e)

theorem parabolicClassFixed_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) : ParabolicClassFixed Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (CFSG.LieType.Universal.Spin.quadPlus n F)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact parabolicClassFixed_of_borelQuotient (borelQuotient_spinPlus hn3 e)

theorem parabolicClassFixed_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) : ParabolicClassFixed Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (CFSG.LieType.Universal.Spin.quadMinus n F b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadMinus hirr)
  exact parabolicClassFixed_of_borelQuotient (borelQuotient_spinMinus hirr (by omega) e)

theorem parabolicClassFixed_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type} [Group Y]
    [Finite Y] [IsSimpleGroup Y] (e : Y ≃* CFSG.Blueprint.AdjointQuotient .G2 K) :
    ParabolicClassFixed Y :=
  parabolicClassFixed_of_borelQuotient (borelQuotient_g2 e)

end Families

section Catalog


theorem parabolicClassFixed_lieIndex {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : ParabolicClassFixed Y := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact parabolicClassFixed_sl_index r q hd hv e
  | twistedA r q =>
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    change q.p = 2 at hd
    rw [hd] at h
    exact parabolicClassFixed_of_model_psu h
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact parabolicClassFixed_of_model_psp h
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact parabolicClassFixed_of_model_psp h
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact parabolicClassFixed_of_model_pomegaPlus h
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact parabolicClassFixed_of_model_pomegaMinus h
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    exact parabolicClassFixed_g2 (e.trans b.symm)
  | _ => exact hd.elim


theorem kFactLieParabolicClass_holds : KFactLieParabolicClass := by
  intro Y _ _ hsimple hY P hP α hα
  have hfix : ParabolicClassFixed Y := by
    rcases hY with ⟨d, hd, ⟨e⟩⟩ | h2 | h3
    · exact parabolicClassFixed_lieIndex d hd e
    · exact parabolicClassFixed_of_card_outer_le_four (card_outer_le_four_of_small (Or.inl h2))
    · exact parabolicClassFixed_of_card_outer_le_four (card_outer_le_four_of_small (Or.inr h3))
  exact hfix P hP α hα

end Catalog

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
