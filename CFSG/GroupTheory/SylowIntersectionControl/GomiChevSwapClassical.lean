module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevOrbitSwapDefs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevNodeSwap
import CFSG.LieType.Universal.Unitary.RootGroupCardRankTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.GroupTheory

open CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal.Spin

variable {K : Type} [Group K] [Finite K]

theorem gomiSwapTop_of_lie_A {d : TauCeti.ValidLieTypeIndex} {r : ℕ} {q : TauCeti.PrimePower}
    (hd : d.1 = .A r q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiSwapTop K := by
  obtain ⟨d, hv⟩ := d
  have hd' : d = .A r q := hd
  subst hd'
  by_cases h2 : r = 2
  · subst h2
    exact gomiSwapTop_of_isGomiL3 ⟨⟨.A 2 q, hv⟩, Or.inl ⟨q, hq, rfl⟩, ⟨e⟩⟩
  · have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
    have hr : (CFSG.LieType.Universal.SpecialLinear.rootDatum r
        (GaloisField q.p q.exponent)).rank ≠ 2 := by
      show r ≠ 2
      exact h2
    exact (gomiNoAtomSwap_of_borelQuotient (borelQuotient_sl (m := r)
      ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans
        e.symm)) hr).gomiSwapTop

theorem gomiNoAtomSwap_of_lie_twistedA {d : TauCeti.ValidLieTypeIndex} {r : ℕ}
    {q : TauCeti.PrimePower} (hd : d.1 = .twistedA r q) (hq : q.p = 2)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : GomiNoAtomSwap K := by
  obtain ⟨d, hv⟩ := d
  have hd' : d = .twistedA r q := hd
  subst hd'
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hq] at h
  obtain ⟨hadm, F, hF, hFfin, hcard, ⟨e'⟩⟩ := h
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  have h2r : 2 ≤ r + 1 := by have := hadm.2.2.1; omega
  have hB := borelQuotient_su (n := r + 1) hcard h2r ζ hζ e'
  by_cases h3 : r = 3
  · subst h3
    exact gomiNoAtomSwap_of_borelQuotient_card_ne (i := (0 : Fin 2)) (j := (1 : Fin 2)) hB
      (CFSG.LieType.Universal.Unitary.card_rootGroup_four_zero_ne_one hcard)
  by_cases h4 : r = 4
  · subst h4
    exact gomiNoAtomSwap_of_borelQuotient_card_ne (i := (0 : Fin 2)) (j := (1 : Fin 2)) hB
      (CFSG.LieType.Universal.Unitary.card_rootGroup_five_zero_ne_one hcard)
  · exact gomiNoAtomSwap_of_borelQuotient hB (by
      show (r + 1) / 2 ≠ 2
      omega)

theorem gomiSwapTop_of_lie_B {d : TauCeti.ValidLieTypeIndex} {r : ℕ} {q : TauCeti.PrimePower}
    (hd : d.1 = .B r q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiSwapTop K := by
  obtain ⟨d, hv⟩ := d
  have hd' : d = .B r q := hd
  subst hd'
  by_cases h2 : r = 2
  · subst h2
    exact gomiSwapTop_of_isGomiSp4 (Or.inr ⟨⟨.B 2 q, hv⟩, ⟨q, hq, rfl⟩, ⟨e⟩⟩)
  · have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    have h3 : 3 ≤ r := by omega
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq h3 e
    rw [hq] at h
    obtain ⟨hadm, F, hF, hFfin, hcard, ⟨e'⟩⟩ := h
    have := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := q.exponent)
      (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    exact (gomiNoAtomSwap_of_borelQuotient (borelQuotient_sp e') (by
      show r ≠ 2
      exact h2)).gomiSwapTop

theorem gomiNoAtomSwap_of_lie_D {d : TauCeti.ValidLieTypeIndex} {r : ℕ} {q : TauCeti.PrimePower}
    (hd : d.1 = .D r q) (hq : q.p = 2) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiNoAtomSwap K := by
  obtain ⟨d, hv⟩ := d
  have hd' : d = .D r q := hd
  subst hd'
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq e
  rw [hq] at h
  obtain ⟨hadm, F, hF, hFfin, hcard, ⟨e'⟩⟩ := h
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := q.exponent)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn : 3 ≤ r := by have := hadm.2.2; omega
  have : NeZero r := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus r F)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadPlus)
  exact gomiNoAtomSwap_of_borelQuotient (borelQuotient_spinPlus hn e') (by
    show r ≠ 2
    omega)

theorem gomiNoAtomSwap_of_lie_twistedD {d : TauCeti.ValidLieTypeIndex} {r : ℕ}
    {q : TauCeti.PrimePower} (hd : d.1 = .twistedD r q) (hq : q.p = 2)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : GomiNoAtomSwap K := by
  obtain ⟨d, hv⟩ := d
  have hd' : d = .twistedD r q := hd
  subst hd'
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq e
  rw [hq] at h
  obtain ⟨hadm, F, hF, hFfin, hcard, b, c, hbc, ⟨e'⟩⟩ := h
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := q.exponent)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn : 4 ≤ r := by have := hadm.2.2; omega
  have : Finite (spinGroup (quadMinus r F b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadMinus hbc)
  exact gomiNoAtomSwap_of_borelQuotient (borelQuotient_spinMinus hbc hn e') (by
    show r - 1 ≠ 2
    omega)

end CFSG.GroupTheory
