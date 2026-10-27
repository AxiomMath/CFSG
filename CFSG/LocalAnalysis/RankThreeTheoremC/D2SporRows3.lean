module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporOpen3
import CFSG.Sporadic.NativeFinite
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Tits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Co2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Co3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2J2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Ru
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreHe
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreJ4Row
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreON
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreThRow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicRowData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Blueprint

set_option linter.unusedSectionVars false


theorem d2VacuousAt_of_rows {s : TauCeti.SporadicName} (hs : s ≠ .M) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [Finite (NativeSporadic.Carrier s)] (hsq : p ^ 2 ∣ d2SporadicOrder s)
    (hrow : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier s) →
      D2IndexDatumPlus L p) : D2VacuousAt (.sporadic s) p := by
  have hfree : D2FreeCaseAt (.sporadic s) fun q => q = p :=
    d2FreeCaseAt_sporadic_of_rows s hs (fun q hq hq2 hsq' hPq L _ _ hL => by
      subst hPq; exact hrow L hL)
  exact fun X _ _ R A X₀ K hK he => hfree X p rfl R A X₀ K hK he

theorem d2VacuousAt_J2_three : D2VacuousAt (.sporadic .J2) 3 := by
  have : Finite (NativeSporadic.Carrier .J2) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .J2 (by decide)
  exact d2VacuousAt_of_rows (by decide) Nat.prime_three (by norm_num)
    (by norm_num [d2SporadicOrder])
    (d2IndexDatumPlus_carrier_of_coreSup (s := .J2) (by decide) Nat.prime_three (by norm_num)
      CFSG.AGLEmbedding.glbCore_sup_J2_three)

theorem d2VacuousAt_He_three : D2VacuousAt (.sporadic .He) 3 := by
  have : Finite (NativeSporadic.Carrier .He) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .He (by decide)
  exact d2VacuousAt_of_rows (by decide) Nat.prime_three (by norm_num)
    (by norm_num [d2SporadicOrder])
    (fun L _ _ he => Or.inl (d2IndexDatum_carrier_of_core (s := .He) (by decide) Nat.prime_three
      (by norm_num) glbCore_He_three L he))

theorem d2VacuousAt_He_seven : D2VacuousAt (.sporadic .He) 7 := by
  have : Finite (NativeSporadic.Carrier .He) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .He (by decide)
  exact d2VacuousAt_of_rows (by decide) Nat.prime_seven (by norm_num)
    (by norm_num [d2SporadicOrder])
    (fun L _ _ he => Or.inl (d2IndexDatum_carrier_of_core (s := .He) (by decide) Nat.prime_seven
      (by norm_num) glbCore_He_seven L he))

theorem d2VacuousAt_ONan_seven : D2VacuousAt (.sporadic .ONan) 7 := by
  have : Finite (NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .ONan (by decide)
  exact d2VacuousAt_of_rows (by decide) Nat.prime_seven (by norm_num)
    (by norm_num [d2SporadicOrder])
    (fun L _ _ he => Or.inl (d2IndexDatum_carrier_of_core (s := .ONan) (by decide) Nat.prime_seven
      (by norm_num) glbCore_ON_seven L he))

theorem d2VacuousAt_Ru_five : D2VacuousAt (.sporadic .Ru) 5 := by
  have : Finite (NativeSporadic.Carrier .Ru) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .Ru (by decide)
  exact d2VacuousAt_of_rows (by decide) Nat.prime_five (by norm_num)
    (by norm_num [d2SporadicOrder])
    (fun L _ _ he => Or.inl (d2IndexDatum_carrier_of_core (s := .Ru) (by decide) Nat.prime_five
      (by norm_num) CFSG.AGLEmbedding.glbCore_Ru_five L he))

theorem d2VacuousAt_Ru_three : D2VacuousAt (.sporadic .Ru) 3 := by
  have : Finite (NativeSporadic.Carrier .Ru) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .Ru (by decide)
  exact d2VacuousAt_of_rows (by decide) Nat.prime_three (by norm_num)
    (by norm_num [d2SporadicOrder])
    (d2IndexDatumPlus_carrier_of_coreSup (s := .Ru) (by decide) Nat.prime_three (by norm_num)
      CFSG.AGLEmbedding.glbCore_sup_Ru_three)

theorem d2VacuousAt_Co2_five : D2VacuousAt (.sporadic .Co2) 5 := by
  have : Finite (NativeSporadic.Carrier .Co2) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .Co2 (by decide)
  exact d2VacuousAt_of_rows (by decide) Nat.prime_five (by norm_num)
    (by norm_num [d2SporadicOrder])
    (d2IndexDatumPlus_carrier_of_coreSup (s := .Co2) (by decide) Nat.prime_five (by norm_num)
      CFSG.AGLEmbedding.glbCore_sup_Co2_five)

theorem d2VacuousAt_Co3_five : D2VacuousAt (.sporadic .Co3) 5 := by
  have : Finite (NativeSporadic.Carrier .Co3) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .Co3 (by decide)
  exact d2VacuousAt_of_rows (by decide) Nat.prime_five (by norm_num)
    (by norm_num [d2SporadicOrder])
    (d2IndexDatumPlus_carrier_of_coreSup (s := .Co3) (by decide) Nat.prime_five (by norm_num)
      CFSG.AGLEmbedding.glbCore_sup_Co3_five)

theorem d2VacuousAt_J4_three : D2VacuousAt (.sporadic .J4) 3 := by
  have : Finite (NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .J4 (by decide)
  exact d2VacuousAt_of_rows (by decide) Nat.prime_three (by norm_num)
    (by norm_num [d2SporadicOrder])
    (fun L _ _ he => Or.inl (d2IndexDatum_J4_three L he))

theorem d2VacuousAt_Th_five : D2VacuousAt (.sporadic .Th) 5 := by
  have : Finite (NativeSporadic.Carrier .Th) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .Th (by decide)
  exact d2VacuousAt_of_rows (by decide) Nat.prime_five (by norm_num)
    (by norm_num [d2SporadicOrder])
    (fun L _ _ he => Or.inl (d2IndexDatum_Th_five L he))

theorem d2VacuousAt_sporadicRows3 :
    ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p := by
  intro s p h
  simp only [d2SporadicRows3, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [d2VacuousAt_J2_three, d2VacuousAt_He_three, d2VacuousAt_Ru_three, d2VacuousAt_Ru_five,
    d2VacuousAt_Co2_five, d2VacuousAt_Co3_five, d2VacuousAt_He_seven, d2VacuousAt_ONan_seven,
    d2VacuousAt_J4_three, d2VacuousAt_Th_five]

theorem d2VacuousAt_tits_three (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .tits) :
    D2VacuousAt (.lie d) 3 :=
  fun X _ _ R A X₀ K hK he =>
    d2FreeCaseAt_tits_three kFactTitsThreeCore d hd X 3 rfl R A X₀ K hK he

end CFSG.LocalAnalysis.RankThreeTheoremC
