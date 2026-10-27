module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporBase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicRows
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreFi24Row
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Blueprint CFSG.AGLEmbeddingD2

@[expose] def SporProvedRows : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), (s, p) ∈ d2SporadicProvedList →
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier s) →
      D2IndexDatumPlus L p

@[expose] def SporFi24SevenRow : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Fi24Prime) →
    D2IndexDatum L 7

theorem smallIdentSporAt_of_rows (hrows : SporProvedRows) (hFi : SporFi24SevenRow)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M →
      Nat.card (NativeSporadic.Carrier s) = d2SporadicOrder s)
    (s : TauCeti.SporadicName) (hs : s ≠ .M) (hHS5 : SporGammaOneAt .HS 5)
    (hB7 : SporGammaOneAt .B 7) : SmallIdentSporAt s := by
  intro K _ _ _ _ ⟨e⟩ p hp hp2 T hT hΓ hr
  obtain ⟨f⟩ := hbr s
  have e' : K ≃* NativeSporadic.Carrier s := e.trans f.symm
  by_cases hsq : p ^ 2 ∣ d2SporadicOrder s
  · rcases (d2SporadicSq_iff s p).1 ⟨hs, hp, hp2, hsq⟩ with hpr | hleaf | hopen
    · exact (false_of_d2DatumPlus hp hp2 (hrows s p hpr K ⟨e'⟩) T hT hΓ hr).elim
    · simp only [d2SporadicLeafList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hleaf
      rcases hleaf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨e⟩)⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ⟨e⟩⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr ⟨e⟩⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨e⟩)⟩))))
    · simp only [d2SporadicOpenList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hopen
      rcases hopen with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (hHS5 K ⟨e⟩ T) hΓ
      · exact (false_of_d2DatumPlus hp hp2 (Or.inl (hFi K ⟨e'⟩)) T hT hΓ hr).elim
      · exact absurd (hB7 K ⟨e⟩ T) hΓ
  · refine absurd (isCyclic_sylow_of_not_sq_dvd hp T ?_) hT
    rwa [Nat.card_congr e'.toEquiv, hcard s hs]

set_option linter.unusedSectionVars false

section Rows


theorem sporProvedRows : SporProvedRows := by
  intro s p h L _ _ ⟨e⟩
  simp only [d2SporadicProvedList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
    or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (d2IndexDatum_M22_three e)
  · exact Or.inl (d2IndexDatum_M23_three e)
  · exact Or.inl (d2IndexDatum_J2_five e)
  · exact Or.inl (d2IndexDatum_He_five e)
  · exact Or.inl (d2IndexDatum_Suz_five e)
  · exact Or.inl (d2IndexDatum_Th_seven e)
  · exact Or.inl (d2IndexDatum_HS_three e)
  · exact Or.inl (d2IndexDatum_Fi23_five e)
  · exact Or.inl (d2IndexDatum_Co1_seven e)
  · exact Or.inl (d2IndexDatum_Fi24Prime_five e)
  · exact Or.inl (d2IndexDatum_carrier_of_core (s := .M12) (by decide) Nat.prime_three
      (by norm_num) CFSG.AGLEmbedding.glbCore_M12_three L ⟨e⟩)
  · exact d2IndexDatumPlus_carrier_of_coreSup (s := .M24) (by decide) Nat.prime_three
      (by norm_num) CFSG.AGLEmbedding.glbCore_sup_M24_three L ⟨e⟩
  · exact Or.inl (d2IndexDatum_carrier_of_pRank (s := .J3) (by decide) Nat.prime_three
      (by norm_num) CFSG.AGLEmbedding.three_le_pRank_J3_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_carrier_of_pRank (s := .McL) (by decide) Nat.prime_three
      (by norm_num) CFSG.AGLEmbedding.three_le_pRank_McL_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_carrier_of_pRank (s := .Co3) (by decide) Nat.prime_three
      (by norm_num) CFSG.AGLEmbedding.three_le_pRank_Co3_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_carrier_of_pRank (s := .Co2) (by decide) Nat.prime_three
      (by norm_num) CFSG.AGLEmbedding.three_le_pRank_Co2_three L ⟨e⟩)
  · exact d2IndexDatumPlus_carrier_of_coreSup (s := .J2) (by decide) Nat.prime_three
      (by norm_num) CFSG.AGLEmbedding.glbCore_sup_J2_three L ⟨e⟩
  · exact Or.inl (d2IndexDatum_carrier_of_core (s := .He) (by decide) Nat.prime_three
      (by norm_num) glbCore_He_three L ⟨e⟩)
  · exact d2IndexDatumPlus_carrier_of_coreSup (s := .Ru) (by decide) Nat.prime_three
      (by norm_num) CFSG.AGLEmbedding.glbCore_sup_Ru_three L ⟨e⟩
  · exact Or.inl (d2IndexDatum_carrier_of_core (s := .Ru) (by decide) Nat.prime_five
      (by norm_num) CFSG.AGLEmbedding.glbCore_Ru_five L ⟨e⟩)
  · exact d2IndexDatumPlus_carrier_of_coreSup (s := .Co2) (by decide) Nat.prime_five
      (by norm_num) CFSG.AGLEmbedding.glbCore_sup_Co2_five L ⟨e⟩
  · exact d2IndexDatumPlus_carrier_of_coreSup (s := .Co3) (by decide) Nat.prime_five
      (by norm_num) CFSG.AGLEmbedding.glbCore_sup_Co3_five L ⟨e⟩
  · exact Or.inl (d2IndexDatum_Suz_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_ONan_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_Fi22_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_HN_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_Ly_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_Th_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_Fi23_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_Co1_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_Fi24Prime_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_Co1_five L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_Ly_five L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_HN_five L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_B_three L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_carrier_of_core (s := .He) (by decide) Nat.prime_seven
      (by norm_num) glbCore_He_seven L ⟨e⟩)
  · have : Finite (NativeSporadic.Carrier .ONan) := Finite.of_equiv L e.toEquiv
    exact Or.inl (d2IndexDatum_carrier_of_core (s := .ONan) (by decide) Nat.prime_seven
      (by norm_num) glbCore_ON_seven L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_carrier_of_pRank (s := .B) (by decide) Nat.prime_five
      (by norm_num) CFSG.AGLEmbedding.three_le_pRank_B_five L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_Th_five L ⟨e⟩)
  · exact Or.inl (d2IndexDatum_J4_three L ⟨e⟩)

theorem sporFi24SevenRow : SporFi24SevenRow := d2IndexDatum_Fi24Prime_seven

theorem smallIdentSporAt_of_ne (s : TauCeti.SporadicName) (hs : s ≠ .M)
    (hHS5 : SporGammaOneAt .HS 5) (hB7 : SporGammaOneAt .B 7) : SmallIdentSporAt s :=
  smallIdentSporAt_of_rows sporProvedRows sporFi24SevenRow
    CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group card_carrier_eq_d2SporadicOrder s hs
    hHS5 hB7

end Rows

end CFSG.AGLEmbedding
