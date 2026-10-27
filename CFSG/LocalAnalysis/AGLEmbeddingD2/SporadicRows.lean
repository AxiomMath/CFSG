module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankRows
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BD2Three
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreHe
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreON
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreThRow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreJ4Row
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicRankFiveB
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Mathieu
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Co2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Co3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2J2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Ru
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicRankRows
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2DatumFi23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2DatumCo1
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2DatumFi24prime

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint

@[expose] def d2SporadicProvedList : List (TauCeti.SporadicName × ℕ) :=
  [(.M22, 3), (.M23, 3), (.J2, 5), (.He, 5), (.Suz, 5), (.Th, 7), (.HS, 3), (.Fi23, 5), (.Co1, 7),
    (.Fi24Prime, 5), (.M12, 3), (.M24, 3), (.J3, 3), (.McL, 3), (.Co3, 3), (.Co2, 3), (.J2, 3),
    (.He, 3), (.Ru, 3), (.Ru, 5), (.Co2, 5), (.Co3, 5), (.Suz, 3), (.ONan, 3), (.Fi22, 3),
    (.HN, 3), (.Ly, 3), (.Th, 3), (.Fi23, 3), (.Co1, 3), (.Fi24Prime, 3), (.Co1, 5), (.Ly, 5),
    (.HN, 5), (.B, 3), (.He, 7), (.ONan, 7), (.B, 5), (.Th, 5), (.J4, 3)]

@[expose] def d2SporadicLeafList : List (TauCeti.SporadicName × ℕ) :=
  [(.McL, 5), (.J4, 11), (.M11, 3), (.Fi22, 5)]

@[expose] def d2SporadicOpenList : List (TauCeti.SporadicName × ℕ) :=
  [(.HS, 5), (.Fi24Prime, 7), (.B, 7)]

@[expose] def D2SporadicOpenRows : Prop :=
  ∀ s p, (s, p) ∈ d2SporadicOpenList → D2IndexCaseAt (.sporadic s) fun q => q = p

theorem d2SporadicSq_iff (s : TauCeti.SporadicName) (p : ℕ) :
    (s ≠ .M ∧ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ d2SporadicOrder s) ↔
      ((s, p) ∈ d2SporadicProvedList ∨ (s, p) ∈ d2SporadicLeafList ∨
        (s, p) ∈ d2SporadicOpenList) := by
  refine ⟨fun ⟨hs, hp, hp2, h⟩ => ?_, fun h => ?_⟩
  · have hN : d2SporadicOrder s ≠ 0 := by
      cases s <;> first | exact absurd rfl hs | norm_num [d2SporadicOrder]
    have hmem : p ∈ (d2SporadicOrder s).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, hN⟩
    clear hN
    cases s <;> first | exact absurd rfl hs | skip
    all_goals
      norm_num [d2SporadicOrder, Nat.primeFactors, Nat.primeFactorsList] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact absurd rfl hp2
        | (exfalso; norm_num [d2SporadicOrder] at h; done)
        | decide
  · have key : ∀ x ∈ d2SporadicProvedList ++ d2SporadicLeafList ++ d2SporadicOpenList,
        x.1 ≠ .M ∧ x.2.Prime ∧ x.2 ≠ 2 ∧ x.2 ^ 2 ∣ d2SporadicOrder x.1 := by
      simp only [d2SporadicProvedList, d2SporadicLeafList, d2SporadicOpenList, List.cons_append,
        List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true]
      norm_num [d2SporadicOrder]
    exact key (s, p) (by simpa [or_assoc] using h)

section Rows

theorem d2SporadicCase_of_openRows' (Q : TauCeti.SporadicName → ℕ → Prop)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicOpenList → Q s p →
      D2IndexCaseAt (.sporadic s) fun q => q = p)
    (hM : D2IndexCaseAt (.sporadic .M) fun p => Q .M p)
    (hM11 : D2IndexCaseAt (.sporadic .M11) fun p => p = 3)
    (hFi22 : D2IndexCaseAt (.sporadic .Fi22) fun p => p = 5) :
    ∀ s : TauCeti.SporadicName, D2IndexCaseAt (.sporadic s) fun p =>
      Q s p ∧ ¬ (s = .McL ∧ p = 5) ∧ ¬ (s = .J4 ∧ p = 11) := by
  have hproved : ∀ (s : TauCeti.SporadicName) (p : ℕ), (s, p) ∈ d2SporadicProvedList →
      ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier s) →
        D2IndexDatumPlus L p := by
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
  intro s
  by_cases hsM : s = .M
  · subst hsM
    intro G _ _ hglob hD1 p hp
    exact hM G hglob hD1 p hp.1
  have hrow := d2IndexCaseAt_sporadic_of_rows s hsM
    (Pp := fun p => ((¬ (s = .McL ∧ p = 5) ∧ ¬ (s = .J4 ∧ p = 11)) ∧
      ¬ ((s = .M11 ∧ p = 3) ∨ (s = .Fi22 ∧ p = 5))) ∧ (s, p) ∉ d2SporadicOpenList)
    (fun p hp hp2 hsq hPp L _ _ he => by
      rcases (d2SporadicSq_iff s p).1 ⟨hsM, hp, hp2, hsq⟩ with hpr | hleaf | hopen
      · exact hproved s p hpr L he
      · exfalso
        simp only [d2SporadicLeafList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
          or_false] at hleaf
        rcases hleaf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hPp.1.1.1 ⟨rfl, rfl⟩
        · exact hPp.1.1.2 ⟨rfl, rfl⟩
        · exact hPp.1.2 (Or.inl ⟨rfl, rfl⟩)
        · exact hPp.1.2 (Or.inr ⟨rfl, rfl⟩)
      · exact absurd hopen hPp.2)
  intro G _ _ hglob hD1 p hp
  by_cases hopen : (s, p) ∈ d2SporadicOpenList
  · exact hrows s p hopen hp.1 G hglob hD1 p rfl
  by_cases hq : (s = .M11 ∧ p = 3) ∨ (s = .Fi22 ∧ p = 5)
  · rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hM11 G hglob hD1 3 rfl
    · exact hFi22 G hglob hD1 5 rfl
  · exact hrow G hglob hD1 p ⟨⟨hp.2, hq⟩, hopen⟩

theorem d2SporadicCase_of_openRows (hrows : D2SporadicOpenRows)
    (hM : D2IndexCaseAt (.sporadic .M) fun _ => True)
    (hM11 : D2IndexCaseAt (.sporadic .M11) fun p => p = 3)
    (hFi22 : D2IndexCaseAt (.sporadic .Fi22) fun p => p = 5) :
    ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt (.sporadic s) fun p => ¬ (s = .McL ∧ p = 5) ∧ ¬ (s = .J4 ∧ p = 11) := by
  intro s G _ _ hglob hD1 p hp
  exact d2SporadicCase_of_openRows' (fun _ _ => True) (fun s p h _ => hrows s p h) hM hM11 hFi22
    s G hglob hD1 p ⟨trivial, hp⟩

end Rows

end CFSG.AGLEmbeddingD2
