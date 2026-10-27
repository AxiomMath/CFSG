module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporOpen3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicRows
public import Certificates.Certificate9502
public import Certificates.Certificate9505
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowCo2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowCo3
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowJ3
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowMcL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeLyFive
import CFSG.Sporadic.NativeFinite

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Blueprint

@[expose] def d2SporadicRowPairs3 : List (TauCeti.SporadicName × ℕ) :=
  [(.M22, 3), (.M23, 3), (.J2, 5), (.He, 5), (.Suz, 5), (.Th, 7), (.HS, 3), (.Co1, 7), (.M12, 3),
    (.M24, 3)]

@[expose] def d2SporadicRankPairs3 : List (TauCeti.SporadicName × ℕ) :=
  [(.J3, 3), (.McL, 3), (.Suz, 3), (.ONan, 3), (.Co3, 3), (.Co2, 3), (.HN, 3), (.HN, 5), (.Ly, 3),
    (.Ly, 5), (.Th, 3), (.Co1, 3), (.Co1, 5)]

theorem d2SporadicPairs3_cover (s : TauCeti.SporadicName) (p : ℕ)
    (hs : s ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName))
    (h : s ≠ .M ∧ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ d2SporadicOrder s) :
    (s, p) ∈ d2SporadicRowPairs3 ∨ (s, p) ∈ d2SporadicRankPairs3 ∨
      (s, p) ∈ d2SporadicOpenPairs3 := by
  have key : ∀ x ∈ d2SporadicProvedList ++ d2SporadicLeafList ++ d2SporadicOpenList,
      x.1 ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) →
        x ∈ d2SporadicRowPairs3 ∨ x ∈ d2SporadicRankPairs3 ∨ x ∈ d2SporadicOpenPairs3 := by
    decide
  exact key (s, p) (by simpa [or_assoc] using (d2SporadicSq_iff s p).1 h) hs

section Rank

theorem three_le_pRank_of_tcGenDatum {X : Type} [Group X] [Finite X] [Nontrivial X] {p : ℕ}
    (hp : p.Prime) (h : TCGenDatum X p) : 3 ≤ Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨r, U, P, S, -, -, hrank, hgen, hnorm⟩ := h
  obtain ⟨g, hg⟩ := exists_ne (1 : X)
  have hS : S.Nonempty := by
    by_contra hS
    rw [Set.not_nonempty_iff_eq_empty] at hS
    have hg' : g ∈ Subgroup.closure S := hgen ▸ Subgroup.mem_top g
    rw [hS, Subgroup.closure_empty, Subgroup.mem_bot] at hg'
    exact hg hg'
  obtain ⟨s, hs⟩ := hS
  obtain ⟨i, -⟩ := hnorm s hs
  exact (hrank i).2.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_top)

theorem three_le_pRank_carrier_J3_three
    [Finite (NativeSporadic.Carrier .J3)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .J3)) :=
  moduleDatum_J3_three.three_le_pRank Nat.prime_three (by norm_num)

theorem three_le_pRank_carrier_McL_three
    [Finite (NativeSporadic.Carrier .McL)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .McL)) :=
  moduleDatum_McL_three.three_le_pRank Nat.prime_three (by norm_num)

theorem three_le_pRank_carrier_Suz_three
    [Finite (NativeSporadic.Carrier .Suz)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Suz)) :=
  moduleDatum_Suz_three.three_le_pRank Nat.prime_three (by norm_num)

theorem three_le_pRank_carrier_Co3_three
    [Finite (NativeSporadic.Carrier .Co3)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Co3)) :=
  moduleDatum_Co3_three.three_le_pRank Nat.prime_three (by norm_num)

theorem three_le_pRank_carrier_Co2_three
    [Finite (NativeSporadic.Carrier .Co2)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Co2)) :=
  moduleDatum_Co2_three.three_le_pRank Nat.prime_three (by norm_num)

theorem three_le_pRank_carrier_Co1_three
    [Finite (NativeSporadic.Carrier .Co1)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Co1)) :=
  moduleDatum_Co1_three.three_le_pRank Nat.prime_three (by norm_num)

theorem three_le_pRank_carrier_HN_three
    [Finite (NativeSporadic.Carrier .HN)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .HN)) :=
  moduleDatum_HN_three.three_le_pRank Nat.prime_three (by norm_num)

theorem three_le_pRank_carrier_Ly_three
    [Finite (NativeSporadic.Carrier .Ly)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Ly)) :=
  moduleDatum_Ly_three.three_le_pRank Nat.prime_three (by norm_num)

theorem three_le_pRank_carrier_Th_three
    [Finite (NativeSporadic.Carrier .Th)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Th)) :=
  moduleDatum_Th_three.three_le_pRank Nat.prime_three (by norm_num)

theorem three_le_pRank_carrier_ONan_three
    [Finite (NativeSporadic.Carrier .ONan)] :
    3 ≤ Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .ONan)) := by
  obtain ⟨D, -, -, -, hidx⟩ := abelianSylowDatum_ON_three
  have hN : Nat.card NativeSporadic.ON = 460815505920 := CFSG.Sporadic.ON.card_ON
  have hcard := Subgroup.card_mul_index D.span
  rw [D.card_span Nat.prime_three, hN] at hcard
  have h3 : 3 ≤ D.n := by
    by_contra hlt
    have : D.n = 0 ∨ D.n = 1 ∨ D.n = 2 := by omega
    rcases this with h | h | h <;> rw [h] at hcard <;> apply hidx <;> omega
  exact h3.trans (D.n_le_pRank Nat.prime_three)

theorem three_le_pRank_carrier_Co1_five
    [Finite (NativeSporadic.Carrier .Co1)] :
    3 ≤ Open.pRank 5 (⊤ : Subgroup (NativeSporadic.Carrier .Co1)) := by
  have hN : Nat.card NativeSporadic.Co1 = 4157776806543360000 := CFSG.Sporadic.Co1.card_Co1
  have : Nontrivial (NativeSporadic.Carrier .Co1) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by show 1 < Nat.card NativeSporadic.Co1; rw [hN]; norm_num)
  exact three_le_pRank_of_tcGenDatum Nat.prime_five
    (R3.tcGenDatum_of_check (CFSG.SectionRank.spec2 24) (D := R3.Co1Five.tcSpec) Nat.prime_five
      Certificates.certificate9502.1)

theorem three_le_pRank_carrier_HN_five
    [Finite (NativeSporadic.Carrier .HN)] :
    3 ≤ Open.pRank 5 (⊤ : Subgroup (NativeSporadic.Carrier .HN)) := by
  have hN : Nat.card NativeSporadic.HN = 273030912000000 := CFSG.Sporadic.HN.card_HN
  have : Nontrivial (NativeSporadic.Carrier .HN) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by show 1 < Nat.card NativeSporadic.HN; rw [hN]; norm_num)
  exact three_le_pRank_of_tcGenDatum Nat.prime_five
    (R3.tcGenDatum_of_check (CFSG.SectionRank.specP 5 133) (D := R3.HNFive.tcSpec) Nat.prime_five
      Certificates.certificate9505.1)

theorem three_le_pRank_carrier_Ly_five
    [Finite (NativeSporadic.Carrier .Ly)] :
    3 ≤ Open.pRank 5 (⊤ : Subgroup (NativeSporadic.Carrier .Ly)) := by
  have hN : Nat.card NativeSporadic.Ly = 51765179004000000 := CFSG.Sporadic.Ly.card_Ly'
  have : Nontrivial (NativeSporadic.Carrier .Ly) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by show 1 < Nat.card NativeSporadic.Ly; rw [hN]; norm_num)
  exact three_le_pRank_of_tcGenDatum Nat.prime_five tcGenDatum_Ly_five

end Rank

section Vacuous

theorem d2SporadicVacuous3_of_certificates : D2SporadicVacuous3 := by
  intro s hs p hp
  have hsM : s ≠ .M := fun h => hs (by simp [h])
  have : Finite (NativeSporadic.Carrier s) := CFSG.Sporadic.finite_carrier_of_ne_M s hsM
  have hrow : ∀ (q : ℕ), (s, q) ∈ d2SporadicRowPairs3 →
      ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier s) →
        D2IndexDatumPlus L q := by
    intro q h L _ _ ⟨e⟩
    simp only [d2SporadicRowPairs3, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (d2IndexDatum_M22_three e)
    · exact Or.inl (d2IndexDatum_M23_three e)
    · exact Or.inl (d2IndexDatum_J2_five e)
    · exact Or.inl (d2IndexDatum_He_five e)
    · exact Or.inl (d2IndexDatum_Suz_five e)
    · exact Or.inl (d2IndexDatum_Th_seven e)
    · exact Or.inl (d2IndexDatum_HS_three e)
    · exact Or.inl (d2IndexDatum_Co1_seven e)
    · exact Or.inl (d2IndexDatum_carrier_of_core (s := .M12) (by decide) Nat.prime_three
        (by norm_num) CFSG.AGLEmbedding.glbCore_M12_three L ⟨e⟩)
    · exact d2IndexDatumPlus_carrier_of_coreSup (s := .M24) (by decide) Nat.prime_three
        (by norm_num) CFSG.AGLEmbedding.glbCore_sup_M24_three L ⟨e⟩
  have hrank : ∀ (q : ℕ), (s, q) ∈ d2SporadicRankPairs3 →
      3 ≤ Open.pRank q (⊤ : Subgroup (NativeSporadic.Carrier s)) := by
    intro q h
    simp only [d2SporadicRankPairs3, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact three_le_pRank_carrier_J3_three
    · exact three_le_pRank_carrier_McL_three
    · exact three_le_pRank_carrier_Suz_three
    · exact three_le_pRank_carrier_ONan_three
    · exact three_le_pRank_carrier_Co3_three
    · exact three_le_pRank_carrier_Co2_three
    · exact three_le_pRank_carrier_HN_three
    · exact three_le_pRank_carrier_HN_five
    · exact three_le_pRank_carrier_Ly_three
    · exact three_le_pRank_carrier_Ly_five
    · exact three_le_pRank_carrier_Th_three
    · exact three_le_pRank_carrier_Co1_three
    · exact three_le_pRank_carrier_Co1_five
  have hfree : D2FreeCaseAt (.sporadic s) fun q => (s, q) ∉ d2SporadicOpenPairs3 := by
    refine d2FreeCaseAt_sporadic_of_rows s hsM ?_
    intro q hq hq2 hsq hPq L _ _ hL
    rcases d2SporadicPairs3_cover s q hs ⟨hsM, hq, hq2, hsq⟩ with h | h | h
    · exact hrow q h L hL
    · exact Or.inl (d2IndexDatum_carrier_of_pRank hsM hq hq2 (hrank q h) L hL)
    · exact absurd h hPq
  exact fun X _ _ R A X₀ K hK he => hfree X p hp R A X₀ K hK he

end Vacuous

end CFSG.LocalAnalysis.RankThreeTheoremC
