module

public import CFSG.GH74.GLS.TwoThin.ClassCongr
public import CFSG.GH74.GLS.TwoThin.G.Pred
public import CFSG.GH74.GLS.Statements
public import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank

@[expose] def IsB2Pair {G : Type} [Group G] (x : G) (K : Subgroup G) : Prop :=
  IsILo 2 x K ∧ InB2 (↥K ⧸ pPrimeCore 2 ↥K)

@[expose] def RankThreeCentralizers : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    3 ≤ pRank 2 G → ∀ x : G, orderOf x = 2 → 3 ≤ pRank 2 ↥(centralizer ({x} : Set G))

@[expose] def B2PumpupClosed (G : Type) [Group G] : Prop :=
  ∀ (x : G) (K : Subgroup G) (x' : G) (K' : Subgroup G),
    InB2 (↥K ⧸ pPrimeCore 2 ↥K) → PumpUpLT 2 x K x' K' → InB2 (↥K' ⧸ pPrimeCore 2 ↥K')

@[expose] def TerminalExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G))) → B2PumpupClosed G →
    (∃ (x : G) (K : Subgroup G), IsB2Pair x K) →
      ∃ (x : G) (K : Subgroup G), IsTwoTerminal x K ∧ InB2 (↥K ⧸ pPrimeCore 2 ↥K)

theorem exists_isB2Pair_of_l2Meets {G : Type} [Group G] [Finite G]
    (hrank : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    (h : L2Meets G InB2) : ∃ (x : G) (K : Subgroup G), IsB2Pair x K := by
  obtain ⟨x, hx, Kh, hKh, hB⟩ := h
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_pComponent_of_component hKh
  exact ⟨x, K, ⟨hx, by simpa [oBound] using hrank x hx, hK⟩, inB2_of_mulEquiv e.symm hB⟩

@[expose] def S_twoThinOfB2P (PG : GroupPred) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PG G → IsKProperSimple G → 3 ≤ pRank 2 G →
    ¬ L2Meets G InG2 → L2Meets G InB2 → HasTwoThinConfiguration G

theorem S_twoThinOfB2_of_P (h : S_twoThinOfB2P GroupPred.trivial) : S_twoThinOfB2 := by
  intro G _ _ hG h3 hnoG2 hB2
  exact h G trivial hG h3 hnoG2 hB2

theorem s_twoThinOfB2P_of_reduction {PG : GroupPred} (hRank : RankThreeCentralizers)
    (hClosed : ∀ (G : Type) [Group G] [Finite G], PG G → IsKProperSimple G → 3 ≤ pRank 2 G →
      ¬ L2Meets G InG2 → B2PumpupClosed G)
    (hTerm : TerminalExists) : S_twoThinOfB2P PG := by
  intro G _ _ hPG hG h3 hnoG2 hB2
  have hrank : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) :=
    fun y hy => hRank G hG.1 hG.2.1 h3 y hy
  obtain ⟨x, K, hxK, hB⟩ := hTerm G hrank (hClosed G hPG hG h3 hnoG2)
    (exists_isB2Pair_of_l2Meets hrank hB2)
  exact ⟨x, K, hxK, hB⟩

theorem s_twoThinOfB2_of_reduction (hRank : RankThreeCentralizers)
    (hClosed : ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G →
      ¬ L2Meets G InG2 → B2PumpupClosed G)
    (hTerm : TerminalExists) : S_twoThinOfB2 :=
  S_twoThinOfB2_of_P
    (s_twoThinOfB2P_of_reduction hRank (fun G _ _ _ hG h3 hno => hClosed G hG h3 hno) hTerm)

end CFSG.GH74.GLS.TwoThin
