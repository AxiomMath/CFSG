module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Reduction
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SixNatOfPairData
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SevenNatOfQuadData
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.NaturalModuleBridge
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightOfData
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 CFSG.QuasithinUnique
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM InClassXBlock NineThreeFive NineThreeEight
  blockV HasIrreducibleCommutatorQuotient)
open CFSG.HardMathSupport.Cooperstein.Coordinator
  (Asc81bNineThreeAltLS asc81bHyp_sup)

variable {G : Type} [Group G] {S L : Subgroup G}

@[expose] def NaturalSection (S L : Subgroup G) (d : ℕ) : Prop :=
  ∃ (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥L →* Equiv.Perm (Fin d)),
    Function.Surjective π ∧
    π.ker = (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer ((L ⊔ S : Subgroup G) : Set G)).subgroupOf
      ⁅blockV S L, L⁆ ∧
    alternatingGroup (Fin d) ≤ θ.range ∧
    ∀ (l : ↥L) (t t' : ↥⁅blockV S L, L⁆), (t' : G) = (l : G) * t * (l : G)⁻¹ →
      ∀ x : evenWeight d, Multiplicative.toAdd (π t) = (QuotientAddGroup.mk x : altHeart d) →
        Multiplicative.toAdd (π t') =
          (QuotientAddGroup.mk (evenWeightPerm (θ l) x) : altHeart d)

@[expose] def NaturalSectionL (S L : Subgroup G) (d : ℕ) : Prop :=
  ∃ (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥L →* Equiv.Perm (Fin d)),
    Function.Surjective π ∧
    π.ker = (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆ ∧
    alternatingGroup (Fin d) ≤ θ.range ∧
    ∀ (l : ↥L) (t t' : ↥⁅blockV S L, L⁆), (t' : G) = (l : G) * t * (l : G)⁻¹ →
      ∀ x : evenWeight d, Multiplicative.toAdd (π t) = (QuotientAddGroup.mk x : altHeart d) →
        Multiplicative.toAdd (π t') =
          (QuotientAddGroup.mk (evenWeightPerm (θ l) x) : altHeart d)

theorem hasIrr_of_naturalSectionL {d : ℕ} (hd : 4 ≤ d) (h : NaturalSectionL S L d) :
    HasIrreducibleCommutatorQuotient L (blockV S L) := by
  obtain ⟨π, θ, hπs, hker, hθ, hequiv⟩ := h
  exact hasIrreducibleCommutatorQuotient_of_altNatural hd π hπs hker θ hθ hequiv

@[expose] def PairActionData (X S L : Subgroup G) (n : ℕ) : Prop :=
  ∃ φ : ↥(barM X L) ≃* AltB (Fin n),
    ((barM X (S ⊓ L)).subgroupOf (barM X L)).map φ.toMonoidHom = EA (Fin n) ∧
    barM X S ≤ Subgroup.normalizer ((barM X L : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) : Set _) ∧
    ∀ s ∈ barM X S, ∃ σ ∈ blockFix (Fin n), ∀ l l' : ↥(barM X L),
      (l' : ↥X ⧸ CFSG.pCore 2 ↥X) = s * l * s⁻¹ →
      ((φ l' : AltB (Fin n)) : Equiv.Perm (Fin n × Bool)) =
        σ * ((φ l : AltB (Fin n)) : Equiv.Perm (Fin n × Bool)) * σ⁻¹

theorem nineThreeSixNat_of_pairActionData [Finite G] {X : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (hyp : Asc81bHyp X S) (hirr : HasIrreducibleCommutatorQuotient L (blockV S L))
    (h : PairActionData X S L n) : NineThreeSixNat X S L := by
  obtain ⟨φ, hS, hSL, hact⟩ := h
  exact nineThreeSixNat_of_action hn hyp hirr φ hS hSL hact

variable [Finite G]

@[expose] def Asc81bEightTen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
    ∀ m : ℕ, (m = 7 ∨ 8 < m) →
    Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m)) →
      InClassXBlock L ∨ (NineThreeFive (L ⊔ S) L ∧ IsA7FourType L) ∨
        (∃ n : ℕ, 5 ≤ n ∧ PairActionData (L ⊔ S) S L n ∧ NaturalSectionL S L (2 * n)) ∨
        (∃ n : ℕ, (n = 3 ∨ 5 ≤ n) ∧ QuadBlockData (L ⊔ S) S L n ∧ NaturalSectionL S L (4 * n)) ∨
        (∃ N r : ℕ, Even N ∧ 2 * r ≤ N ∧ 1 ≤ r ∧ (r = 1 ∨ r = 3 ∨ 5 ≤ r) ∧ 6 ≤ N - 2 * r ∧
          EightBlockData X S L r (N - 2 * r) ∧ IsShort2 L ∧ IsTypeScriptL L)

theorem asc81bNineThreeAltLS_of_eightTen (h : Asc81bEightTen) : Asc81bNineThreeAltLS := by
  intro G _ _ X S L hX hA hL hSL m hm he
  rcases h G X S L hX hA hL hSL m hm he with
    h1 | h5 | ⟨n, hn, hd, hnat⟩ | ⟨n, hn, hd, hnat⟩ | ⟨N, r, hN, hr2, hr1, hr, hs, hD, hsh, hT⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h5)
  · have hA' := asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
    exact Or.inr (Or.inr (Or.inl (nineThreeSixNat_of_pairActionData hn hA'
      (hasIrr_of_naturalSectionL (by omega) hnat) hd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (nineThreeSevenNat_of_quadBlockData hn
      (hasIrr_of_naturalSectionL (by omega) hnat) hd))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨nineThreeEight_of_eightBlockData hsh hN hr2 hr1 hr hs hD, hT⟩)))

theorem asc81bNineThreeAlt_of_eightTen (h : Asc81bEightTen) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.Asc81bNineThreeAlt :=
  CFSG.HardMathSupport.Cooperstein.Coordinator.asc81bNineThreeAlt_of_LS
    (asc81bNineThreeAltLS_of_eightTen h)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
