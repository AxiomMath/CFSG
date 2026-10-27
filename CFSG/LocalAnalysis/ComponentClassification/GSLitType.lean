module

public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitOddInput
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankSmallSources
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem oddCore_eq_pPrimeCore_two (G : Type*) [Group G] : oddCore G = pPrimeCore 2 G := by
  simp only [oddCore, pPrimeCore, Nat.coprime_two_left]

theorem statedClassicalModel_of_lieModel_psl_two {G : Type} [Group G] {p f : ℕ}
    (h : Blueprint.LieModel G .PSL 2 p f) :
    Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem statedClassicalModel_of_lieModel_psl_three {G : Type} [Group G] {p f : ℕ}
    (h : Blueprint.LieModel G .PSL 3 p f) :
    Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem two_le_pRank_of_mulEquiv_he {J : Type} [Group J] [Finite J]
    (hA : IsQuasisimple (J ⧸ oddCore J)) (e : J ⧸ oddCore J ≃* Blueprint.NativeSporadic.He) :
    2 ≤ pRank 2 J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup Blueprint.NativeSporadic.He := Sporadic.He.isSimpleGroup_He
  have hnab : ∃ a b : J ⧸ oddCore J, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hA
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  have hZ : center (J ⧸ oddCore J) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Blueprint.NativeSporadic.He) with
      hZ | hZ
    · rw [eq_bot_iff]
      intro z hz
      have h1 : e z ∈ center Blueprint.NativeSporadic.He := by
        rw [mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, mem_center_iff.mp hz g']
      rw [hZ, mem_bot] at h1
      rw [mem_bot]
      exact e.injective (by rw [h1, map_one])
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : e b ∈ center Blueprint.NativeSporadic.He := hZ ▸ mem_top _
      apply hab
      apply e.injective
      rw [map_mul, map_mul]
      exact mem_center_iff.mp hb (e a)
  have h2 := LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hA
    (by rw [hZ, Subgroup.card_bot]; exact odd_one)
  have hOodd : ¬ 2 ∣ Nat.card (oddCore J) := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact UnbalancedCatalog.EvenCatalog.odd_card_oddCore
  have hrank : pRank 2 J = pRank 2 (J ⧸ oddCore J) := by
    rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top,
      SectionRank.pRank_quotient_eq (oddCore J) hOodd]
  rw [hrank]
  exact h2

variable {X : Type} [Group X] [Finite X]

theorem isQuasisimple_of_gsUnbalancingTriple {x y : X} {L : Subgroup X}
    (hL : GSUnbalancingTriple x y L) : IsQuasisimple (L ⧸ pPrimeCore 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hL.2.2.2.1).1
    hL.2.2.2.2.1).2.2

variable [IsSimpleGroup X]

theorem unbalancing_component_type_of_small (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (hsmall : ¬ ∃ (x y : X) (L : Subgroup X), GSUnbalancingTriple x y L ∧
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) ∨
        Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2))
    {x y : X} {L : Subgroup X} (hL : GSUnbalancingTriple x y L) :
    Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f := by
  rcases hTB X hnonab hK hz hU x y L hL with ⟨n, hodd, hn, he⟩ | h | h
  · exact absurd ⟨x, L, n, hL.1, hodd, hn, hL.2.2.2.1, hL.2.2.2.2.1, he⟩
      (hSA X hnonab hK hz hU)
  · exact h
  · exact absurd ⟨x, y, L, hL, h⟩ hsmall

theorem unbalancing_component_type (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hGS : GriessSolomonInput)
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {x y : X} {L : Subgroup X}
    (hL : GSUnbalancingTriple x y L) :
    Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f :=
  unbalancing_component_type_of_small hTB hSA hnonab hK hz hU (hGS X hnonab hK hz hU) hL

theorem two_le_pRank_of_gsUnbalancingTriple (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {x y : X} {L : Subgroup X}
    (hL : GSUnbalancingTriple x y L) : 2 ≤ pRank 2 ↥L := by
  let e : L ⧸ oddCore L ≃* L ⧸ pPrimeCore 2 L :=
    QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore_two L)
  have hA : IsQuasisimple (L ⧸ oddCore L) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e.symm).1
      (isQuasisimple_of_gsUnbalancingTriple hL)
  rcases hTB X hnonab hK hz hU x y L hL with ⟨n, hodd, hn, he⟩ |
      (⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, -, hmodel⟩) | (⟨⟨eHe⟩⟩ | h34)
  · exact absurd ⟨x, L, n, hL.1, hodd, hn, hL.2.2.2.1, hL.2.2.2.2.1, he⟩
      (hSA X hnonab hK hz hU)
  · exact UnbalancedGS.small_source_models_force_rank_at_least_two hA (Or.inr (Or.inl ⟨e.trans e7⟩))
  · exact UnbalancedGS.small_source_models_force_rank_at_least_two hA
      (Or.inl ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, SectionRank.statedClassicalModel_of_mulEquiv e
        (statedClassicalModel_of_lieModel_psl_two hmodel)⟩)
  · exact two_le_pRank_of_mulEquiv_he hA (e.trans eHe)
  · exact UnbalancedGS.small_source_models_force_rank_at_least_two hA
      (Or.inr (Or.inr (statedClassicalModel_of_lieModel_psl_three h34)))

end CFSG.ComponentClassification.GSLit
