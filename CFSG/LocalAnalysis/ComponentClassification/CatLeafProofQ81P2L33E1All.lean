module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1Res
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1E6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1TwE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1D4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1GFE

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_isPGroup_E7
    {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    (α : MulAut (adjointGroup .E7 K)) (hα : α ^ 2 = 1)
    (hinn : (∃ (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ), ∀ h : adjointGroup .E7 K,
        (α h : ModGL .E7 K) = (g : ModGL .E7 K) * rootDiagUnit .E7 a * h *
          (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹) →
      ∃ X : Subgroup (adjointGroup .E7 K), X ≤ fixedSubgroup α ∧ ⁅X, X⁆ = X ∧
        2 ∣ Nat.card X) :
    ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α)) := by
  have : Finite (ModGL Tag.E7 K) := finite_modGL
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  rcases odd_E7_involution_inner_or_quadratic hK hα with hin |
    ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
  · obtain ⟨X, hXF, hXp, hX2⟩ := hinn hin
    exact not_isPGroup_of_perfect hXF hXp hX2
  · exact not_isPGroup_quadratic_field hK2 hq he hKe δ hδ hαg hα

theorem sq_eq_one_and_ne_one {Y : Type} [Group Y] {a : MulAut Y} (ha : orderOf a = 2) :
    a ^ 2 = 1 ∧ a ≠ 1 := by
  refine ⟨by rw [← ha]; exact pow_orderOf_eq_one a, fun h => ?_⟩
  rw [h, orderOf_one] at ha
  exact absurd ha (by norm_num)

theorem not_isPGroup_of_untwisted
    {Y : Type} [Group Y] [Finite Y] (τ : Tag) {q : ℕ}
    (hm : UntwistedChevalleyModel Y τ q) (hq : Odd q) {a : MulAut Y} (ha : orderOf a = 2)
    (h : ∀ (K : Type) [Field K] [Finite K], Odd (Nat.card K) →
      ∀ α : MulAut (adjointGroup τ K), α ^ 2 = 1 → α ≠ 1 →
        ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α))) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨ha2, ha1⟩ := sq_eq_one_and_ne_one ha
  intro hP
  exact h K (hK ▸ hq) (MulAut.congr e a) (by rw [← map_pow, ha2, map_one])
    (fun h' => ha1 ((MulAut.congr e).injective (h'.trans (map_one _).symm)))
    (isPGroup_fixedPoints_congr e a hP)

theorem not_isPGroup_of_twisted
    {Y : Type} [Group Y] [Finite Y] (t : TwistTag) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hm : TwistedChevalleyModel Y t (p ^ f)) {a : MulAut Y} (ha : orderOf a = 2)
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ t.order →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
        ∀ α : MulAut (graphFixedRootGroup t K σ.toRingHom), α ^ 2 = 1 → α ≠ 1 →
          ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α))) :
    ¬ IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card t hp hf hm
  have : Finite (ModGL t.tag K) := finite_modGL
  obtain ⟨ha2, ha1⟩ := sq_eq_one_and_ne_one ha
  intro hP
  exact h K hK σ hσ (MulAut.congr e a) (by rw [← map_pow, ha2, map_one])
    (fun h' => ha1 ((MulAut.congr e).injective (h'.trans (map_one _).symm)))
    (isPGroup_fixedPoints_congr e a hP)

theorem twoNilpFor_chevOdd
    (hRes : ChevOddInnerInput) :
    TwoNilpFor fun Y _ => ∃ (t : StatedLieTag) (p f : ℕ), p ≠ 2 ∧
      t ∈ Blueprint.chevalleyExceptionalTags ∧ Blueprint.ChevalleyExceptionalModel Y t p f := by
  obtain ⟨hRes7, hResT⟩ := hRes
  rintro Y _ _ ⟨t, p, f, hp2, -, ⟨⟨hp, hf, -⟩, hm⟩⟩ _ _ a ha hP
  have hq : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  exfalso
  cases t
  case G2 =>
    refine not_isPGroup_of_untwisted .G2 hm hq ha ?_ hP
    intro K _ _ hK α hα _
    exact not_isPGroup_GFE (Or.inl rfl) hK α hα
  case F4 =>
    refine not_isPGroup_of_untwisted .F4 hm hq ha ?_ hP
    intro K _ _ hK α hα _
    exact not_isPGroup_GFE (Or.inr (Or.inl rfl)) hK α hα
  case E6 =>
    refine not_isPGroup_of_untwisted .E6 hm hq ha ?_ hP
    intro K _ _ hK α hα _
    exact not_isPGroup_E6 hK α hα
  case E7 =>
    refine not_isPGroup_of_untwisted .E7 hm hq ha ?_ hP
    intro K _ _ hK α hα hα1
    exact not_isPGroup_E7 hK α hα (hRes7 K hK α hα hα1)
  case E8 =>
    refine not_isPGroup_of_untwisted .E8 hm hq ha ?_ hP
    intro K _ _ hK α hα _
    exact not_isPGroup_GFE (Or.inr (Or.inr rfl)) hK α hα
  case twistedE6 =>
    refine not_isPGroup_of_twisted .E6 hp hf hm ha ?_ hP
    intro K _ _ hK σ hσ α hα hα1
    exact not_isPGroup_twistedE6 hp hp2 hf hK σ hσ α hα hα1 (hResT .E6 p f hp hp2 hf K hK σ hσ)
  case trialityD4 =>
    refine not_isPGroup_of_twisted .D4 hp hf hm ha ?_ hP
    intro K _ _ hK σ hσ α hα hα1
    exact not_isPGroup_triality hp hp2 hf hK σ hσ α hα hα1 (hResT .D4 p f hp hp2 hf K hK σ hσ)
  all_goals exact hm.elim

end CFSG.ComponentClassification.HarrisLit.L33.E1
