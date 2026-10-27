module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcTwE6
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcInnerLane
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcSimp
import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2
public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExc
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcField

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem gomi_exists_simple_component_congr {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (α : MulAut A) (L : Subgroup ↥(α.toMonoidHom.eqLocus (MonoidHom.id A)))
    (hL : CFSG.IsComponent L) (hLs : IsSimpleGroup L) (hLnab : ∃ x y : L, x * y ≠ y * x) :
    ∃ L' : Subgroup ↥((MulAut.congr φ α).toMonoidHom.eqLocus (MonoidHom.id B)),
      CFSG.IsComponent L' ∧ IsSimpleGroup L' ∧ (∃ x y : L', x * y ≠ y * x) ∧
        Nat.card L' = Nat.card L := by
  let Ψ : ↥(α.toMonoidHom.eqLocus (MonoidHom.id A)) ≃*
      ↥((MulAut.congr φ α).toMonoidHom.eqLocus (MonoidHom.id B)) :=
    ((α.toMonoidHom.eqLocus (MonoidHom.id A)).equivMapOfInjective φ.toMonoidHom
      φ.injective).trans
      (MulEquiv.subgroupCongr (CFSG.LocalAnalysis.SteinbergBM.map_eqLocus_mulAut_congr φ α))
  let eL : L ≃* L.map Ψ.toMonoidHom := L.equivMapOfInjective Ψ.toMonoidHom Ψ.injective
  haveI := hLs
  refine ⟨L.map Ψ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv Ψ hL,
    eL.symm.isSimpleGroup, ?_, Subgroup.card_map_of_injective Ψ.injective⟩
  obtain ⟨x, y, hxy⟩ := hLnab
  exact ⟨eL x, eL y, fun h' => hxy (eL.injective
    ((MulEquiv.map_mul eL x y).trans (h'.trans (MulEquiv.map_mul eL y x).symm)))⟩

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.false_of_oddLie_E7
    (h : GomiU42Data X J D E a) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : ChevalleyExceptionalModel ↥D .E7 p f) : False := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hD
  let ψ : ↥D ≃* adjointGroup Tag.E7 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot_field Tag.E7 K)).trans
      QuotientGroup.quotientBot)
  obtain ⟨α, hα2, hα1, hdvd, L, hL, hLs, hLnab, hLcard⟩ :=
    h.exists_involution_aut_simple_component
  obtain ⟨L', hL', hL's, hL'nab, hL'card⟩ :=
    gomi_exists_simple_component_congr ψ α L hL hLs hLnab
  have hβ1 : MulAut.congr ψ α ≠ 1 := fun h1 =>
    hα1 ((MulAut.congr ψ).injective (h1.trans (map_one _).symm))
  have hβ2 : MulAut.congr ψ α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
  have hβd : Nat.card ↥((MulAut.congr ψ α).toMonoidHom.eqLocus
      (MonoidHom.id (adjointGroup Tag.E7 K))) ∣ 51840 := by
    rw [gomi_card_eqLocus_congr ψ α]
    exact hdvd
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  rcases odd_E7_involution_inner_or_quadratic hodd hβ2 with ⟨g, a', hβg⟩ |
    ⟨q, e', hq, he', hFe, δ, hδ, g, a', hβg⟩
  · exact gomi_E7_inner_false hp hp2 hf hK hβg hβ2 L' hL' hL's hL'nab (hL'card.trans hLcard)
  · have hq2 : q ≠ 2 := fun h2 => by
      rw [h2, ← pow_mul] at hFe
      rw [hFe] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' (by omega)).2 even_two)
    exact gomi_quadField_false (Or.inr (Or.inr (Or.inl rfl))) hq hq2 he' hFe δ hδ hβg hβ2 hβd

theorem GomiU42Data.false_of_oddLie_twistedE6
    (h : GomiU42Data X J D E a) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : ChevalleyExceptionalModel ↥D .twistedE6 p f) : False := by
  obtain ⟨⟨-, hf, -⟩, F, _, _, hF, σ₀, hσ₀, ⟨e⟩⟩ := hD
  have : Finite F := ‹_›
  let σ : F ≃+* F := RingEquiv.ofBijective σ₀
    ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  have hσσ₀ : σ.toRingHom = σ₀ := RingHom.ext fun _ => rfl
  have hσ : ∀ c, σ c = c ^ (p ^ f) := hσ₀
  have hF2 : Nat.card F = (p ^ f) ^ 2 := hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨φ⟩, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf F hF2 σ hσ
  rw [← hσσ₀] at e
  let ψ : ↥D ≃* graphFixedRootGroup TwistTag.E6 F σ.toRingHom := e.trans φ
  obtain ⟨α, hα2, hα1, hdvd, L, hL, hLs, hLnab, hLcard⟩ :=
    h.exists_involution_aut_simple_component
  obtain ⟨L', hL', hL's, hL'nab, hL'card⟩ :=
    gomi_exists_simple_component_congr ψ α L hL hLs hLnab
  have hβ2 : MulAut.congr ψ α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
  by_cases hβi : MulAut.congr ψ α ∈ twistedE6Inn F σ
  · exact gomi_twistedE6_inner_false hp hp2 hf F hF2 σ hσ (MulAut.congr ψ α) hβ2 hβi L' hL'
      hL's hL'nab (hL'card.trans hLcard)
  · refine gomi_TwE6_outer_false hp hp2 hf F hF2 σ hσ (MulAut.congr ψ α) hβ2 hβi L' hL' ?_
    rw [hL'card, hLcard]
    norm_num

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
