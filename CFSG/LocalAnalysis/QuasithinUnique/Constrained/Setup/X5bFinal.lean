module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bActor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bOuter

public section

namespace CFSG.QuasithinUnique.Setup.X5

open CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank

theorem evenUnitaryThreeNoOffender_of
    (hN4 : ThreeInvolutionProduct) (hN2 : OuterInverter) :
    EvenUnitaryThreeNoOffender := by
  intro f hf W _ _ hW hnt L₀ A₀ hperf hirr hmodel hA1 hAe hAn
  obtain ⟨⟨hp, hf1, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  let α : L₀ ⧸ Subgroup.center L₀ ≃* unitaryPSU hU 3 :=
    e.trans (unitaryPSUEquiv hU (by norm_num)).symm
  exact (irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders_of hf hU hN4 hN2
    (fun w => by simpa [sq] using hW w) L₀ hperf hirr α).2.2.2.2 A₀ hAn hA1 hAe

theorem irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders
    {f : ℕ} {K : Type} [Field K] (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K)
    {W : Type} [CommGroup W] [Finite W] [Nontrivial W]
    (hW : ∀ w : W, w * w = 1) (L : Subgroup (MulAut W)) (hperf : Group.IsPerfect L)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (α : L ⧸ Subgroup.center L ≃* unitaryPSU h 3) :
    (∃ φ : unitarySU 2 f K 3 →* L, Function.Surjective φ ∧ φ.ker ≤ unitaryScalars h 3 ∧
      (unitaryScalars h 3).map φ = Subgroup.center L ∧
      ∀ s, α (QuotientGroup.mk (φ s)) = unitaryProj h 3 s) ∧
    Nat.card (Subgroup.center L) ∣ Nat.gcd 3 (2 ^ f + 1) ∧
    (∀ t ∈ L, t * t = 1 → t ≠ 1 → 2 ^ (2 * f) ≤ (fixV (Subgroup.zpowers t)).index) ∧
    (∀ a ∈ Subgroup.normalizer (L : Set (MulAut W)), a * a = 1 →
      (¬ ∃ l ∈ L, ∀ x ∈ L, ∃ z ∈ L, (∀ y ∈ L, y * z = z * y) ∧
        a * x * a⁻¹ = l * x * l⁻¹ * z) →
      2 ^ (3 * f) ≤ (fixV (Subgroup.zpowers a)).index) ∧
    (∀ A : Subgroup (MulAut W), A ≤ Subgroup.normalizer (L : Set (MulAut W)) → A ≠ ⊥ →
      IsElemAbelian2 A → Nat.card A * Nat.card (fixV A) < Nat.card W) :=
  irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders_of hf h
    threeInvolutionProduct_holds outerInverter_holds hW L hperf hirr α

theorem evenUnitaryThreeNoOffender
    : EvenUnitaryThreeNoOffender :=
  evenUnitaryThreeNoOffender_of threeInvolutionProduct_holds outerInverter_holds

theorem no_even_unitary_three_component_of_section
    (hSec : ActorComponentSection)
    {V : Type} [CommGroup V] [Finite V] {H T M E : Subgroup (MulAut V)}
    (hA : CFSG.QuasithinUnique.Setup.X35.ActorBase V H T M E) (hns : ¬ Group.IsSolvable H)
    {L : Subgroup (MulAut V)} (hL : CFSG.QuasithinUnique.IsComponentIn L H) (f : ℕ) :
    ¬ StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 3 2 f :=
  no_even_unitary_three_component hSec evenUnitaryThreeNoOffender hA hns hL f

end CFSG.QuasithinUnique.Setup.X5
