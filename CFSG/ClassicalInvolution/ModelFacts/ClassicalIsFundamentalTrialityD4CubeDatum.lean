module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedDatum

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.CatalogueBPrimeJoin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

theorem mul_sq_sub_one_lt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [ha2, hb2]
  have : (a : ℤ) < b := by exact_mod_cast hab
  have : (1 : ℤ) ≤ a := by exact_mod_cast ha
  nlinarith [mul_pos (by linarith : (0 : ℤ) < a) (by linarith : (0 : ℤ) < b)]

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem exists_eq_range_orbitMapHom_of_isPComponent_cube (hX : Finite D.totalFixedGroup)
    (hsingle : ∀ J' : Set.range D.classOrbit, ∃ O₀, (D.withOrbit J').orbits = {O₀})
    (hsize : ∀ J' : Set.range D.classOrbit, ∀ O ∈ (D.withOrbit J').orbits, orbitCard O ≤ 3)
    {J₀ : Subgroup (adjointGroup τ k)} (hle : J₀ ≤ D.totalFixedGroup)
    (hJ₀ : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup))
    {Y : Type} [Group Y] (φ : Y ≃* J₀) (O : Subgroup Y) [O.Normal]
    {F₂ : Type} [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = D.q ^ 3)
    (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ (J' : Set.range D.classOrbit) (O₀ : Set (Fin τ.rank → ℤ))
      (hO₀ : O₀ ∈ (D.withOrbit J').orbits),
      (D.withOrbit J').orbits = {O₀} ∧ orbitCard O₀ = 3 ∧
        J₀ = ((D.withOrbit J').orbitMapHom hO₀).range.subgroupOf (adjointGroup τ k) := by
  obtain ⟨J', hJ', hq⟩ := exists_eq_orbitGroupC_of_isPComponent D hX hle hJ₀
  have hfinJ : Finite J₀ := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hfinY : Finite Y := Finite.of_equiv _ φ.symm.toEquiv
  let eC : (D.withOrbit J').orbitGroupC ≃* (D.withOrbit J').orbitGroup :=
    Subgroup.subgroupOfEquivOfLe (D.withOrbit J').orbitGroup_le_adjointGroup
  let φ' : Y ≃* (D.withOrbit J').orbitGroup := (φ.trans (MulEquiv.subgroupCongr hJ')).trans eC
  obtain ⟨O₀, hA⟩ := hsingle J'
  have hO₀ : O₀ ∈ (D.withOrbit J').orbits := by
    rw [hA]
    exact Set.mem_singleton O₀
  have hsurj := (D.withOrbit J').orbitGroupHom_surjective hO₀ hA
  have hfinK := finite_orbitField (D.withOrbit J') hO₀
  have hq3 : 3 ≤ D.q := D.three_le_q
  have hdle : orbitCard O₀ ≤ 3 := hsize J' O₀ hO₀
  have hdpos : 0 < orbitCard O₀ := (D.withOrbit J').orbitCard_pos hO₀
  have hcardK : Nat.card ((D.withOrbit J').orbitField O₀) = D.q ^ orbitCard O₀ :=
    (D.withOrbit J').card_orbitField hO₀
  have hYle : Nat.card Y ≤ Nat.card (SL2 ((D.withOrbit J').orbitField O₀)) := by
    have h1 : Nat.card Y = Nat.card (D.withOrbit J').orbitGroup := Nat.card_congr φ'.toEquiv
    rw [h1]
    exact Nat.card_le_card_of_surjective _ hsurj
  have hYge : Nat.card (SL(2, F₂)) ≤ Nat.card Y := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup O
    have h2 : Nat.card (Y ⧸ O) = Nat.card SL(2, F₂) := Nat.card_congr eY.toEquiv
    have hpos : 0 < Nat.card O := Nat.card_pos
    rw [h1, ← h2]
    exact Nat.le_mul_of_pos_right _ hpos
  rw [CFSG.GorensteinWalter.sl2_card_formula, hF₂] at hYge
  rw [CFSG.GorensteinWalter.sl2_card_formula, hcardK] at hYle
  have hd3 : orbitCard O₀ = 3 := by
    by_contra hne
    have hlt : orbitCard O₀ < 3 := by omega
    have hq1 : 1 ≤ D.q ^ orbitCard O₀ := Nat.one_le_pow _ _ (by omega)
    have hlt' : D.q ^ orbitCard O₀ < D.q ^ 3 := Nat.pow_lt_pow_right (by omega) hlt
    have := mul_sq_sub_one_lt hq1 hlt'
    omega
  refine ⟨J', O₀, hO₀, hA, hd3, ?_⟩
  rw [hJ']
  show (D.withOrbit J').orbitGroup.subgroupOf (adjointGroup τ k) = _
  congr 1
  refine SetLike.coe_injective ?_
  rw [← (D.withOrbit J').range_orbitMap_eq_of_orbits_eq hA]
  rfl

end CFSG.ClassicalInvolution.ModelFacts
