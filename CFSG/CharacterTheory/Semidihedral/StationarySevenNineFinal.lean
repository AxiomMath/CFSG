module

public import CFSG.CharacterTheory.Semidihedral.StationarySevenNineRegular
public import CFSG.CharacterTheory.Semidihedral.StationaryConfinementFixedFactor

public section

namespace CFSG.Semidihedral.StationarySevenNine

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.StationaryConfinement

theorem stationaryConfinementStatement_holds
    : StationaryConfinementStatement :=
  @stationary_all_local_prime_covers_confine_every_nontrivial_odd_core_element
   

theorem stationaryFixedFactorStatement_holds
    : StationaryFixedFactorStatement :=
  @stationary_all_prime_odd_core_has_cyclic_fixed_factor_and_fixed_free_complement_action
   

theorem stationary_all_prime_seven_nine_odd_core_is_cyclic_and_central
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : p ^ f = 7 ∨ p ^ f = 9)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G)) :
    let s₀ : G := fS (s n)
    let e : ℤ := if p ^ f = 7 then -1 else 1
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Na := (N t).map (C t).subtype
    let Ja := J.map (C t).subtype
    let A₀ := Na ⊓ Subgroup.centralizer ({s₀} : Set G)
    let JS := Ja ⊔ Subgroup.zpowers s₀
    let a₀ := Nat.card A₀
    n = 5 ∧ (∀ x ∈ Na, s₀ * x * s₀⁻¹ = x⁻¹ → x = 1) ∧ E = ⊥ ∧ Na = A₀ ∧ IsCyclic Na ∧
      Nat.card Na = a₀ ∧ (a₀ : ℤ) ∣ ((p ^ f : ℕ) + e) / 2 ∧
      (p ^ f = 7 → a₀ = 1 ∨ a₀ = 3) ∧ (p ^ f = 9 → a₀ = 1 ∨ a₀ = 5) ∧
      (∃ φ : J ≃* T₀, ∀ x : J, (φ x : H t) = nu t x) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (T₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      (Y = J ⊔ N t ∧ J ⊓ N t = ⊥ ∧ ∀ x ∈ J, ∀ y ∈ N t, Commute x y) ∧
      (JS ⊔ Na = C t ∧ JS ⊓ Na = ⊥ ∧ ∀ x ∈ JS, ∀ y ∈ Na, Commute x y) ∧
      N t ≤ Subgroup.center (C t) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (a : Fˣ), Nat.card F = p ^ f ∧
        ¬ IsSquare a ∧ Nonempty (JS ≃* MatrixCoverData.M F a)) ∧
      (p ^ f = 7 → Nat.card G = 2328480 * a₀ ∨ Nat.card G = 1876896 * a₀) ∧
      (p ^ f = 9 → Nat.card G = 8514720 * a₀ ∨ Nat.card G = 6441120 * a₀ ∨
        Nat.card G = 7236000 * a₀) :=
  stationary_all_prime_seven_nine_odd_core_is_cyclic_and_central_of_confinement
    stationaryConfinementStatement_holds stationaryFixedFactorStatement_holds hGnonab
    hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov

theorem stationary_all_prime_parameter_nine_with_nontrivial_odd_core_is_regular
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : p ^ f = 9)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hcov : EscapingLocalEigensubgroups.allLocalPrimeStationaryCovers t (fS (s n) : G))
    (hN : N t ≠ ⊥) :
    let s₀ : G := fS (s n)
    let T₀ := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    let Y := T₀.comap (nu t)
    let H₀ := Y ⊓ Subgroup.centralizer (N t : Set (C t))
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ N t
    let Na := (N t).map (C t).subtype
    let c := Nat.card (C t)
    let d := Nat.card ↥(C t ⊓ Subgroup.centralizer ({s₀} : Set G))
    N t ≤ Subgroup.center (C t) ∧ IsCyclic Na ∧ Nat.card Na = 5 ∧
      (∀ x ∈ Na, s₀ * x * s₀⁻¹ = x⁻¹ → x = 1) ∧ E = ⊥ ∧ n = 5 ∧
      c = 7200 ∧ d = 100 ∧ Nat.card G = 42573600 ∧ (C t).index = 5913 ∧
      padicValNat 3 (Nat.card G) = 6 ∧
      (padicValNat 3 (Nat.card G) : ℤ) = 3 * padicValNat 3 c - 2 * padicValNat 3 d :=
  stationary_all_prime_parameter_nine_with_nontrivial_odd_core_is_regular_of_confinement
    stationaryConfinementStatement_holds stationaryFixedFactorStatement_holds hGnonab
    hrecognition n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hcov hN

end CFSG.Semidihedral.StationarySevenNine
