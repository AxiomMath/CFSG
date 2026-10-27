module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleExclusions
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleGraph

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open FourGroupEvenCanonical UnitaryHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem faithful_even_higher_linear_socle_small_source_involution_selector
    {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWsimple : IsSimpleGroup W) (hWnonab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    {p f : ℕ} (_hp : p.Prime) (hp2 : p ≠ 2) (_hf : 1 ≤ f)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    (hWalt : ∀ m : ℕ, 5 ≤ m → IsEmpty (W ≃* alternatingGroup (Fin m)))
    {n e : ℕ} (hn : 3 ≤ n) (he : 1 ≤ e) {K : Type} [Field K] (hK : Nat.card K = 2 ^ e)
    (φ : W ≃* projectiveSL n K) :
    ∃ ρ : A →* MulAut (projectiveSL n K), Function.Injective ρ ∧
      (∀ w : W, ρ w = MulAut.conj (φ w)) ∧
      (∀ ρ' : A →* MulAut (projectiveSL n K), (∀ w : W, ρ' w = MulAut.conj (φ w)) → ρ' = ρ) ∧
      IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
      IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
      ∃ c : GL (Fin n) K,
        (∃ σ : K ≃+* K,
          ((n = 3 ∧ e = 2 ∧ p = 7 ∧ f = 1 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
              ∀ t, σ t = t ^ 2) ∨
            (n = 3 ∧ e = 4 ∧ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 ∧
              StatedClassicalModel L .PSL 3 2 2 ∧ ∀ t, σ t = t ^ 4)) ∧
          (centralizer {fieldAut n K σ} : Set (MulAut (projectiveSL n K))) =
            {α | ∃ (B : GL (Fin n) (fixedField K σ)) (τ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
              α = conjAut n K (subfieldGLMap (Fin n) K (fixedField K σ) B) * fieldAut n K τ *
                dualAut n K ^ ε} ∧
          ρ a = conjAut n K c * fieldAut n K σ * (conjAut n K c)⁻¹ ∧
          (centralizer {a}).map ρ = ρ.range ⊓
            (centralizer {fieldAut n K σ}).map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
          (W ⊓ centralizer {a}).map ρ = inner (projectiveSL n K) ⊓
            (centralizer {fieldAut n K σ}).map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
          L.map ρ = (subfieldConj n σ).range.map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
          Nonempty (L ≃* projectiveSL n (fixedField K σ)) ∧
          centralizer (L : Set A) = zpowers a) ∨
        (let β := dualAut n K
         let O := matrixIsometryGroup ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
         let N := O.map (conjAut n K)
         let N' : Subgroup (MulAut (projectiveSL n K)) := ⁅N, N⁆
         let B := Matrix.toBilin' ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
         let dperp := LinearMap.ker (B fun _ => 1)
         ρ a = conjAut n K c * β * (conjAut n K c)⁻¹ ∧
         (centralizer {a}).map ρ = ρ.range ⊓
           (centralizer {β}).map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
         (W ⊓ centralizer {a}).map ρ = inner (projectiveSL n K) ⊓
           (centralizer {β}).map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
         Function.Injective ((conjAut n K).comp O.subtype) ∧
         (∀ g : O, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun _ => 1) =
           fun _ => 1) ∧
         (∃ R : O ≃* isometryGroup (B.restrict dperp),
           ∀ g w, ((R g).1 w : Fin n → K) = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) ∧
         ((n = 3 ∧ e = 2 ∧ p = 5 ∧ f = 1 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
             (centralizer {β} : Set (MulAut (projectiveSL n K))) =
               {α | ∃ g ∈ O, ∃ (τ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
                 α = conjAut n K g * fieldAut n K τ * β ^ ε} ∧
             Nonempty (isometryGroup (B.restrict dperp) ≃* StatedSp 1 K) ∧
             Nonempty (isometryGroup (B.restrict dperp) ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
             L.map ρ = N.map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
             Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∨
           (n = 5 ∧ e = 1 ∧ p = 3 ∧ f = 2 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
             (centralizer {β} : Set (MulAut (projectiveSL n K))) =
               {α | ∃ g ∈ O, ∃ ε : ℕ, ε ≤ 1 ∧ α = conjAut n K g * β ^ ε} ∧
             Nonempty (isometryGroup (B.restrict dperp) ≃* StatedSp 2 K) ∧
             (∃ E : N ≃* PresentationLocal.sympFour, ∀ x : N,
               (x : MulAut (projectiveSL n K)) ∈ N' ↔
                 PresentationLocal.omegaPerm (E x) ∈ alternatingGroup (Fin 6)) ∧
             Nonempty (N ≃* Equiv.Perm (Fin 6)) ∧ Nonempty (N' ≃* alternatingGroup (Fin 6)) ∧
             L.map ρ = N'.map (MulAut.conj (conjAut n K c)).toMonoidHom ∧
             Nonempty (L ≃* alternatingGroup (Fin 6))))) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : IsSimpleGroup (projectiveSL n K) := φ.symm.isSimpleGroup
  have hnabP : ∃ x y : projectiveSL n K, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnonab
    refine ⟨φ x, φ y, fun hc => hxy (φ.injective ?_)⟩
    rw [map_mul, map_mul, hc]
  have hZ := center_eq_bot_of_isSimpleGroup hnabP
  obtain ⟨ρ, hinj, hρW, huniq, -⟩ := socle_extension hCW φ hZ
  have hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}) :=
    isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
  have hLnab := exists_ne_commute_of_isQuasisimple hL.2.2
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨Aₘ, σ, ε, hε, hρa⟩ := hform (ρ a)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hρa
      exact (linear_socle_inner_false ha hLCW hn he hK φ hinj hρW hZ hρa).elim
    · obtain ⟨c, hrows, hCset, hρa', hCA, hCW, hLimg, hLiso, hcent, hLs, hA7⟩ :=
        linear_socle_field_case ha hLCW hn he hK φ hinj hρW hσ hρa hp2 hsrc
      exact ⟨ρ, hinj, hρW, huniq, hLs, hLnab, hA7, c,
        Or.inl ⟨σ, hrows, hCset, hρa', hCA, hCW, hLimg, hLiso, hcent⟩⟩
  · rw [pow_one] at hρa
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hρa
      obtain ⟨c, hG, hLs, hA7⟩ :=
        linear_socle_pure_graph_case ha hLCW hn he hK φ hinj hρW hWalt hρa hp2 hsrc
      exact ⟨ρ, hinj, hρW, huniq, hLs, hLnab, hA7, c, Or.inr hG⟩
    · exact (linear_socle_graph_field_false ha hLCW hn he hK φ hinj hρW hσ hρa hp2 hsrc).elim

end CFSG.ComponentClassification.OutcomeLocal
