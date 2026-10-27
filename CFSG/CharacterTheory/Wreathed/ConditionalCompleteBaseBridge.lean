module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedCharacters
public import CFSG.CharacterTheory.Wreathed.OriginalCoordinates
public import CFSG.CharacterTheory.Wreathed.BaseNormalizer
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseLabels
public import CFSG.CharacterTheory.Wreathed.ConditionalOddFourierCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.ConditionalFiveFixed CFSG.Wreathed.ConditionalOddFourier

theorem wreathModelHom_a_mem_centralizer {G : Type*} [Group G] {n : ℕ} (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.a (2 ^ n)) ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hcen : Original.a (2 ^ n) ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [← Original.Z_eq _ (Nat.one_lt_two_pow (by omega))]
    exact Subgroup.mem_zpowers _
  have hg' : g = wreathModelHom S e (e ⟨g, hg⟩) := by
    simp [wreathModelHom]
  rw [hg', ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen (e ⟨g, hg⟩)]

variable {G : Type} [Group G] [Fintype G] {basis : FiniteIrreducibleCharacterBasis G}
  {B : Finset basis.index} {p A Bq Dq ω : basis.index}

theorem basisCombination_y0 (hprincipal : (basis.representation p).character = 1) (hp : p ∈ B)
    (hA : A ∈ B) (hBq : Bq ∈ B) (hDq : Dq ∈ B) (σ τ₀ κ : ℤ) :
    basisCombination basis B (fun φ => unitVector p φ + σ * unitVector A φ -
      τ₀ * unitVector Bq φ + κ * unitVector Dq φ) =
      1 + (σ : ℂ) • (basis.representation A).character -
        (τ₀ : ℂ) • (basis.representation Bq).character +
        (κ : ℂ) • (basis.representation Dq).character := by
  rw [basisCombination_eq_fun]
  funext x
  rw [Finset.sum_congr rfl fun φ _ => by
      rw [show ((unitVector p φ + σ * unitVector A φ - τ₀ * unitVector Bq φ +
        κ * unitVector Dq φ : ℤ) : ℂ) = ((1 * unitVector p φ + σ * unitVector A φ +
          (-τ₀) * unitVector Bq φ + κ * unitVector Dq φ : ℤ) : ℂ) by push_cast; ring],
    sum_cast_four_mul hp hA hBq hDq]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, hprincipal]
  push_cast
  ring

theorem basisCombination_xj (hprincipal : (basis.representation p).character = 1) (hp : p ∈ B)
    (hA : A ∈ B) (hBq : Bq ∈ B) (hDq : Dq ∈ B) {X₀ : basis.index} (hX₀ : X₀ ∈ B)
    (σ τ₀ κ : ℤ) :
    basisCombination basis B (fun φ => fixedPart p A Bq Dq σ τ₀ κ φ +
      2 * σ * unitVector X₀ φ) =
      -1 - (σ : ℂ) • (basis.representation A).character -
        (τ₀ : ℂ) • (basis.representation Bq).character +
        (κ : ℂ) • (basis.representation Dq).character +
        (2 * σ : ℂ) • (basis.representation X₀).character := by
  rw [basisCombination_eq_fun]
  funext x
  rw [Finset.sum_congr rfl fun φ _ => by
      rw [show ((fixedPart p A Bq Dq σ τ₀ κ φ + 2 * σ * unitVector X₀ φ : ℤ) : ℂ) =
        (((-1) * unitVector p φ + (-σ) * unitVector A φ + (-τ₀) * unitVector Bq φ +
          κ * unitVector Dq φ + (2 * σ) * unitVector X₀ φ : ℤ) : ℂ) by
          rw [fixedPart]; push_cast; ring],
    sum_cast_five_mul hp hA hBq hDq hX₀]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
    Pi.one_apply, hprincipal]
  push_cast
  ring

theorem basisCombination_C (hprincipal : (basis.representation p).character = 1) (hp : p ∈ B)
    (hA : A ∈ B) (hBq : Bq ∈ B) (hDq : Dq ∈ B) (hω : ω ∈ B) (σ τ₀ κ : ℤ) :
    basisCombination basis B (fun φ => unitVector p φ - σ * unitVector A φ -
      τ₀ * unitVector Bq φ - κ * unitVector Dq φ + 2 * τ₀ * unitVector ω φ) =
      1 - (σ : ℂ) • (basis.representation A).character -
        (τ₀ : ℂ) • (basis.representation Bq).character -
        (κ : ℂ) • (basis.representation Dq).character +
        (2 * τ₀ : ℂ) • (basis.representation ω).character := by
  rw [basisCombination_eq_fun]
  funext x
  rw [Finset.sum_congr rfl fun φ _ => by
      rw [show ((unitVector p φ - σ * unitVector A φ - τ₀ * unitVector Bq φ -
        κ * unitVector Dq φ + 2 * τ₀ * unitVector ω φ : ℤ) : ℂ) =
        ((1 * unitVector p φ + (-σ) * unitVector A φ + (-τ₀) * unitVector Bq φ +
          (-κ) * unitVector Dq φ + (2 * τ₀) * unitVector ω φ : ℤ) : ℂ) by push_cast; ring],
    sum_cast_five_mul hp hA hBq hDq hω]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, hprincipal]
  push_cast
  ring

theorem basisCombination_xk (hprincipal : (basis.representation p).character = 1) (hp : p ∈ B)
    (hA : A ∈ B) (hBq : Bq ∈ B) (hDq : Dq ∈ B) {γ : Fin 4 → basis.index} (hγ : ∀ l, γ l ∈ B)
    (σ τ₀ κ : ℤ) (ε : Fin 4 → ℤ) :
    basisCombination basis B (fun φ => fixedPart p A Bq Dq σ τ₀ κ φ +
      ∑ l, ε l * unitVector (γ l) φ) =
      -1 - (σ : ℂ) • (basis.representation A).character -
        (τ₀ : ℂ) • (basis.representation Bq).character +
        (κ : ℂ) • (basis.representation Dq).character +
        ∑ l, (ε l : ℂ) • (basis.representation (γ l)).character := by
  rw [basisCombination_eq_fun]
  funext x
  simp only [Int.cast_add, add_mul, Finset.sum_add_distrib]
  rw [sum_cast_fixedPart_mul hp hA hBq hDq, sum_cast_lincomb_mul hγ]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
    Pi.one_apply, hprincipal, Finset.sum_apply]

theorem basisCombination_yr {γ : Fin 4 → basis.index} (hγ : ∀ l, γ l ∈ B) (ε : Fin 4 → ℤ) :
    basisCombination basis B (fun φ => ∑ l, (quadSign l * ε l) * unitVector (γ l) φ) =
      (ε 0 : ℂ) • (basis.representation (γ 0)).character +
        (ε 1 : ℂ) • (basis.representation (γ 1)).character -
        (ε 2 : ℂ) • (basis.representation (γ 2)).character -
        (ε 3 : ℂ) • (basis.representation (γ 3)).character := by
  rw [basisCombination_eq_fun]
  funext x
  rw [sum_cast_lincomb_mul hγ, Fin.sum_univ_four, quadSign_zero, quadSign_one, quadSign_two,
    quadSign_three]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem basisCombination_diag (hprincipal : (basis.representation p).character = 1)
    (hp : p ∈ B) (hA : A ∈ B) (hω : ω ∈ B) {P Q : basis.index} (hP : P ∈ B) (hQ : Q ∈ B)
    (σ τ₀ κ : ℤ) :
    basisCombination basis B (fun φ => baseFixed p A ω σ τ₀ φ - τ₀ * unitVector P φ -
      κ * unitVector Q φ) =
      1 - (σ : ℂ) • (basis.representation A).character +
        (2 * τ₀ : ℂ) • (basis.representation ω).character -
        (τ₀ : ℂ) • (basis.representation P).character -
        (κ : ℂ) • (basis.representation Q).character := by
  rw [basisCombination_eq_fun]
  funext x
  rw [Finset.sum_congr rfl fun φ _ => by
      rw [show ((baseFixed p A ω σ τ₀ φ - τ₀ * unitVector P φ - κ * unitVector Q φ : ℤ) : ℂ) =
        ((1 * unitVector p φ + (-σ) * unitVector A φ + (2 * τ₀) * unitVector ω φ +
          (-τ₀) * unitVector P φ + (-κ) * unitVector Q φ : ℤ) : ℂ) by
          rw [baseFixed]; push_cast; ring],
    sum_cast_five_mul hp hA hω hP hQ]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, hprincipal]
  push_cast
  ring

theorem basisCombination_gen (hprincipal : (basis.representation p).character = 1)
    (hp : p ∈ B) (hA : A ∈ B) (hω : ω ∈ B) {ψ : basis.index} (hψ : ψ ∈ B) (σ τ₀ ρ₀ : ℤ) :
    basisCombination basis B (fun φ => baseFixed p A ω σ τ₀ φ + ρ₀ * unitVector ψ φ) =
      1 - (σ : ℂ) • (basis.representation A).character +
        (2 * τ₀ : ℂ) • (basis.representation ω).character +
        (ρ₀ : ℂ) • (basis.representation ψ).character := by
  rw [basisCombination_eq_fun]
  funext x
  rw [Finset.sum_congr rfl fun φ _ => by
      rw [show ((baseFixed p A ω σ τ₀ φ + ρ₀ * unitVector ψ φ : ℤ) : ℂ) =
        ((1 * unitVector p φ + (-σ) * unitVector A φ + (2 * τ₀) * unitVector ω φ +
          ρ₀ * unitVector ψ φ : ℤ) : ℂ) by
          rw [baseFixed]; push_cast; ring],
    sum_cast_four_mul hp hA hω hψ]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, hprincipal]
  push_cast
  ring

omit [Group G] [Fintype G] in
theorem quad_relabel {X : Type*} {γ : Fin 4 → X} {ε : Fin 4 → ℤ} {P Q : Fin 2 → X} {τ₀ κ : ℤ}
    (h0 : (P 0 = γ 0 ∧ Q 0 = γ 1) ∨ (P 0 = γ 1 ∧ Q 0 = γ 0))
    (h1 : (P 1 = γ 2 ∧ Q 1 = γ 3) ∨ (P 1 = γ 3 ∧ Q 1 = γ 2))
    (hP : ∀ e l, P e = γ l → ε l = τ₀) (hQ : ∀ e l, Q e = γ l → ε l = -κ) (f : X → G → ℂ) :
    ∑ l, (ε l : ℂ) • f (γ l) = (τ₀ : ℂ) • (f (P 0) + f (P 1)) - (κ : ℂ) • (f (Q 0) + f (Q 1)) ∧
      (ε 0 : ℂ) • f (γ 0) + (ε 1 : ℂ) • f (γ 1) - (ε 2 : ℂ) • f (γ 2) - (ε 3 : ℂ) • f (γ 3) =
        (τ₀ : ℂ) • (f (P 0) - f (P 1)) - (κ : ℂ) • (f (Q 0) - f (Q 1)) := by
  rw [Fin.sum_univ_four]
  rcases h0 with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> rcases h1 with ⟨e2, e3⟩ | ⟨e2, e3⟩
  · rw [hP 0 0 e0, hQ 0 1 e1, hP 1 2 e2, hQ 1 3 e3, e0, e1, e2, e3]
    constructor <;> funext x <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> push_cast <;> ring
  · rw [hP 0 0 e0, hQ 0 1 e1, hP 1 3 e2, hQ 1 2 e3, e0, e1, e2, e3]
    constructor <;> funext x <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> push_cast <;> ring
  · rw [hP 0 1 e0, hQ 0 0 e1, hP 1 2 e2, hQ 1 3 e3, e0, e1, e2, e3]
    constructor <;> funext x <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> push_cast <;> ring
  · rw [hP 0 1 e0, hQ 0 0 e1, hP 1 3 e2, hQ 1 2 e3, e0, e1, e2, e3]
    constructor <;> funext x <;> simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> push_cast <;> ring

end CFSG.Wreathed.ConditionalCompleteBase
