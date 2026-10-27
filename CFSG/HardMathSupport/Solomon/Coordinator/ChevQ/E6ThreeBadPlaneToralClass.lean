module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralMat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerFrame
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.E6.StdF4RadicalRoots
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Norm

variable {K : Type*} [Field K]

theorem diagonal_mul_signedCycMat_sq_pow_three (d : Fin 3 → K) :
    (diagonal d * signedCycMat ^ 2 : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d 0 * d 1 * d 2) • 1 := by
  rw [signedCycMat_sq, pow_succ, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  all_goals first | ring1 | (left; ring1)

theorem diagonal_mul_signedCycMat_pow_cube (d : Fin 3 → K) {n : ℕ} (hn : ¬ 3 ∣ n) :
    (diagonal d * signedCycMat ^ n : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d 0 * d 1 * d 2) • 1 := by
  rw [pow_eq_pow_mod n (signedCycMat_pow_three (K := K))]
  have h : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h
  · rw [h, pow_one]
    exact diagonal_mul_signedCycMat_pow_three d
  · rw [h]
    exact diagonal_mul_signedCycMat_sq_pow_three d

theorem exists_norm_form (hζ : ∃ ζ : K, IsPrimitiveRoot ζ 3) {γ : GL (Fin 3) K} {α : K}
    (hγ : (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1) :
    ∃ (z : SpecialLinearGroup (Fin 3) K) (d : Fin 3 → K) (n : ℕ),
      ((SpecialLinearGroup.toGL z * γ * (SpecialLinearGroup.toGL z)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat ^ n ∧
      ((∀ μ : K, μ ^ 3 ≠ α) → ¬ 3 ∣ n ∧ d 0 * d 1 * d 2 = α) ∧
      ((∃ μ : K, μ ^ 3 = α) → n = 0) := by
  by_cases hc : ∃ μ : K, μ ^ 3 = α
  · obtain ⟨μ, hμ⟩ := hc
    obtain ⟨z, hz⟩ := exists_SL_conj_offDiag_eq_zero_of_cube hζ hγ hμ
    set M : Matrix (Fin 3) (Fin 3) K :=
      ((SpecialLinearGroup.toGL z * γ * (SpecialLinearGroup.toGL z)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) with hM
    refine ⟨z, fun a => M a a, 0, ?_, fun h => absurd hμ (h μ), fun _ => rfl⟩
    rw [pow_zero, Matrix.mul_one]
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact hz a b hab
  · obtain ⟨z, d, k, hk, hconj⟩ :=
      exists_conj_cyclic_of_not_cube hζ hγ (fun μ hμ => hc ⟨μ, hμ⟩)
    refine ⟨z, d, k, hconj, fun _ => ⟨hk, ?_⟩, fun h => absurd h hc⟩
    have h3 : ((SpecialLinearGroup.toGL z * γ * (SpecialLinearGroup.toGL z)⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := by
      have e : (SpecialLinearGroup.toGL z * γ * (SpecialLinearGroup.toGL z)⁻¹) ^ 3 =
          SpecialLinearGroup.toGL z * γ ^ 3 * (SpecialLinearGroup.toGL z)⁻¹ := conj_pow
      rw [← Units.val_pow_eq_pow_val, e, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
        hγ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
        Units.val_one]
    rw [hconj, diagonal_mul_signedCycMat_pow_cube d hk] at h3
    have := congrFun (congrFun h3 0) 0
    simpa using this

end Norm

section Class

variable {K : Type} [Field K]

theorem rootChar_cartanChar_prod {τ : Tag} (c : Fin τ.rank → Kˣ) (β : Fin τ.rank → ℤ) :
    rootChar (cartanChar c) β = ∏ j, c j ^ (∑ l, τ.cartan j l * β l) := by
  simp only [rootChar, cartanChar, ← Finset.prod_zpow, ← _root_.zpow_mul]
  rw [Finset.prod_comm]
  simp only [Finset.prod_zpow_eq_zpow_sum]

@[expose] def e6DetChar (c : Fin Tag.E6.rank → Kˣ) (i : Fin 3) : Kˣ :=
  rootChar c (-(e6LinePair i).1) * rootChar c (-((e6LinePair i).1 + (e6LinePair i).2))

theorem rootChar_cartanChar_eq_prod_six (c : Fin Tag.E6.rank → Kˣ) (β : Fin Tag.E6.rank → ℤ) :
    rootChar (cartanChar c) β =
      c 0 ^ (∑ l, Tag.cartan .E6 0 l * β l) * c 1 ^ (∑ l, Tag.cartan .E6 1 l * β l) *
        c 2 ^ (∑ l, Tag.cartan .E6 2 l * β l) * c 3 ^ (∑ l, Tag.cartan .E6 3 l * β l) *
          c 4 ^ (∑ l, Tag.cartan .E6 4 l * β l) * c 5 ^ (∑ l, Tag.cartan .E6 5 l * β l) := by
  rw [rootChar_cartanChar_prod]
  exact Fin.prod_univ_six (fun j : Fin 6 => c j ^ (∑ l, Tag.cartan .E6 j l * β l))

theorem e6DetChar_classes (t : Fin Tag.E6.rank → Kˣ) :
    ∃ g a₀ a₁ a₂ : Kˣ, e6DetChar (cartanChar t) 0 = g * a₀ ^ 3 ∧
      e6DetChar (cartanChar t) 1 = g⁻¹ * a₁ ^ 3 ∧ e6DetChar (cartanChar t) 2 = g * a₂ ^ 3 := by
  have key : ∀ (i : Fin 3) (n₀ n₁ n₂ n₃ n₄ n₅ : ℤ),
      ∑ l, Tag.cartan .E6 0 l * (-(e6LinePair i).1 + -((e6LinePair i).1 + (e6LinePair i).2)) l
        = n₀ →
      ∑ l, Tag.cartan .E6 1 l * (-(e6LinePair i).1 + -((e6LinePair i).1 + (e6LinePair i).2)) l
        = n₁ →
      ∑ l, Tag.cartan .E6 2 l * (-(e6LinePair i).1 + -((e6LinePair i).1 + (e6LinePair i).2)) l
        = n₂ →
      ∑ l, Tag.cartan .E6 3 l * (-(e6LinePair i).1 + -((e6LinePair i).1 + (e6LinePair i).2)) l
        = n₃ →
      ∑ l, Tag.cartan .E6 4 l * (-(e6LinePair i).1 + -((e6LinePair i).1 + (e6LinePair i).2)) l
        = n₄ →
      ∑ l, Tag.cartan .E6 5 l * (-(e6LinePair i).1 + -((e6LinePair i).1 + (e6LinePair i).2)) l
        = n₅ →
      e6DetChar (cartanChar t) i =
        t 0 ^ n₀ * t 1 ^ n₁ * t 2 ^ n₂ * t 3 ^ n₃ * t 4 ^ n₄ * t 5 ^ n₅ := by
    intro i n₀ n₁ n₂ n₃ n₄ n₅ h₀ h₁ h₂ h₃ h₄ h₅
    rw [e6DetChar, ← rootChar_add, rootChar_cartanChar_eq_prod_six, h₀, h₁, h₂, h₃, h₄, h₅]
  refine ⟨t 3, (t 0)⁻¹, t 3 * (t 4)⁻¹, (t 1)⁻¹, ?_, ?_, ?_⟩
  · rw [key 0 (-3) 0 0 1 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    simp [_root_.zpow_neg, inv_pow, mul_pow, mul_comm, pow_succ, mul_assoc, mul_left_comm]
  · rw [key 1 0 0 0 2 (-3) 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    simp [_root_.zpow_neg, inv_pow, mul_pow, mul_comm, pow_succ, mul_assoc, mul_left_comm]
  · rw [key 2 0 (-3) 0 1 0 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    simp [_root_.zpow_neg, inv_pow, mul_pow, mul_comm, pow_succ, mul_assoc, mul_left_comm]

theorem exists_cube_iff_of_eq {g a q : Kˣ} (h : q = g * a ^ 3) :
    (∃ m : Kˣ, m ^ 3 = q) ↔ ∃ m : Kˣ, m ^ 3 = g := by
  subst h
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m * a⁻¹, by rw [mul_pow, inv_pow, hm]; group⟩
  · rintro ⟨m, hm⟩
    exact ⟨m * a, by rw [mul_pow, hm]⟩

theorem exists_cube_inv_iff (g : Kˣ) : (∃ m : Kˣ, m ^ 3 = g⁻¹) ↔ ∃ m : Kˣ, m ^ 3 = g := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m⁻¹, by rw [inv_pow, hm, inv_inv]⟩
  · rintro ⟨m, hm⟩
    exact ⟨m⁻¹, by rw [inv_pow, hm]⟩

theorem forall_cube_ne_iff (q : Kˣ) :
    (∀ μ : K, μ ^ 3 ≠ (q : K)) ↔ ¬ ∃ m : Kˣ, m ^ 3 = q := by
  constructor
  · rintro h ⟨m, hm⟩
    exact h m (by rw [← Units.val_pow_eq_pow_val, hm])
  · intro h μ hμ
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact q.ne_zero (by rw [← hμ]; ring)
    exact h ⟨Units.mk0 μ hμ0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ])⟩

theorem e6DetChar_not_cube_spread (t : Fin Tag.E6.rank → Kˣ) {j : Fin 3}
    (h : ∀ μ : K, μ ^ 3 ≠ ((e6DetChar (cartanChar t) j : Kˣ) : K)) (i : Fin 3) :
    ∀ μ : K, μ ^ 3 ≠ ((e6DetChar (cartanChar t) i : Kˣ) : K) := by
  obtain ⟨g, a₀, a₁, a₂, h0, h1, h2⟩ := e6DetChar_classes t
  have hcls : ∀ i : Fin 3, (∃ m : Kˣ, m ^ 3 = e6DetChar (cartanChar t) i) ↔
      ∃ m : Kˣ, m ^ 3 = g := by
    intro i
    fin_cases i
    · exact exists_cube_iff_of_eq h0
    · exact (exists_cube_iff_of_eq h1).trans (exists_cube_inv_iff g)
    · exact exists_cube_iff_of_eq h2
  rw [forall_cube_ne_iff] at h ⊢
  intro hi
  exact h ((hcls j).2 ((hcls i).1 hi))

end Class

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
