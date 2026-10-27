module

public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Steinberg.Minuscule.CertInputs
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8.F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction

@[expose] def e8fRoot (k : ℕ) : Fin (Tag.rank .E7) → ℤ := (Tag.rootCertificate .E7).root k

abbrev e8fTh : Fin (Tag.rank .E7) → ℤ := MinData.toWeight (highRoot .E7)

@[expose] def e8fGrade (b : Fin e7Data.d) : ℤ := ![2, 3, 4, 6, 5, 4, 3] ⬝ᵥ e7Data.wt b

open Classical in
@[expose] noncomputable def e8fIdx (w : Fin (Tag.rank .E7) → ℤ) : Fin e7Data.d :=
  if h : ∃ a : Fin e7Data.d, e7Data.wt a = w then h.choose else ⟨0, by decide⟩

@[expose] def e8fStep (J : List (Fin (Tag.rank .E7))) (S : List ℕ) : List ℕ :=
  (S ++ S.flatMap fun a => J.map fun i => e7Data.weyl a i).eraseDups

@[expose] def e8fReach (J : List (Fin (Tag.rank .E7))) (a₀ : ℕ) : ℕ → List ℕ
  | 0 => [a₀]
  | N + 1 => e8fStep J (e8fReach J a₀ N)

theorem wt_injective : ∀ a b : Fin e7Data.d, e7Data.wt a = e7Data.wt b → a = b := by
  decide +kernel

theorem wt_idx {w : Fin (Tag.rank .E7) → ℤ} (h : ∃ a : Fin e7Data.d, e7Data.wt a = w) :
    e7Data.wt (e8fIdx w) = w := by
  rw [e8fIdx, dif_pos h]
  exact h.choose_spec

theorem idx_wt (a : Fin e7Data.d) : e8fIdx (e7Data.wt a) = a :=
  wt_injective _ _ (wt_idx ⟨a, rfl⟩)

theorem wt_ne_neg : ∀ a : Fin e7Data.d, e7Data.wt a ≠ -e7Data.wt a := by decide +kernel

theorem exists_op : ∀ a : Fin e7Data.d, ∃ b : Fin e7Data.d, e7Data.wt b = -e7Data.wt a := by
  decide +kernel

theorem grade_cases : ∀ b : Fin e7Data.d,
    e8fGrade b = 3 ∨ e8fGrade b = 1 ∨ e8fGrade b = -1 ∨ e8fGrade b = -3 := by decide +kernel

theorem grade_eq_neg_three : ∀ b : Fin e7Data.d, e8fGrade b = -3 →
    e7Data.wt b = -e7Data.wt 0 := by decide +kernel

theorem wt_zero_th : e7Data.wt 0 ⬝ᵥ highRoot .E7 = 1 := by decide +kernel

theorem exists_grade_one : ∃ b : Fin e7Data.d, e8fGrade b = 1 := by decide +kernel

@[expose] def e8fMu : ℕ :=
  ((List.range e7Data.d).find? fun b => decide (e7Data.wt b = e8fTh - e7Data.wt 0)).getD 0

theorem e8fMu_lt : e8fMu < e7Data.d := by decide +kernel

theorem wt_e8fMu : e7Data.wt e8fMu = e8fTh - e7Data.wt 0 := by decide +kernel

theorem th_dot_th : e8fTh ⬝ᵥ highRoot .E7 = 2 := by decide +kernel

theorem star_exists : ∀ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = 1 →
    ∃ b : Fin e7Data.d, e7Data.wt b = e8fTh - e7Data.wt a := by decide +kernel

theorem star_ne : ∀ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = 1 →
    e7Data.wt a ≠ e8fTh - e7Data.wt a := by decide +kernel

theorem reach_th : ∀ a b : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = 1 →
    e7Data.wt b ⬝ᵥ highRoot .E7 = 1 →
      (b : ℕ) ∈ e8fReach ((List.finRange (Tag.rank .E7)).drop 1) a 10 := by
  decide +kernel

theorem reach_grade_neg_one : ∀ b : Fin e7Data.d, e8fGrade b = -1 →
    e8fMu ∈ e8fReach ((List.finRange (Tag.rank .E7)).take 6) b 16 := by
  decide +kernel

section Roots

theorem e8fRoot_isRoot {k : ℕ} (hk : k < 126) : IsRoot .E7 (e8fRoot k) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)

theorem exists_e8fRoot_eq {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    ∃ k < 126, e8fRoot k = β := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, hkβ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hβ
  exact ⟨k, by omega, hkβ⟩

theorem forall_root_of_listed {P : (Fin (Tag.rank .E7) → ℤ) → Prop}
    (h : ∀ k ∈ List.range 126, P (e8fRoot k)) {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    P β := by
  obtain ⟨k, hk, rfl⟩ := exists_e8fRoot_eq hβ
  exact h k (List.mem_range.2 hk)

theorem not_isRoot_of_listed {β : Fin (Tag.rank .E7) → ℤ}
    (h : ∀ j ∈ List.range 126, e8fRoot j ≠ β) : ¬ IsRoot .E7 β := fun hβ => by
  obtain ⟨k, hk, hkβ⟩ := exists_e8fRoot_eq hβ
  exact h k (List.mem_range.2 hk) hkβ

end Roots

theorem tw_dot_self_listed : ∀ k ∈ List.range 126,
    MinData.toWeight (e8fRoot k) ⬝ᵥ e8fRoot k = 2 := by decide +kernel

theorem two_wt_ne_listed : ∀ k ∈ List.range 126, ∀ a : Fin e7Data.d,
    e7Data.wt a + e7Data.wt a + MinData.toWeight (e8fRoot k) ≠ 0 := by decide +kernel

theorem th_cases_listed : ∀ k ∈ List.range 126, 0 < height (e8fRoot k) →
    e8fTh ⬝ᵥ e8fRoot k = 0 ∨ e8fTh ⬝ᵥ e8fRoot k = 1 ∨ e8fTh ⬝ᵥ e8fRoot k = 2 := by
  decide +kernel

theorem siegel_irr_listed : ∀ k ∈ List.range 126, e8fTh ⬝ᵥ e8fRoot k = 0 →
    ∀ a : Fin e7Data.d,
      e7Data.wt a + e7Data.wt a + MinData.toWeight (e8fRoot k) ≠ e8fTh := by decide +kernel

theorem triv_listed : ∀ k ∈ List.range 126, 1 ≤ e8fTh ⬝ᵥ e8fRoot k → ∀ a : Fin e7Data.d,
    e7Data.wt a ⬝ᵥ highRoot .E7 = 1 → e7Data.wt a ⬝ᵥ e8fRoot k ≠ -1 := by decide +kernel

theorem tw_dot_th_listed : ∀ k ∈ List.range 126,
    MinData.toWeight (e8fRoot k) ⬝ᵥ highRoot .E7 = e8fTh ⬝ᵥ e8fRoot k := by decide +kernel

theorem zero_shift_grade_listed : ∀ k ∈ List.range 126, e7Data.wt 0 ⬝ᵥ e8fRoot k = -1 →
    ∀ b : Fin e7Data.d, e7Data.wt b = e7Data.wt 0 + MinData.toWeight (e8fRoot k) →
      0 < e8fGrade b := by decide +kernel

theorem plane_listed : ∀ k ∈ List.range 126,
    (∃ j ∈ List.range 126, e8fRoot j = highRoot .E7 + e8fRoot k) →
    ∃ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = 1 ∧ e7Data.wt a ⬝ᵥ e8fRoot k = 0 := by
  decide +kernel

theorem cn_listed : ∀ i : Fin (Tag.rank .E7), i ≠ ⟨0, by decide⟩ →
    (∀ j ∈ List.range 126, e8fRoot j ≠ highRoot .E7 + Pi.single i 1) ∧
    (∀ j ∈ List.range 126, e8fRoot j ≠ highRoot .E7 + -Pi.single i 1) ∧
    (highRoot .E7 + Pi.single i 1 ≠ 0) ∧ (highRoot .E7 + -Pi.single i 1 ≠ 0) := by
  decide +kernel

@[expose] def e8fLam (k : ℕ) : List (Fin e7Data.d) :=
  (List.finRange e7Data.d).filter fun a =>
    decide (e7Data.wt a ⬝ᵥ highRoot .E7 = 1 ∧ e7Data.wt a ⬝ᵥ e8fRoot k = 1)

theorem mem_e8fLam {k : ℕ} {a : Fin e7Data.d} :
    a ∈ e8fLam k ↔ e7Data.wt a ⬝ᵥ highRoot .E7 = 1 ∧ e7Data.wt a ⬝ᵥ e8fRoot k = 1 := by
  simp [e8fLam]

theorem comm_case_listed : ∀ k ∈ List.range 126, e8fRoot k ≠ highRoot .E7 → e8fLam k ≠ [] →
    (e8fRoot k ≠ -highRoot .E7 ∧ ∀ j ∈ List.range 126, e8fRoot j ≠ highRoot .E7 + e8fRoot k) := by
  decide +kernel

theorem clique_exists_listed : ∀ k ∈ List.range 126, e8fRoot k ≠ highRoot .E7 →
    ∀ μ ∈ e8fLam k, ∀ l ∈ e8fLam k, μ ≠ l →
      ∃ j ∈ List.range 126, e7Data.wt l = e7Data.wt μ + MinData.toWeight (e8fRoot j) := by
  decide +kernel

theorem clique_moves_listed : ∀ k ∈ List.range 126, e8fRoot k ≠ highRoot .E7 →
    ∀ μ ∈ e8fLam k, ∀ l ∈ e8fLam k, μ ≠ l → ∀ j ∈ List.range 126,
      e7Data.wt l = e7Data.wt μ + MinData.toWeight (e8fRoot j) →
        e7Data.wt μ ⬝ᵥ e8fRoot j = -1 := by
  decide +kernel

theorem clique_fix_listed : ∀ k ∈ List.range 126, e8fRoot k ≠ highRoot .E7 →
    ∀ μ ∈ e8fLam k, ∀ l ∈ e8fLam k, μ ≠ l → ∀ j ∈ List.range 126,
      e7Data.wt l = e7Data.wt μ + MinData.toWeight (e8fRoot j) →
        ∀ ν ∈ e8fLam k, ν ≠ μ → ν ≠ l → e7Data.wt ν ⬝ᵥ e8fRoot j ≠ -1 := by
  decide +kernel

end CFSG.GF2Type.SmithTypeE.E8.F
