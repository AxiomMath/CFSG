module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocBase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdEven
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.ComponentClassification.GSThmB.Soc

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem factorial_ne_of_lt {k c : ℕ} (hk : k.factorial < c) (hk1 : c < (k + 1).factorial)
    (m : ℕ) : m.factorial ≠ c := by
  intro h
  rcases le_or_gt m k with hm | hm
  · have := Nat.factorial_le hm
    omega
  · have := Nat.factorial_le (show k + 1 ≤ m by omega)
    omega

theorem isEmpty_alt_of_card {X : Type} [Group X] {c : ℕ} (hX : Nat.card X = c)
    (hc : ∀ m : ℕ, m.factorial ≠ 2 * c) :
    ∀ m : ℕ, 5 ≤ m → IsEmpty (X ≃* alternatingGroup (Fin m)) := by
  intro m hm
  refine ⟨fun φ => ?_⟩
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin m)
  rw [← Nat.card_congr φ.toEquiv, hX, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h2
  exact hc m h2.symm

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {α : G} {J : Subgroup G}

namespace Hyp

theorem selector (h : Hyp N α J) {n e : ℕ} (hm : Blueprint.LieModel N .PSL n 2 e) (hn : 3 ≤ n)
    (hWalt : ∀ m : ℕ, 5 ≤ m → IsEmpty (N ≃* alternatingGroup (Fin m))) :
    n = 3 ∧ e = 4 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : N ≃* projectiveSL n K)
      (ρ : G →* MulAut (projectiveSL n K)) (c : GL (Fin n) K) (σ : K ≃+* K),
      Nat.card K = 2 ^ e ∧ Function.Injective ρ ∧ (∀ w : N, ρ w = MulAut.conj (φ w)) ∧
        (∀ t, σ t = t ^ 4) ∧ ρ α = conjAut n K c * fieldAut n K σ * (conjAut n K c)⁻¹ := by
  obtain ⟨⟨-, he, -⟩, K, _, _, hK, ⟨φ₀⟩⟩ := RestrictedStd.statedClassicalModel_of_lieModel_PSL hm
  let φ : N ≃* projectiveSL n K := φ₀.trans (SymmetricLocal.statedProjEquivProjectiveSL n K)
  have hsrc : StatedClassicalModel (↥J ⧸ center ↥J) .PSL 2 3 1 ∨
      Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (↥J ⧸ center ↥J) .PSL 3 2 2 :=
    Or.inr (Or.inr (RestrictedStd.statedClassicalModel_of_lieModel_PSL h.lie))
  have hcomp : Assembly.IsComponentOf J (centralizer ({α} : Set G)) :=
    (isComponentOf_iff_isComponent_subgroupOf h.le_C).mpr h.component
  obtain ⟨ρ, hinj, hρW, -, -, -, -, c, hrows⟩ :=
    OutcomeLocal.faithful_even_higher_linear_socle_small_source_involution_selector h.simple
      h.nonabelian h.centralizer_eq h.order_two h.le_N hcomp Nat.prime_three (by decide) le_rfl
      hsrc hWalt hn he hK φ
  rcases hrows with ⟨σ, hF, -, hρa, -⟩ | hG
  · rcases hF with ⟨-, -, h37, -⟩ | ⟨hn3, he4, -, -, hσ4⟩
    · exact absurd h37 (by decide)
    · exact ⟨hn3, he4, K, inferInstance, inferInstance, φ, ρ, c, σ, hK, hinj, hρW, hσ4, hρa⟩
  · exfalso
    obtain ⟨-, -, -, -, -, -, hG59⟩ := hG
    rcases hG59 with ⟨-, -, h35, -⟩ | ⟨-, -, -, h12, -⟩
    · exact absurd h35 (by decide)
    · exact absurd h12 (by decide)

theorem false_of_psl_five_two (h : Hyp N α J) (hm : Blueprint.LieModel N .PSL 5 2 1) : False := by
  have hcard : Nat.card N = 9999360 := by
    rw [(Timmesfeld.card_statedClassicalModel_two
      (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm)).1 rfl]
    decide
  have hWalt := isEmpty_alt_of_card hcard
    (factorial_ne_of_lt (k := 10) (by decide) (by decide))
  obtain ⟨h53, -⟩ := h.selector hm (by norm_num) hWalt
  exact absurd h53 (by decide)

theorem field_form (h : Hyp N α J) (hm : Blueprint.LieModel N .PSL 3 2 4) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : N ≃* projectiveSL 3 K)
      (ρ : G →* MulAut (projectiveSL 3 K)) (c : GL (Fin 3) K) (σ : K ≃+* K),
      Nat.card K = 16 ∧ Function.Injective ρ ∧ (∀ w : N, ρ w = MulAut.conj (φ w)) ∧
        (∀ t, σ t = t ^ 4) ∧ ρ α = conjAut 3 K c * fieldAut 3 K σ * (conjAut 3 K c)⁻¹ := by
  have hcard : Nat.card N = 1425715200 := by
    rw [(Timmesfeld.card_statedClassicalModel_two
      (RestrictedStd.statedClassicalModel_of_lieModel_PSL hm)).1 rfl]
    decide
  have hWalt := isEmpty_alt_of_card hcard
    (factorial_ne_of_lt (k := 12) (by decide) (by decide))
  obtain ⟨-, -, K, hF, hfin, φ, ρ, c, σ, hK, hrest⟩ := h.selector hm (by norm_num) hWalt
  exact ⟨K, hF, hfin, φ, ρ, c, σ, by rw [hK]; norm_num, hrest⟩

end Hyp

end CFSG.ComponentClassification.GSThmB.Soc
