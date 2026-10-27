module

public import CFSG.FeitThompson.Representations.CentralCharacterHomomorphism
public import Mathlib.Analysis.Complex.Polynomial.Basic
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped ComplexConjugate

namespace CFSG.FeitThompson

namespace Representation

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

theorem isConj_inv_inv {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, by group⟩

theorem card_conjClassFinset_eq_card_carrier [Finite G] {x : G} {K : ConjClasses G}
    (hx : ConjClasses.mk x = K) : (conjClassFinset x).card = Nat.card K.carrier := by
  rw [card_conjClassFinset, hx]

theorem sum_character_mul_character_inv [Fintype G] (ρ : _root_.Representation ℂ G V)
    [ρ.IsIrreducible] :
    ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : ℂ) := by
  classical
  have h1 : cfInner ρ.character ρ.character = 1 := by
    rw [cfInner_character_character ρ ρ]
    exact if_pos ⟨_root_.Representation.Equiv.refl ρ⟩
  rw [cfInner_def] at h1
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  field_simp at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [character_inv ρ (isOfFinOrder_of_finite g)]

theorem card_eq_sum_card_mul_character_mul_character_inv [Finite G] [Fintype (ConjClasses G)]
    (ρ : _root_.Representation ℂ G V) [ρ.IsIrreducible] (x : ConjClasses G → G)
    (hx : ∀ K, ConjClasses.mk (x K) = K) :
    (Nat.card G : ℂ) = ∑ K : ConjClasses G,
      (Nat.card K.carrier : ℂ) * (ρ.character (x K) * ρ.character (x K)⁻¹) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hfib : ∀ K : ConjClasses G,
      Finset.univ.filter (fun g : G => ConjClasses.mk g = K) = conjClassFinset (x K) := by
    intro K
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_conjClassFinset]
    rw [← ConjClasses.mk_eq_mk_iff_isConj, hx K, eq_comm]
  rw [← sum_character_mul_character_inv ρ,
    ← Finset.sum_fiberwise Finset.univ ConjClasses.mk
      (fun g => ρ.character g * ρ.character g⁻¹)]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [hfib K, Finset.sum_congr rfl
    (g := fun _ => ρ.character (x K) * ρ.character (x K)⁻¹) (fun g hg => ?_),
    Finset.sum_const, nsmul_eq_mul, card_conjClassFinset_eq_card_carrier (hx K)]
  have h := mem_conjClassFinset.1 hg
  rw [char_eq_of_isConj ρ h, char_eq_of_isConj ρ (isConj_inv_inv h)]

theorem card_div_character_one_eq_sum [Finite G] [Fintype (ConjClasses G)]
    (ρ : _root_.Representation ℂ G V) [ρ.IsIrreducible] (x : ConjClasses G → G)
    (hx : ∀ K, ConjClasses.mk (x K) = K) :
    (Nat.card G : ℂ) / ρ.character 1 =
      ∑ K : ConjClasses G,
        (Nat.card K.carrier : ℂ) * ρ.character (x K) / ρ.character 1 * ρ.character (x K)⁻¹ := by
  rw [card_eq_sum_card_mul_character_mul_character_inv ρ x hx, Finset.sum_div]
  exact Finset.sum_congr rfl fun K _ => by ring

theorem card_div_character_one_eq_sum_centralCharacter [Finite G] [Fintype (ConjClasses G)]
    (ρ : _root_.Representation ℂ G V) [ρ.IsIrreducible] (x : ConjClasses G → G)
    (hx : ∀ K, ConjClasses.mk (x K) = K) :
    (Nat.card G : ℂ) / ρ.character 1 =
      ∑ K : ConjClasses G,
        centralCharacter ρ ⟨conjClassSum ℂ (x K), conjClassSum_mem_center ℂ (x K)⟩ *
          ρ.character (x K)⁻¹ := by
  rw [card_div_character_one_eq_sum ρ x hx]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [centralCharacter_conjClassSum ρ (x K), card_conjClassFinset_eq_card_carrier (hx K)]

end Representation

theorem card_div_character_one_eq_sum_of_mem_Irr {G : Type*} [Group G] [Finite G]
    [Fintype (ConjClasses G)] {χ : G → ℂ} (hχ : χ ∈ Irr G) (x : ConjClasses G → G)
    (hx : ∀ K, ConjClasses.mk (x K) = K) :
    (Nat.card G : ℂ) / χ 1 =
      ∑ K : ConjClasses G, (Nat.card K.carrier : ℂ) * χ (x K) / χ 1 * χ (x K)⁻¹ := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hχ
  have := hW
  exact Representation.card_div_character_one_eq_sum W.ρ x hx

end CFSG.FeitThompson
