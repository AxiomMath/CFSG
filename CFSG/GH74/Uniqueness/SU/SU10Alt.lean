module

public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2
public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.Bender

theorem center_eq_bot_of_isBender {X : Type} [Group X] [Finite X]
    (h : CFSG.BenderSuzuki.IsBenderGroup X) : center X = ⊥ := by
  obtain ⟨n, i, e, hB⟩ := isBenderGroup_iff_exists_benderType.mp h
  have hs : IsSimpleGroup X := hB.isSimple
  have hnc : ∃ a b : X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hB.isSimpleBenderGroup.not_commutative hcon
  exact CFSG.TwoRankLowerBound.Helpers.center_eq_bot_of_nonabelian_simple X hnc

theorem center_ne_bot_of_isTwoAlt {X : Type} [Group X] {n : ℕ} (h : K.IsTwoAlt X n) :
    center X ≠ ⊥ := by
  intro hbot
  obtain ⟨-, -, hc, -⟩ := h
  rw [hbot, Subgroup.card_bot] at hc
  omega

theorem center_ne_bot_of_isTwoSz8 {X : Type} [Group X] (h : K.IsTwoSz8 X) : center X ≠ ⊥ := by
  intro hbot
  obtain ⟨-, -, hc, -⟩ := h
  rw [hbot, Subgroup.card_bot] at hc
  omega

theorem center_ne_bot_of_isSL25 {X : Type} [Group X] (h : K.IsSL25 X) : center X ≠ ⊥ := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  intro hbot
  let φ : Matrix.SpecialLinearGroup (Fin 2) F ≃* X :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).trans e.symm
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    decide
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hmem := CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F
  have hne := CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one F h2
  have hc : φ (CFSG.Semidihedral.OddFieldSL2.minusIdentity F) ∈ center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hmem y']
  rw [hbot, Subgroup.mem_bot] at hc
  exact hne (φ.injective (by rw [hc, map_one]))

theorem isTwoAlt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : K.IsTwoAlt X n) : K.IsTwoAlt Y n := by
  obtain ⟨hq, hfin, hc, ⟨f⟩⟩ := h
  have hcen : (center X).map e.toMonoidHom = center Y := Subgroup.map_center_eq e
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, Finite.of_equiv X e.toEquiv, ?_, ?_⟩
  · rw [← hcen, Subgroup.card_map_of_injective e.injective]
    exact hc
  · exact ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩

end CFSG.GH74.Uniqueness.SU.SU10
