module

public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.Quasithin.Vol2.Ch10SecACoprime

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_centralizer_mul_card_commutator_of_coprime {W X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hWab : IsMulCommutative ↥W) (hWexp : ∀ w ∈ W, w ^ 2 = 1)
    (hX : IsPGroup p X) (hp2 : p ≠ 2) (hXW : X ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card ↥W = Nat.card ↥(W ⊓ Subgroup.centralizer (X : Set G)) *
        Nat.card ↥(⁅W, X⁆ : Subgroup G) ∧
      (W ⊓ Subgroup.centralizer (X : Set G)) ⊓ (⁅W, X⁆ : Subgroup G) = ⊥ := by
  classical
  have hW2 : IsPGroup 2 W := fun w => ⟨1, Subtype.ext (by simpa using hWexp w w.2)⟩
  have hXodd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [hk]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hJleW : (⁅W, X⁆ : Subgroup G) ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hXW
  have hJ2 : IsPGroup 2 (⁅W, X⁆ : Subgroup G) := hW2.to_le hJleW
  have hXnormJ : X ≤ Subgroup.normalizer ((⁅W, X⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right W X
  have hJnotp : ¬ p ∣ Nat.card ↥(⁅W, X⁆ : Subgroup G) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hJ2 Fact.out hp2
  have hsup : (W ⊓ Subgroup.centralizer (X : Set G)) ⊔ (⁅W, X⁆ : Subgroup G) = W :=
    CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
      (p := p) (X := W) (N := (⁅W, X⁆ : Subgroup G)) (R := X)
      hJleW hXW hXnormJ hX hJnotp le_rfl
  have hdisj : (W ⊓ Subgroup.centralizer (X : Set G)) ⊓ (⁅W, X⁆ : Subgroup G) = ⊥ := by
    letI : IsMulCommutative ↥W := hWab
    have h0 := CFSG.Quasithin.Vol2.Ch10.SecA.commutator_inf_centralizer_eq_bot
      (W := W) (D := X) hWexp hXodd hXW
    refine le_antisymm ?_ bot_le
    intro z hz
    have hzinf : z ∈ (⁅W, X⁆ : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) :=
      Subgroup.mem_inf.mpr ⟨hz.2, hz.1.2⟩
    rw [h0] at hzinf
    exact Subgroup.mem_bot.mp hzinf
  have hCJleW : (W ⊓ Subgroup.centralizer (X : Set G)) ≤ W := inf_le_left
  have hCJnorm : (W ⊓ Subgroup.centralizer (X : Set G)) ≤
      Subgroup.normalizer ((⁅W, X⁆ : Subgroup G) : Set G) := by
    intro z hz
    refine Subgroup.centralizer_le_normalizer ((⁅W, X⁆ : Subgroup G) : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (congrArg Subtype.val (hWab.is_comm.comm ⟨z, hz.1⟩ ⟨j, hJleW hj⟩)).symm
  have h1 : W ⊓ (W ⊓ Subgroup.centralizer (X : Set G)) =
      W ⊓ Subgroup.centralizer (X : Set G) := by
    rw [inf_comm]
    exact inf_of_le_left hCJleW
  have h2 : W ⊓ (⁅W, X⁆ : Subgroup G) = (⁅W, X⁆ : Subgroup G) := by
    rw [inf_comm]
    exact inf_of_le_left hJleW
  have hfac : CFSG.GroupTheory.FT63ChII.IsFactorized
      (W ⊓ Subgroup.centralizer (X : Set G)) (⁅W, X⁆ : Subgroup G) W := by
    unfold CFSG.GroupTheory.FT63ChII.IsFactorized
    have hmul : ((W ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) *
        ((⁅W, X⁆ : Subgroup G) : Set G) = (W : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right
        (W ⊓ Subgroup.centralizer (X : Set G)) (⁅W, X⁆ : Subgroup G) hCJnorm, hsup]
    rw [h1, h2]
    exact hmul.symm
  have hcards := CFSG.GroupTheory.FT63ChII.card_mul_card_inf_of_isFactorized
    (M := W ⊓ Subgroup.centralizer (X : Set G)) (N := (⁅W, X⁆ : Subgroup G)) (R := W) hfac
  have hcards' : Nat.card ↥W * Nat.card ↥((W ⊓ Subgroup.centralizer (X : Set G)) ⊓ (⁅W, X⁆ : Subgroup G)) =
      Nat.card ↥(W ⊓ Subgroup.centralizer (X : Set G)) * Nat.card ↥(⁅W, X⁆ : Subgroup G) := by
    simpa only [h1, h2] using hcards
  rw [hdisj, Subgroup.card_bot, mul_one] at hcards'
  exact ⟨hcards', hdisj⟩

theorem four_le_card_commutator_of_fixedPoints_eq_bot {W X : Subgroup G}
    (hW2 : IsPGroup 2 W) (hXW : X ≤ Subgroup.normalizer (W : Set G))
    (hJne : (⁅W, X⁆ : Subgroup G) ≠ ⊥)
    (hfix : (⁅W, X⁆ : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    4 ≤ Nat.card ↥(⁅W, X⁆ : Subgroup G) := by
  classical
  have hJleW : (⁅W, X⁆ : Subgroup G) ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hXW
  have hJ2 : IsPGroup 2 (⁅W, X⁆ : Subgroup G) := hW2.to_le hJleW
  have hJnot2 : Nat.card ↥(⁅W, X⁆ : Subgroup G) ≠ 2 := by
    intro hJcard
    obtain ⟨y, -, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(⁅W, X⁆ : Subgroup G))).1 hJcard
    have hJfix : ∀ x ∈ X, ∀ j ∈ (⁅W, X⁆ : Subgroup G), x * j * x⁻¹ = j := by
      intro x hxX j hjJ
      have hxN : x ∈ Subgroup.normalizer ((⁅W, X⁆ : Subgroup G) : Set G) :=
        Subgroup.normalizer_commutator_ge_right W X hxX
      have hconjJ : x * j * x⁻¹ ∈ (⁅W, X⁆ : Subgroup G) :=
        (Subgroup.mem_normalizer_iff.mp hxN j).mp hjJ
      by_cases hj1 : j = 1
      · simp [hj1]
      · have hconj1 : x * j * x⁻¹ ≠ 1 := by
          intro h
          apply hj1
          have := congrArg (fun t => x⁻¹ * t * x) h
          simpa [mul_assoc] using this
        have hconj1' : (⟨x * j * x⁻¹, hconjJ⟩ : ↥(⁅W, X⁆ : Subgroup G)) ≠ 1 := by
          intro h
          exact hconj1 (congrArg Subtype.val h)
        have hj1' : (⟨j, hjJ⟩ : ↥(⁅W, X⁆ : Subgroup G)) ≠ 1 := by
          intro h
          exact hj1 (congrArg Subtype.val h)
        have e1 : (⟨x * j * x⁻¹, hconjJ⟩ : ↥(⁅W, X⁆ : Subgroup G)) = y := hyuniq _ hconj1'
        have e2 : (⟨j, hjJ⟩ : ↥(⁅W, X⁆ : Subgroup G)) = y := hyuniq _ hj1'
        exact congrArg Subtype.val (e1.trans e2.symm)
    obtain ⟨j, hj1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hJne
    have hjC : (j : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxX
      calc x * (j : G) = (x * j * x⁻¹) * x := by group
        _ = (j : G) * x := by rw [hJfix x hxX (j : G) j.2]
    have hmem : (j : G) ∈ (⁅W, X⁆ : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) :=
      Subgroup.mem_inf.mpr ⟨j.2, hjC⟩
    rw [hfix] at hmem
    exact hj1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
  obtain ⟨kJ, hkJ⟩ := hJ2.exists_card_eq
  have hJ1 : Nat.card ↥(⁅W, X⁆ : Subgroup G) ≠ 1 := by
    intro h1
    exact hJne (Subgroup.card_eq_one.mp h1)
  have hkJne0 : kJ ≠ 0 := by
    intro h
    apply hJ1
    rw [hkJ, h, pow_zero]
  have hkJne1 : kJ ≠ 1 := by
    intro h
    apply hJnot2
    rw [hkJ, h, pow_one]
  have hkJge : 2 ≤ kJ := by omega
  rw [hkJ]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ kJ := Nat.pow_le_pow_right (by norm_num) hkJge

end CFSG.GroupTheory
