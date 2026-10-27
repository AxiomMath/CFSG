module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcFieldCore

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E27

open CFSG.RankThree.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank SteinbergBT
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.E6Descent
open CFSG.HardMathSupport.Malle.E27Lie (dvd_card_fixedSubgroup_of_conj)

theorem twentySeven_dvd_fixedSubgroup_adjointE_of_not_innerDiag
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h27 : ∀ (F : Type) [Field F] [Finite F], 27 ∣ Nat.card (adjointGroup τ F))
    {ℓ f p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1)
    (_hα : α ∉ inner (adjointGroup τ K))
    (hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      α ≠ MulAut.conj g * rootDiagAut τ K a) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  obtain ⟨-, T, r, j, ψ, -, -, -, -, -, hαβ, hψ⟩ :=
    exists_conj_entrywise_of_not_innerDiag τ hτ hf K hK hp hp2 α hαp hnd
  rw [fixedSubgroup_pow_eq hαβ]
  exact dvd_card_fixedSubgroup_of_conj h27 (α ^ r) ψ T hψ

theorem ne_conj_mul_rootDiagAut_of_not_dvd (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hq : ¬ p ∣ Nat.card K - 1)
    (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1) (hα : α ∉ inner (adjointGroup τ K)) :
    ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ), α ≠ MulAut.conj g * rootDiagAut τ K a := by
  intro g a hαdiag
  exact hq (prime_dvd_of_diag_noninner τ hτ K hp g a α hαdiag hαp hα).2

theorem twentySeven_dvd_card_adjointGroup_E6 (F : Type) [Field F] [Finite F] :
    27 ∣ Nat.card (adjointGroup Tag.E6 F) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6]
  have hnum : 81 ∣ CFSG.Open.ordE6 (Nat.card F) * Nat.gcd 3 (Nat.card F - 1) := by
    rw [CFSG.HardMathSupport.Lang.Coordinator.ordE6_mul_gcd]
    exact CFSG.HardMathSupport.Malle.E27Lie.eightyOne_dvd_numE6 _ Nat.card_pos
  have h81 : 81 ∣ CFSG.Open.ordE6 (Nat.card F) * 3 :=
    hnum.trans (mul_dvd_mul_left _ (Nat.gcd_dvd_left 3 _))
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 3)
    (by rwa [show (27 : ℕ) * 3 = 81 by norm_num])

theorem twentySeven_dvd_fixedSubgroup_E6_of_not_innerDiag {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup Tag.E6 K))
    (hα3 : α ^ 3 = 1) (hα : α ∉ inner (adjointGroup Tag.E6 K))
    (hnd : ∀ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
      α ≠ MulAut.conj g * rootDiagAut Tag.E6 K a) :
    27 ∣ Nat.card (fixedSubgroup α) :=
  twentySeven_dvd_fixedSubgroup_adjointE_of_not_innerDiag .E6 (Or.inl rfl)
    twentySeven_dvd_card_adjointGroup_E6 hf K hK Nat.prime_three (by norm_num) α hα3 hα hnd

theorem twentySeven_dvd_fixedSubgroup_E6_of_not_dvd {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (hq : ¬ 3 ∣ ℓ ^ f - 1)
    (α : MulAut (adjointGroup Tag.E6 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (adjointGroup Tag.E6 K)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  have : Finite K := Nat.finite_of_card_ne_zero
    (by rw [hK]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  exact twentySeven_dvd_fixedSubgroup_E6_of_not_innerDiag hf K hK α hα3 hα
    (ne_conj_mul_rootDiagAut_of_not_dvd .E6 (Or.inl rfl) K Nat.prime_three (by rwa [hK]) α hα3 hα)

@[expose] def E6InnerDiagLowerBound : Prop :=
  ∀ {ℓ f : ℕ} [Fact ℓ.Prime], 1 ≤ f → ∀ (K : Type) [Field K], Nat.card K = ℓ ^ f →
    3 ∣ ℓ ^ f - 1 → ∀ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
      (MulAut.conj g * rootDiagAut Tag.E6 K a) ^ 3 = 1 →
      MulAut.conj g * rootDiagAut Tag.E6 K a ∉ inner (adjointGroup Tag.E6 K) →
        27 ∣ Nat.card (fixedSubgroup (MulAut.conj g * rootDiagAut Tag.E6 K a))

theorem twentySeven_dvd_fixedSubgroup_E6_of_innerDiag (hdiag : E6InnerDiagLowerBound)
    {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.E6 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (adjointGroup Tag.E6 K)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  by_cases hnd : ∀ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
      α ≠ MulAut.conj g * rootDiagAut Tag.E6 K a
  · exact twentySeven_dvd_fixedSubgroup_E6_of_not_innerDiag hf K hK α hα3 hα hnd
  · push Not at hnd
    obtain ⟨g, a, rfl⟩ := hnd
    by_cases hq : 3 ∣ ℓ ^ f - 1
    · exact hdiag hf K hK hq g a hα3 hα
    · exact twentySeven_dvd_fixedSubgroup_E6_of_not_dvd hf K hK hq _ hα3 hα

end CFSG.HardMathSupport.Lang.E27
