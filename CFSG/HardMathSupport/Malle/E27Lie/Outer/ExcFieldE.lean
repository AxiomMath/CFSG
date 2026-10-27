module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcFieldCore
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE7

public noncomputable section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.RankThree.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank SteinbergBT
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.E6Descent

theorem twentySeven_dvd_fixedSubgroup_adjointE
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (h27 : ∀ (F : Type) [Field F] [Finite F], 27 ∣ Nat.card (adjointGroup τ F))
    {ℓ f p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ¬ p ∣ τ.cartan.det.natAbs)
    (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup τ K)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  obtain ⟨-, T, r, j, ψ, -, -, -, hαβ, hψ⟩ :=
    exists_conj_entrywise_of_outer_E τ hτ hf K hK hp hp2 hdet α hαp hα
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  rw [fixedSubgroup_pow_eq hαβ]
  exact dvd_card_fixedSubgroup_of_conj h27 (α ^ r) ψ T hψ


section


theorem twentySeven_dvd_card_adjointGroup_E7 (F : Type) [Field F] [Finite F] :
    27 ∣ Nat.card (adjointGroup Tag.E7 F) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7]
  have h : 27 ∣ CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .E7 0 (Nat.card F) :=
    twentySeven_dvd_numE7 _ Nat.card_pos
  rw [← ordE7_mul_gcd] at h
  exact Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 _) (by norm_num)) h

theorem twentySeven_dvd_card_adjointGroup_E8 (F : Type) [Field F] [Finite F] :
    27 ∣ Nat.card (adjointGroup Tag.E8 F) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8]
  exact twentySeven_dvd_ordE8 _ Nat.card_pos

theorem twentySeven_dvd_fixedSubgroup_E7 {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup Tag.E7 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (adjointGroup Tag.E7 K)) : 27 ∣ Nat.card (fixedSubgroup α) := by
  refine twentySeven_dvd_fixedSubgroup_adjointE .E7 (Or.inr (Or.inl rfl))
    twentySeven_dvd_card_adjointGroup_E7 hf K hK Nat.prime_three (by norm_num) ?_ α hα3 hα
  rw [det_cartan_E7]
  decide

theorem twentySeven_dvd_fixedSubgroup_E8 {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup Tag.E8 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ inner (adjointGroup Tag.E8 K)) : 27 ∣ Nat.card (fixedSubgroup α) := by
  refine twentySeven_dvd_fixedSubgroup_adjointE .E8 (Or.inr (Or.inr rfl))
    twentySeven_dvd_card_adjointGroup_E8 hf K hK Nat.prime_three (by norm_num) ?_ α hα3 hα
  rw [det_cartan_E8]
  decide

end

end CFSG.HardMathSupport.Malle.E27Lie
