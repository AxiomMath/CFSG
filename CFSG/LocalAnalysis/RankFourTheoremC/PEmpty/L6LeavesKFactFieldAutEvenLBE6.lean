module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Adjoint
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Fixed27

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.RankThree.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank SteinbergBT
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.GroupTheory
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.E6Descent
  (card_fixedSubgroup_conj fixedSubgroup_pow_eq exists_conj_entrywise_of_outer_E)
open CFSG.HardMathSupport.Lang.Coordinator (card_fixedSubgroup_congr congr_mem_inner_iff)

theorem fixedLower_adjointE6
    {ℓ f f₀ p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (hf₀ : f = p * f₀) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (α : MulAut (adjointGroup Tag.E6 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.E6 K)) :
    CFSG.Open.ordE6 (ℓ ^ f₀) ∣ Nat.card (fixedSubgroup α) := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  have hdet : ¬ p ∣ Tag.E6.cartan.det.natAbs := by
    rw [det_cartan_E6]
    intro h
    have h3 : p ∣ 3 := h
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  obtain ⟨d, T, r, j, ψ, hd, -, hcard, hαβ, hψ⟩ :=
    exists_conj_entrywise_of_outer_E .E6 (Or.inl rfl) hf K hK hp (by omega) hdet α hαp hα
  rw [Nat.eq_of_mul_eq_mul_left hp.pos (hd.symm.trans hf₀)] at hcard
  rw [fixedSubgroup_pow_eq hαβ, ← card_fixedSubgroup_conj ψ (α ^ r), hψ]
  have h := CFSG.HardMathSupport.Malle.E27Lie.card_adjointGroup_dvd_card_fixedSubgroup
    (τ := Tag.E6) T
  rwa [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hcard] at h

theorem fixedLowerBoundAt_E6
    : FixedLowerBoundAt .E6 := by
  intro K _ _ n ℓ f f₀ p hadm hmodel _ hp hp5 _ _ hf α hαp hαin
  have : Fact ℓ.Prime := ⟨hadm.1⟩
  have hf1 : 1 ≤ f := hadm.2.1
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    let θ : K ≃* adjointGroup Tag.E6 F := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    have hβp : MulAut.congr θ α ^ p = 1 := by rw [← map_pow, hαp, map_one]
    have hβout : MulAut.congr θ α ∉ inner (adjointGroup Tag.E6 F) := fun hin =>
      hαin ((congr_mem_inner_iff θ α).mp hin)
    rw [← card_fixedSubgroup_congr θ α]
    have h := fixedLower_adjointE6 hf1 hf F hFcard hp hp5 _ hβp hβout
    have h1 : lieOrderDivisor .E6 0 (ℓ ^ f₀) = Nat.gcd 3 (ℓ ^ f₀ - 1) := rfl
    have h2 : lieOrderNumerator .E6 0 (ℓ ^ f₀) =
        CFSG.Open.ordE6 (ℓ ^ f₀) * Nat.gcd 3 (ℓ ^ f₀ - 1) :=
      (CFSG.SeitzReduction.E6Pilot.ordE6_mul_gcd _).symm
    rw [h1, h2, mul_comm (CFSG.Open.ordE6 (ℓ ^ f₀))]
    exact Nat.mul_dvd_mul_left _ h
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
