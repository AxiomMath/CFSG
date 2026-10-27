module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.RankThree.PartOne.KE.SuzukiFinal

public section

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

theorem outerFixedOrderBoundAt_twistedB2 : OuterFixedOrderBoundAt .twistedB2 := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 _ _ α hαp hαin
  left
  have hSz : SuzukiModel K ℓ f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
  obtain ⟨-, a, ha, F, hF, hFin, hfa, hFcard, ⟨e⟩⟩ := hSz
  have hℓ : ℓ = 2 := hadm.2.2.2.1
  subst hℓ
  have hK : Nat.card F = 2 ^ (2 * a + 1) := hfa ▸ hFcard
  set β := MulAut.congr e α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ inner (suzukiGroup a F) :=
    fun hin => hαin ((congr_mem_inner_iff e α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (inner (suzukiGroup a F)).one_mem)
  have : Fact p.Prime := ⟨hp⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨σ, h, b, k, hk, hkfin, -, hbp, hkcard, hconj, ⟨eH⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha F hK p hp hp2 β hβord hβout
  rw [← card_fixedSubgroup_congr e α]
  set γ : MulAut (suzukiGroup a F) := szFieldAut a F σ with hγ
  have hcard1 : Nat.card (fixedSubgroup β) = Nat.card (fixedSubgroup γ) :=
    card_fixedSubgroup_eq_of_intertwine (MulAut.conj h) β γ fun x => by
      rw [← hconj]
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hcard2 : Nat.card (fixedSubgroup γ) = Nat.card (suzukiGroup b k) := by
    rw [show fixedSubgroup γ = (szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _) from rfl]
    exact Nat.card_congr eH.toEquiv
  refine ⟨2 * b + 1, ?_, ?_⟩
  · rw [hfa, ← hbp, mul_comm]
  · rw [hcard1, hcard2, suzuki_order hkcard]
    simp only [lieOrderNumerator]
    exact dvd_of_eq (by ring)

end CFSG.HardMathSupport.Lang.Coordinator
