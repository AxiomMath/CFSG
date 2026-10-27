module

public import CFSG.Sporadic.FischerOddCore.FischerOuterFi24
public import CFSG.Sporadic.SmallOddCore.Assembly

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Fi24PrimeAux

open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Sporadic.Fi24 (R J JR jR)


theorem card_outer_le_two {G : Type*} [Group G] [Finite G] (hcen : Subgroup.center G = ⊥)
    (hc : Nat.card (MulAut G) = 2 * Nat.card G) : Nat.card (Outer G) ≤ 2 := by
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun x => by
      have := congrArg (fun α : MulAut G => α x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group
    rw [hcen, Subgroup.mem_bot] at hg'
    exact hg'
  have hinn : Nat.card (OuterAutomorphisms.inner G) = Nat.card G := by
    rw [OuterAutomorphisms.inner, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj,
      Subgroup.card_top]
  have h1 := (OuterAutomorphisms.inner G).card_mul_index
  rw [hinn, hc, Subgroup.index_eq_card] at h1
  have h2 : Nat.card G * Nat.card (Outer G) = Nat.card G * 2 := by rw [h1]; ring
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h2).le

section Model


theorem fi24_autModel : AutModel (JR : Subgroup ↥R) (⊤ : Subgroup ↥R) where
  le := le_top
  conj_mem := fun x _ p hp => CFSG.Sporadic.Fi24.normal_JR.conj_mem p hp x
  surj := fun α => by
    obtain ⟨r, hr⟩ := CFSG.Sporadic.FischerOddCore.conjJ_surjective
      (MulAut.congr (Subgroup.subgroupOfEquivOfLe CFSG.Sporadic.Fi24.J_le_R) α)
    refine ⟨r, Subgroup.mem_top r, fun p => ?_⟩
    have h1 := CFSG.Sporadic.Fi24.jR_conjJ r
      (Subgroup.subgroupOfEquivOfLe CFSG.Sporadic.Fi24.J_le_R p)
    rw [hr] at h1
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    exact h1
  inj := fun x _ hx => by
    apply CFSG.Sporadic.Fi24.conjJ_injective
    rw [map_one]
    refine MulEquiv.ext fun g => CFSG.Sporadic.Fi24.jR_injective ?_
    rw [CFSG.Sporadic.Fi24.jR_conjJ, MulAut.one_apply]
    calc x * jR g * x⁻¹ = jR g * x * x⁻¹ := by
          rw [hx (jR g) (CFSG.Sporadic.Fi24.jR_mem_JR g)]
      _ = jR g := by group

theorem card_mulAut_JR : Nat.card (MulAut ↥JR) = 2 * Nat.card ↥JR := by
  have e : MulAut ↥JR ≃ ↥R :=
    ((MulAut.congr (Subgroup.subgroupOfEquivOfLe CFSG.Sporadic.Fi24.J_le_R)).toEquiv.trans
      (Equiv.ofBijective CFSG.Sporadic.Fi24.conjJ
        ⟨CFSG.Sporadic.Fi24.conjJ_injective,
          CFSG.Sporadic.FischerOddCore.conjJ_surjective⟩).symm)
  have h := (JR : Subgroup ↥R).card_mul_index
  rw [CFSG.Sporadic.Fi24.index_JR] at h
  rw [Nat.card_congr e, ← h, mul_comm]

theorem card_mulAut_of_mulEquiv {S : Type*} [Group S] (θ : S ≃* ↥JR) :
    Nat.card (MulAut S) = 2 * Nat.card S := by
  rw [Nat.card_congr (@MulAut.congr S _ ↥JR (Subgroup.toGroup JR) θ).toEquiv,
    Nat.card_congr θ.toEquiv]
  exact card_mulAut_JR

end Model

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Fi24PrimeAux
