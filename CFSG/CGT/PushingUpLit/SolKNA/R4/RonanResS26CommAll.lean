module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (odd_outerEquivSemilinearQuotient)

theorem outer_comm_of_smallL2 {F : Type} [Group F] (h : CFSG.ClassicalInvolution.Q3.TA3.SmallL2 F)
    (a b : Outer F) : a * b = b * a := by
  obtain ⟨p, f, K, _, _, hp, hpodd, hf, h3, hK, ⟨e⟩⟩ := soc_l2_data h
  have hK' : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hpodd, by omega, hK⟩
  have h3' : 3 < Nat.card K := by rw [hK]; exact h3
  have hPSL : ∀ c d : Outer (PSL2 K), c * d = d * c := by
    intro c d
    apply (odd_outerEquivSemilinearQuotient K hK' h3').symm.injective
    rw [map_mul, map_mul]
    exact soc_l2_semilinearQuotient_comm K hK' _ _
  apply (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective
  rw [map_mul, map_mul]
  exact hPSL _ _

theorem l2_comm_all {A : Type} [Group A] (T : Subgroup A) [T.Normal]
    (hT : CFSG.ClassicalInvolution.Q3.TA3.SmallL2 ↥T)
    (hC : Subgroup.centralizer (T : Set A) = ⊥) (x y : A) : ⁅x, y⁆ ∈ T := by
  let Ψ : A →* Outer ↥T :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥T)).comp
      (MulAut.conjNormal : A →* MulAut ↥T)
  have hker : ∀ g : A, Ψ g = 1 → g ∈ T := by
    intro g hg
    have h2 : (MulAut.conjNormal g : MulAut ↥T) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥T :=
      (QuotientGroup.eq_one_iff _).mp hg
    obtain ⟨f, hf⟩ := h2
    have hg' : g⁻¹ * (f : A) ∈ Subgroup.centralizer (T : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have key := congrArg (fun α : MulAut ↥T => ((α ⟨w, hw⟩ : ↥T) : A)) hf
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        InvMemClass.coe_inv] at key
      calc w * (g⁻¹ * (f : A)) = g⁻¹ * (g * w * g⁻¹) * f := by group
        _ = g⁻¹ * ((f : A) * w * (f : A)⁻¹) * f := by rw [key]
        _ = g⁻¹ * f * w := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hg'
    rw [hg']
    exact f.2
  apply hker
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (outer_comm_of_smallL2 hT _ _)

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
