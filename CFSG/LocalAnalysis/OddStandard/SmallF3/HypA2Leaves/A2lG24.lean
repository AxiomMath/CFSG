module

public import CFSG.LieType.Steinberg.CentralExt.G2FourRootLifts
public import CFSG.LieType.Steinberg.CentralExt.G2FourMultiplier
public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.G2FieldFour CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.Steinberg.CentralExt.G2Four

section Model


theorem a2l_g2_model {Y : Type} [Group Y] (hL : LieModel (Y ⧸ center Y) .G2 0 2 2) :
    ∃ (F : Type) (_ : Field F), Nat.card F = 4 ∧
      Nonempty (Y ⧸ center Y ≃* adjointGroup .G2 F) := by
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hL.chevalleyExceptionalModel (by decide)
  refine ⟨F, hF, by simpa using hcard, ⟨e.trans ?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
    QuotientGroup.quotientBot

end Model

section Rank


theorem a2l_card_center_g2 {K F : Type} [Group K] [Finite K] [Group.IsPerfect K] [Field F]
    (hc : center K ≠ ⊥) (hF : Nat.card F = 4) (e : K ⧸ center K ≃* adjointGroup .G2 F) :
    Nat.card ↥(center K) = 2 := by
  let φ : K →* adjointGroup .G2 F := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = center K := by
    ext k
    rw [MonoidHom.mem_ker]
    exact centralQuotient_eq_one_iff e k
  have hle : Nat.card ↥(center K) ≤ 2 := by
    have := g2_four_card_ker_le_two hF φ hφ hker.le
    rwa [hker] at this
  have hpos : 0 < Nat.card ↥(center K) := Nat.card_pos
  have hne : Nat.card ↥(center K) ≠ 1 := fun h => hc (Subgroup.card_eq_one.1 h)
  omega

theorem a2l_three_le_pRank_of_g2 {K F : Type} [Group K] [Finite K] [Field F]
    (hZ : Nat.card ↥(center K) = 2) (hF : Nat.card F = 4)
    (e : K ⧸ center K ≃* adjointGroup .G2 F) : 3 ≤ CFSG.pRank 2 K := by
  classical
  let φ : K →* adjointGroup .G2 F := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = center K := by
    ext k
    rw [MonoidHom.mem_ker]
    exact centralQuotient_eq_one_iff e k
  let ψ : Multiplicative F →* adjointGroup .G2 F :=
    { toFun := fun s => rootX rootC (Multiplicative.toAdd s)
      map_one' := rootX_zero rootC
      map_mul' := fun s t => rootX_add rootC _ _ }
  have hψ : Function.Injective ψ := fun s t h =>
    Multiplicative.toAdd.injective (rootX_injective rootC h)
  have hEcard : Nat.card ψ.range = 4 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F), hF]
  have hcard : Nat.card ((ψ.range).comap φ) = 2 ^ 3 := by
    rw [GH74.GLS.IVK.Lifted.card_comap_of_surjective_two hφ, hEcard, hker, hZ]
    norm_num
  have hsq : ∀ x ∈ (ψ.range).comap φ, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 (Subgroup.mem_comap.1 hx)
    by_cases h0 : Multiplicative.toAdd s = 0
    · have h1 : φ x = 1 := by
        rw [← hs]
        change rootX rootC (Multiplicative.toAdd s) = 1
        rw [h0, rootX_zero]
      have hxc : x ∈ center K := hker ▸ MonoidHom.mem_ker.2 h1
      have hp := pow_card_eq_one' (G := ↥(center K)) (x := ⟨x, hxc⟩)
      rw [hZ] at hp
      exact congrArg Subtype.val hp
    · have hx2 : orderOf x = 2 := by
        refine orderOf_eq_two_of_isConj_long_of_quotient hZ hF e (γ := rootC)
          (s := Multiplicative.toAdd s) (by simp [longRoots]) h0 (x := x) ?_
        have hxs : e (x : K ⧸ center K) = rootX rootC (Multiplicative.toAdd s) := hs.symm
        rw [hxs]
      rw [← hx2]
      exact pow_orderOf_eq_one x
  exact GH74.GLS.IVK.Lifted.le_pRank_two_of_elementaryAbelian _
    (GH74.GLS.IVK.Lifted.isElementaryAbelian_two_of_sq_eq_one hsq) hcard

theorem a2l_three_le_pRank_g2 {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (hc : center Y ≠ ⊥) (hL : LieModel (Y ⧸ center Y) .G2 0 2 2) : 3 ≤ CFSG.pRank 2 Y := by
  haveI : Group.IsPerfect Y := hY.1
  obtain ⟨F, _, hF, ⟨e⟩⟩ := a2l_g2_model hL
  exact a2l_three_le_pRank_of_g2 (a2l_card_center_g2 hc hF e) hF e

end Rank

end CFSG.OddStandard.SmallF3.HypA2Leaves
