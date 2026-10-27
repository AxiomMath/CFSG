module

public import CFSG.GF2Type.Smith1979.IdxFourBridge
public import CFSG.GF2Type.Smith1979.IdxFourTransport
public import CFSG.GF2Type.Smith1979.IdxFourHMain
public import CFSG.GF2Type.Smith1979.IdxFourModelFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
open CFSG.GF2Type.Smith1979.GammaU

@[expose] def ModelInput : Prop :=
  Nat.card M0 = 39191040 ∧ ∃ (K2 L : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (x0 : V12 ≃ₗ[ZMod 2] V12)
    (a0 : V12) (Vt : Submodule (ZMod 2) V12), ModelFacts M0 K2 L x0 a0 Vt

theorem modelInput_holds :
    ModelInput :=
  ⟨card_M0, _, _, _, _, _, modelFacts⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_ne_mul (S : Setting G) (hw : S.width ≠ 0) : ∃ a b : G, a * b ≠ b * a := by
  by_contra! hall
  have hpos : 0 < finrank (ZMod 2) S.Qt := by rw [S.finrank_Qt_eq_two_mul_width]; omega
  obtain ⟨v, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  refine hv0 (S.q_nondegenerate.1 v fun w => ?_)
  obtain ⟨x, hx, rfl⟩ := S.exists_cl v
  obtain ⟨y, hy, rfl⟩ := S.exists_cl w
  exact (S.polar_cl_eq_zero_iff hx hy).mpr (hall x y)

theorem index_ne_four (hTI : WeaklyClosedTITransitive.{0}) (hMI : ModelInput) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 6) (hirr : ¬ S.IsReducible) (hnoAll : S11.NoA2All S)
    {g : G} (H : Hyp4 S g) (C : Cons311 S g) (E Ob : Subgroup S.Mbar) (hEn : E.Normal)
    (hOb : Ob = CFSG.pCore 3 S.Mbar) (hO : Nat.card Ob = 3)
    (hZ : (center E).map E.subtype = Ob)
    (hX : CFSG.Open.StatedClassicalModel (E ⧸ center E) .PSU 4 3 1) : E.index ≠ 4 := by
  intro hidx
  obtain ⟨hM0card, K2, L, x0, a0, Vt, hF⟩ := hMI
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOb1 : Ob ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hO
    omega
  obtain ⟨θ', hθ'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hOb1
  have hθ1 : (θ' : S.Mbar) ≠ 1 := fun h => hθ'1 (Subtype.ext h)
  have hord : orderOf (θ' : S.Mbar) = 3 := by
    rw [Subgroup.orderOf_coe]
    have h1 : orderOf θ' ∣ 3 := hO ▸ orderOf_dvd_natCard θ'
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hθ'1
    · exact h
  have hθ3 : (θ' : S.Mbar) ^ 3 = 1 := hord ▸ pow_orderOf_eq_one _
  have hObz : Ob = zpowers (θ' : S.Mbar) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr θ'.2) ?_
    rw [hO, Nat.card_zpowers, hord]
  have hZ' : (center E).map E.subtype = zpowers (θ' : S.Mbar) := hZ.trans hObz
  have hZn : (zpowers (θ' : S.Mbar)).Normal := by
    rw [← hObz, hOb]
    exact CFSG.pCore_normal
  obtain ⟨ψ, hq, hθψ, hMψ⟩ :=
    exists_isometry_map_eq_M0 S hw E hEn hidx hθ3 hθ1 hZ' hZn hX hM0card
  have hfpf := fixedPointFree_of_layer S hw E hθ3 hθ1 hZ' hX
  have hθO3 : (((θ' : S.Mbar) : S.O)) ^ 3 = 1 := by
    simpa using congrArg (fun x : S.Mbar => (x : S.O)) hθ3
  obtain ⟨K, xb, hIF⟩ := exists_idxFourFacts hw H C hF hq hθψ hMψ (θ' : S.Mbar).2 hθO3 hfpf
  exact false_of_idx4 (exists_mul_ne_mul S (by omega)) hTI S hw hirr hnoAll H.conj_mem
    H.conj_ne hIF

end CFSG.GF2Type.Smith1979.IdxFour
