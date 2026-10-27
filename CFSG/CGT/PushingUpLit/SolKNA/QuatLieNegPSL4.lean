module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSL4Comp
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSL4Twin
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

namespace PSL4Asm

theorem exists_mulEquiv_psl4 {X : Type} [Group X] (h : CFSG.Blueprint.LieModel X .PSL 4 3 1) :
    Nonempty (X ≃* SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) := by
  classical
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have : Fintype K := Fintype.ofFinite K
  have hK3 : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK, pow_one]
  have φ : K ≃+* ZMod 3 := (ZMod.ringEquivOfPrime K Nat.prime_three hK3).symm
  let E := CFSG.ClassicalModels.specialLinearFieldEquiv φ (Fin 4)
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 4 K)).trans
    (QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)))⟩

theorem twin_or_component (s : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3))
    (hs : orderOf s = 2) : TwinAt s ∨ ComponentAt s := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  have hss : (QuotientGroup.mk g : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) *
      QuotientGroup.mk g = 1 := by
    have := pow_orderOf_eq_one
      (QuotientGroup.mk g : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3))
    rwa [hs, pow_two] at this
  have hg2c : g * g ∈ Subgroup.center SL(4, ZMod 3) := by
    have h1 : QuotientGroup.mk' (Subgroup.center SL(4, ZMod 3)) (g * g) = 1 := by
      rw [map_mul]
      exact hss
    exact (QuotientGroup.eq_one_iff (g * g)).mp h1
  have hgc : g ∉ Subgroup.center SL(4, ZMod 3) := by
    intro h
    have h1 : (QuotientGroup.mk g : SL(4, ZMod 3) ⧸ Subgroup.center SL(4, ZMod 3)) = 1 :=
      (QuotientGroup.eq_one_iff g).mpr h
    rw [h1, orderOf_one] at hs
    exact absurd hs (by norm_num)
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg2c
  have hmat : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * g = Matrix.scalar (Fin 4) r := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← hrz]
  rw [Fintype.card_fin] at hr
  rcases (by decide : ∀ r : ZMod 3, r ^ 4 = 1 → r = 1 ∨ r = -1) r hr with rfl | rfl
  · exact Or.inl (twinAt_psl4_of_sq_eq_one g (by rw [hmat, map_one]) hgc)
  · exact Or.inr (componentAt_psl4_of_sq_eq_neg_one g (by rw [hmat, map_neg, map_one]; rfl))

end PSL4Asm

theorem negModel_PSL4 : NegModel .PSL 4 := by
  intro X _ _ hX K hK R
  obtain ⟨e⟩ := PSL4Asm.exists_mulEquiv_psl4 hX
  exact not_quaternion_of_equiv e (fun s hs => PSL4Asm.twin_or_component s hs) hK R

end CFSG.CGT.PushingUpLit.SolKNA
