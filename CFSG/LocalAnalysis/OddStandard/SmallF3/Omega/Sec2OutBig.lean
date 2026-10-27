module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOne
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutSeven
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrBlockType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem outerData_of_big (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    (hσ : quadSign Q = 1) {x : OGroup Q} (hx : x * x = 1) (h5 : 5 ≤ invDim x)
    (h7 : invDim x ≤ 7) : OuterData ↥(omegaProj hQ) (projAut hQ x) := by
  have hQU := nondegenerate_restrict_commSp hQ hx
  have hrU : Module.finrank (ZMod 3) ↥(commSp x) = invDim x := rfl
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) x
  have hq : CFSG.IsQuasisimple (omegaGroup hQU) :=
    isQuasisimple_omegaGroup_of_five_le_seven hQU (by omega) (by omega)
  obtain ⟨u, huu, hut⟩ := (exists_involution_of_type hQU (2 * invDim x - 8)
    ((-1) ^ (invDim x - 4))).mpr ⟨by omega, fun h => by omega, fun h => by omega⟩
  have hud : invDim u = 2 * invDim x - 8 := congrArg Prod.fst hut
  have hus : invSign u = (-1) ^ (invDim x - 4) := congrArg Prod.snd hut
  have huΩ : u ∈ omegaGroup hQU := by
    refine (involution_mem_omegaGroup_iff hQU huu).mpr ⟨?_, ?_⟩
    · rw [hud]
      exact ⟨invDim x - 4, by omega⟩
    · rw [hus, hud]
      congr 1
      omega
  have hu1 : u ≠ 1 := by
    intro h
    have h0 : invDim u = 0 := by rw [h]; exact congrArg Prod.fst invType_one
    omega
  have hty : invType (blockInr hx u * x) = invType (piOrth Q * x) := by
    have hxe : blockInr hx u * x = blockInr hx (piOrth (Q.restrict (commSp x)) * u) := by
      rw [map_mul, blockInr_piOrth]
      exact Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ hx u)
    rw [hxe, invType_blockInr hQ hx (piOrth_mul_mul_self huu), invType_piOrth_mul hQU huu,
      invType_piOrth_mul hQ hx, hud, hus, hrU, hdim, hσ]
    refine Prod.ext (show invDim x - (2 * invDim x - 8) = 8 - invDim x by omega) ?_
    change quadSign (Q.restrict (commSp x)) * (-1) ^ (invDim x - 4) *
      (-1) ^ ((2 * invDim x - 8) * (invDim x - (2 * invDim x - 8))) =
      1 * quadSign (Q.restrict (commSp x)) * (-1) ^ (invDim x * (8 - invDim x))
    rcases Int.units_eq_one_or (quadSign (Q.restrict (commSp x))) with he | he <;> rw [he] <;>
      rcases (by omega : invDim x = 5 ∨ invDim x = 6 ∨ invDim x = 7) with hr | hr | hr <;>
      rw [hr] <;> decide
  exact outerData_of_block hQ (by omega) hx (by omega) (by omega) hq (u := ⟨u, huΩ⟩) huu
    (fun h => hu1 (congrArg Subtype.val h)) (Or.inr hty)

end CFSG.OddStandard.SmallF3.Omega
