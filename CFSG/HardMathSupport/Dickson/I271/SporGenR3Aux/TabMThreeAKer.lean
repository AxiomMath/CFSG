module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeADefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeACover
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAFi24

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.YGroups CFSG.YGroups.Y443 CFSG.Open
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

theorem ker_coverHom_yMc
    (hG : Gmat = AutO) (h : (yMc hG).ker ≤ yJ.ker) :
    orderOf (zetaM hG) = 3 ∧ tGriess * zetaM hG * tGriess⁻¹ = (zetaM hG)⁻¹ ∧
      zetaM hG ∈ (yMc hG).range ∧
      ∀ d : ↥(yMc hG).range, coverHom (yMc hG) yJ h d = 1 ↔
        (d : MGriess) ∈ Subgroup.zpowers (zetaM hG) := by
  haveI := card_ker_yJ_le.1
  obtain ⟨hfin, hcard⟩ := card_ker_coverHom_le (Φ := yMc hG) (ψ := yJ) h
  set K : Subgroup MGriess := (coverHom (yMc hG) yJ h).ker.map (yMc hG).range.subtype with hK
  have hmem : ∀ g : MGriess, g ∈ K ↔ ∃ y, yJ y = 1 ∧ yMc hG y = g := by
    intro g
    rw [hK, Subgroup.mem_map]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact (coverHom_eq_one_iff h d).1 hd
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨yMc hG y, y, rfl⟩, (coverHom_eq_one_iff h _).2 ⟨y, hy, rfl⟩, rfl⟩
  have hKe : ↥(coverHom (yMc hG) yJ h).ker ≃ ↥K :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).toEquiv
  haveI : Finite K := Finite.of_equiv _ hKe
  have hKcard : Nat.card K ≤ 3 := by
    rw [← Nat.card_congr hKe]
    exact hcard.trans card_ker_yJ_le.2
  have hζK : zetaM hG ∈ K := by
    rw [hmem]
    refine ⟨yWordC yVWord (by decide) (by decide) ^ 17, ?_, (zetaM_eq hG).symm⟩
    rw [yJ_eq_one_iff, Subgroup.coe_pow, map_pow]
    exact yKM_yV_pow
  have hcK : ∀ k ∈ K, tGriess * k * tGriess⁻¹ ∈ K := by
    intro k hk
    obtain ⟨y, hy, rfl⟩ := (hmem k).1 hk
    have hy' : evalWord (yGen 4 4 2) yF0 * (y : YGroup 4 4 2) *
        (evalWord (yGen 4 4 2) yF0)⁻¹ ∈ commutator (YGroup 4 4 2) :=
      (inferInstance : (commutator (YGroup 4 4 2)).Normal).conj_mem _ y.2 _
    refine (hmem _).2 ⟨⟨_, hy'⟩, ?_, ?_⟩
    · rw [yJ_eq_one_iff] at hy ⊢
      show yKM (evalWord (yGen 4 4 2) yF0 * (y : YGroup 4 4 2) *
        (evalWord (yGen 4 4 2) yF0)⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hy, mul_one, mul_inv_cancel]
    · show yM hG (evalWord (yGen 4 4 2) yF0 * (y : YGroup 4 4 2) *
        (evalWord (yGen 4 4 2) yF0)⁻¹) = tGriess * yM hG (y : YGroup 4 4 2) * tGriess⁻¹
      rw [map_mul, map_mul, map_inv, yM_yF0 hG]
  obtain ⟨h3, hinv, hzp⟩ := kernel_cyclic_three hKcard hζK hcK (tGriess_mul_yM_yVWord_pow_ne hG)
  refine ⟨h3, hinv, ⟨_, (zetaM_eq hG).symm⟩, fun d => ?_⟩
  rw [← hzp, hK, ← MonoidHom.mem_ker]
  exact (Subgroup.mem_map_iff_mem Subtype.val_injective).symm

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
