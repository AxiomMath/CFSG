module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Three
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Asm

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open CFSG.LieType.BorelTits (orthGroup)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell (card_orthGroup_quadPlus_two)
open scoped commutatorElement

theorem isSolvable_statedOmega_plus_two :
    Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) := by
  have hcard : Nat.card ↥(orthGroup (StatedQuadPlus 2 (ZMod 2))) = 2 ^ 3 * 3 ^ 2 := by
    rw [card_orthGroup_quadPlus_two, Nat.card_zmod]; norm_num
  haveI : Fintype ↥(orthGroup (StatedQuadPlus 2 (ZMod 2))) := Fintype.ofFinite _
  have hO : Group.IsSolvable ↥(orthGroup (StatedQuadPlus 2 (ZMod 2))) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])
  have hle : StatedOmega (StatedQuadPlus 2 (ZMod 2)) ≤ orthGroup (StatedQuadPlus 2 (ZMod 2)) := by
    show ⁅orthGroup (StatedQuadPlus 2 (ZMod 2)), orthGroup (StatedQuadPlus 2 (ZMod 2))⁆ ≤ _
    rw [Subgroup.commutator_le]
    intro g hg h hh
    simp only [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh) (Subgroup.inv_mem _ hg))
      (Subgroup.inv_mem _ hh)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).symm.injective

theorem omegaFourComponentCentre_holds : OmegaFourComponentCentre := by
  intro ε X _ _ K hK hΩ
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2.2.2
  obtain ⟨a, b, hab⟩ := (isQuasisimple_of_comp hK).2.2
  cases ε
  · obtain ⟨e⟩ := hΩ
    haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1)) :=
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.isSimpleGroup_statedOmega_quadMinus_two
    haveI : IsSimpleGroup ↥K := e.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
    · exact h
    · exfalso
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      have hx : x ∈ Subgroup.center ↥K := by rw [h]; exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.1 hx y).symm
  · exfalso
    obtain ⟨e⟩ := hΩ
    haveI : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) :=
      isSolvable_statedOmega_plus_two
    haveI : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    haveI : Group.IsSolvable (↥K ⧸ Subgroup.center ↥K) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 inferInstance) a b)

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
