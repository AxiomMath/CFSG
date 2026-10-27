module

public import CFSG.RankThree.PartOne.KS.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrFrattini
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBDefs

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut CFSG.Open CFSG.QuasithinUnique
open CFSG.RankThree.PartOne (centerQuotientAction commute_of_centerQuotientAction_eq_one
  centerQuotientAction_mk center_eq_bot_of_simple conj_injective_of_center_eq_bot)
open scoped commutatorElement

@[expose] def YLevelIrr : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsClassicalTwoOrG2 Y →
    Function.Injective (MulAut.conj : Y →* MulAut Y) →
    ∀ (p r : ℕ), p.Prime → p ≠ 2 → r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p →
    ∀ (S₀ : Sylow 2 Y) (J : Subgroup Y), Subgroup.normalizer (S₀ : Set Y) ≤ J →
      PerfectCyclicSylow p J →
      ∀ (U Z : Subgroup (MulAut Y)) (y : MulAut Y), IsPGroup p U → Z = ⁅U, U⁆ → IrrAct y U Z →
        p ^ 3 ≤ Z.relIndex U → (∀ u ∈ U, u ^ p ∈ Z) →
        y ∈ Subgroup.normalizer (U : Set (MulAut Y)) →
        U ≤ Subgroup.normalizer
          ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)) →
        y ∈ Subgroup.normalizer
          ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)) →
        (∃ a : ℕ, y ^ r ^ a = 1) → False

theorem conj_injective_of_isQuasisimple {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) :
    Function.Injective
      (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)) := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2
  have hnab : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := by
    have : Group.IsPerfect L := ⟨hL.1⟩
    have hnoncomm := Group.IsPerfect.not_isMulCommutative (L ⧸ Subgroup.center L)
    simpa only [isMulCommutative_iff, not_forall] using hnoncomm
  exact conj_injective_of_center_eq_bot (center_eq_bot_of_simple hnab)

section Aux

theorem mem_normalizer_map_conj_of_iff {Y : Type*} [Group Y] {J : Subgroup Y} {α : MulAut Y}
    (h : ∀ x, x ∈ J ↔ α x ∈ J) :
    α ∈ Subgroup.normalizer
      ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨α x, (h x).1 hx, ?_⟩
    ext w
    simp [MulAut.conj_apply]
  · rintro ⟨x', hx', hx'b⟩
    have hb : b = MulAut.conj (α.symm x') := by
      have : α * b * α⁻¹ = MulAut.conj x' := hx'b.symm
      ext w
      have := congrArg (fun f : MulAut Y => α.symm (f (α w))) this
      simpa [MulAut.conj_apply] using this
    refine ⟨α.symm x', (h _).2 ?_, hb.symm⟩
    simpa using hx'

variable {X : Type} [Group X]

theorem mk_mem_quotImage_iff {L J : Subgroup X}
    (hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : X) ∈ J) (l : ↥L) :
    (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) ∈ quotImage L J ↔ (l : X) ∈ J := by
  constructor
  · intro h
    obtain ⟨l', hl'J, hl'⟩ := mem_quotImage.1 h
    have hz : l'⁻¹ * l ∈ Subgroup.center ↥L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hl',
        inv_mul_cancel]
    have hzJ := hZ _ hz
    have : (l : X) = (l' : X) * ((l'⁻¹ * l : ↥L) : X) := by simp
    rw [this]
    exact J.mul_mem hl'J hzJ
  · intro h
    exact mem_quotImage.2 ⟨l, h, rfl⟩

end Aux

end CFSG.AGLEmbedding.ParabAutIrr
