module

public import CFSG.LieType.SpecialLinear.TwoEnd.CoverType
public import CFSG.RepresentationTheory.FixedBaseChange

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.Theory.Representation
open scoped TensorProduct

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {E : Type} [Field E] {k : Type} [Field k] [Algebra E k] [Algebra F k]
  {m : ℕ} {X : Type} [AddCommGroup X] [Module E X]

omit [Fintype F] [CharP F 2] in
private theorem twoEndNormalizer :
    ∀ g : SpecialLinearGroup (Fin (m + 1)) F,
      ∀ n ∈ twoEndRadical m F, embedMid m F g * n * (embedMid m F g)⁻¹ ∈ twoEndRadical m F :=
  fun g _ hn => embedMid_conj_mem_twoEndRadical (m := m) (F := F) (h := g) hn

theorem stage_twoEnd_isSimpleRep [CharP k 2]
    (σ : Representation E (SpecialLinearGroup (Fin (m + 3)) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ))
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (m + 3)) F → k}
    {J : Finset (Fin (m + 2))}
    (ht : IsCoverType (rankOne (m + 2) F 2) (extendScalars k σ) y χ J) :
    IsSimpleRep (extendScalars k (twoEndRestrict m F σ)) := by
  classical
  let e : RepEquiv (extendScalars k (twoEndRestrict m F σ))
      (twoEndRestrict m F (extendScalars k σ)) :=
    sectionRepExtendScalarsEquiv k σ (twoEndRadical m F) (embedMid m F) twoEndNormalizer
  have h := twoEndRestrict_isSimple (m := m) (F := F) (p := 2) (k := k)
    (V := k ⊗[E] X) (extendScalars k σ) hsimp ht
  exact IsSimpleRep.of_linearEquiv e.symm.toLinearEquiv e.symm.isIntertwining h

omit [Algebra F k] in
theorem stage_twoEnd_isCoverType
    (σ : Representation E (SpecialLinearGroup (Fin (m + 3)) F) X)
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (m + 3)) F → k}
    {J : Finset (Fin (m + 2))}
    (ht : IsCoverType (rankOne (m + 2) F 2) (extendScalars k σ) y χ J) :
    ∃ y' : k ⊗[E] (twoEndFix m F σ),
      IsCoverType (rankOne m F 2) (extendScalars k (twoEndRestrict m F σ)) y'
        (χ ∘ embedMid m F)
        (Finset.univ.filter fun s : Fin m => s.castSucc.succ ∈ J) := by
  classical
  let e : RepEquiv (extendScalars k (twoEndRestrict m F σ))
      (twoEndRestrict m F (extendScalars k σ)) :=
    sectionRepExtendScalarsEquiv k σ (twoEndRadical m F) (embedMid m F) twoEndNormalizer
  have h := twoEndRestrict_isCoverType (m := m) (F := F) (p := 2) (k := k)
    (V := k ⊗[E] X) (extendScalars k σ) ht
  exact ⟨e.symm ⟨y, mem_twoEndFix_of_isCoverType (m := m) (F := F) (p := 2)
      (extendScalars k σ) ht⟩,
    IsCoverType.of_linearEquiv e.symm.toLinearEquiv e.symm.isIntertwining h⟩

end

end CFSG.LieType.SpecialLinear
