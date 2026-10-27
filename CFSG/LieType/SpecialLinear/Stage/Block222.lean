module

public import CFSG.LieType.SpecialLinear.Block222.CoverType
public import CFSG.LieType.SpecialLinear.Stage.Active
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
  {c : ℕ} {X : Type} [AddCommGroup X] [Module E X]

omit [Fintype F] [CharP F 2] in
private theorem block222Normalizer :
    ∀ g : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin c) F ×
        SpecialLinearGroup (Fin 2) F,
      ∀ n ∈ blockRadical222 c F,
        blockEmbed222 c F g * n * (blockEmbed222 c F g)⁻¹ ∈ blockRadical222 c F :=
  fun g _ hn => blockRadical222_normalized c F ⟨g, rfl⟩ hn

theorem stage_block222_isSimpleRep [CharP k 2]
    (σ : Representation E (SpecialLinearGroup (Fin (c + 4)) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ))
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (c + 4)) F → k}
    {J : Finset (Fin (c + 3))}
    (ht : IsCoverType (rankOne (c + 3) F 2) (extendScalars k σ) y χ J) :
    IsSimpleRep (blockRestrict222 c F σ) := by
  classical
  have h := blockRestrict222_isSimple_of_isCoverType (c := c) (F := F) (p := 2)
    (k := k) (V := k ⊗[E] X) (ρ := extendScalars k σ) hsimp
    (by simpa using splitOver (c + 3) F 2 k) ht
  exact isSimpleRep_sectionRep_of_extendScalars (F' := k) σ (blockRadical222 c F)
    (blockEmbed222 c F) block222Normalizer h

omit [Algebra F k] in
theorem stage_block222_left_ne_one [CharP k 2]
    (σ : Representation E (SpecialLinearGroup (Fin (c + 4)) F) X)
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (c + 4)) F → k}
    {J : Finset (Fin (c + 3))}
    (ht : IsCoverType (rankOne (c + 3) F 2) (extendScalars k σ) y χ J)
    (h0 : (⟨0, by omega⟩ : Fin (c + 3)) ∉ J) :
    ∃ g, blockRestrict222 c F σ (g, 1, 1) ≠ 1 := by
  classical
  have ht1 := factor1_isCoverType (c := c) (F := F) (p := 2)
    (ρ := extendScalars k σ) ht
  have h0' : (0 : Fin 1) ∉ (Finset.univ.filter fun _ : Fin 1 =>
      (⟨0, by omega⟩ : Fin (c + 3)) ∈ J) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h0
  obtain ⟨g, hg⟩ := exists_ne_one_of_not_mem_isCoverType (n := 1) (p := 2) (F := F)
    (V := blockFix222 c F (extendScalars k σ))
    (ρ := factor1Rep c F (extendScalars k σ)) ht1 (s := 0) h0'
  refine ⟨g, fun h1 => hg ?_⟩
  have hiff := sectionRep_eq_one_iff (F' := k) σ (blockRadical222 c F)
    (blockEmbed222 c F) block222Normalizer (g, 1, 1)
  have h1' : sectionRep σ (blockRadical222 c F) (blockEmbed222 c F) block222Normalizer
      (g, 1, 1) = 1 := by
    change blockRestrict222 c F σ (g, 1, 1) = 1
    exact h1
  have hk : blockRestrict222 c F (extendScalars k σ) (g, 1, 1) = 1 := hiff.mpr h1'
  simpa [factor1Rep, leftHom222] using hk

omit [Algebra F k] in
theorem stage_block222_right_ne_one [CharP k 2]
    (σ : Representation E (SpecialLinearGroup (Fin (c + 4)) F) X)
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (c + 4)) F → k}
    {J : Finset (Fin (c + 3))}
    (ht : IsCoverType (rankOne (c + 3) F 2) (extendScalars k σ) y χ J)
    (hl : (⟨c + 2, by omega⟩ : Fin (c + 3)) ∉ J) :
    ∃ g, blockRestrict222 c F σ (1, 1, g) ≠ 1 := by
  classical
  have ht3 := factor3_isCoverType (c := c) (F := F) (p := 2)
    (ρ := extendScalars k σ) ht
  have hl' : (0 : Fin 1) ∉ (Finset.univ.filter fun _ : Fin 1 =>
      (⟨c + 2, by omega⟩ : Fin (c + 3)) ∈ J) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hl
  obtain ⟨g, hg⟩ := exists_ne_one_of_not_mem_isCoverType (n := 1) (p := 2) (F := F)
    (V := blockFix222 c F (extendScalars k σ))
    (ρ := factor3Rep c F (extendScalars k σ)) ht3 (s := 0) hl'
  refine ⟨g, fun h1 => hg ?_⟩
  have hiff := sectionRep_eq_one_iff (F' := k) σ (blockRadical222 c F)
    (blockEmbed222 c F) block222Normalizer (1, 1, g)
  have h1' : sectionRep σ (blockRadical222 c F) (blockEmbed222 c F) block222Normalizer
      (1, 1, g) = 1 := by
    change blockRestrict222 c F σ (1, 1, g) = 1
    exact h1
  have hk : blockRestrict222 c F (extendScalars k σ) (1, 1, g) = 1 := hiff.mpr h1'
  simpa [factor3Rep, rightHom222] using hk

end

end CFSG.LieType.SpecialLinear
