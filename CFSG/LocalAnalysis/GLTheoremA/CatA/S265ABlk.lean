module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ACount
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks4
import TauCeti.LinearAlgebra.Dimension.DirectSum

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ}

theorem finrank_eq_fixedByEnd_add_nOut (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (a : ↥A) :
    Module.finrank F V = Module.finrank F ↥(fixedByEnd (a : V ≃ₗ[F] V)) +
      nOut (fun D : Hyperplane A p => D.1) (fun D => Module.finrank F ↥(blockSpace A D.1)) a := by
  classical
  set f : V →ₗ[F] V := (a : V ≃ₗ[F] V).toLinearMap - LinearMap.id
  have hfv : ∀ v, f v = (a : V ≃ₗ[F] V) v - v := fun v => rfl
  set W : Hyperplane A p → Submodule F V :=
    fun D => if a ∈ D.1 then ⊥ else blockSpace A D.1 with hW
  have hker : LinearMap.ker f = fixedByEnd (a : V ≃ₗ[F] V) := by
    ext v
    rw [LinearMap.mem_ker, mem_fixedByEnd, hfv, sub_eq_zero]
  have hle : LinearMap.range f ≤ ⨆ D, W D := by
    rw [LinearMap.range_eq_map, ← sup_fixedSpaceOf_iSup_blockSpace A hp hpF hA,
      Submodule.map_sup, Submodule.map_iSup]
    refine sup_le ?_ (iSup_mono fun D => ?_)
    · rintro _ ⟨v, hv, rfl⟩
      rw [hfv, (mem_fixedSpaceOf A).1 hv a, sub_self]
      exact Submodule.zero_mem _
    · rintro _ ⟨v, hv, rfl⟩
      by_cases haD : a ∈ D.1
      · rw [hfv, ((mem_blockSpace A).1 hv).1 a haD, sub_self]
        exact Submodule.zero_mem _
      · simp only [hW, haD, if_false]
        exact Submodule.sub_mem _ (blockSpace_invariant A hp hpF hA hv) hv
  have hge : (⨆ D, W D) ≤ LinearMap.range f := by
    refine iSup_le fun D => ?_
    by_cases haD : a ∈ D.1
    · simp only [hW, haD, if_true, bot_le]
    · simp only [hW, haD, if_false]
      have hmaps : ∀ v ∈ blockSpace A D.1, f v ∈ blockSpace A D.1 := fun v hv =>
        Submodule.sub_mem _ (blockSpace_invariant A hp hpF hA hv) hv
      have hinj : Function.Injective (f.restrict hmaps) := by
        rw [injective_iff_map_eq_zero]
        intro v hv
        have h0 : f v = 0 := congrArg Subtype.val hv
        rw [hfv, sub_eq_zero] at h0
        exact Subtype.ext (eq_zero_of_fixed_mem_blockSpace A hp hpF hA haD v.2 h0)
      intro w hw
      obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨w, hw⟩
      exact LinearMap.mem_range.2 ⟨v, congrArg Subtype.val hv⟩
  have hind : iSupIndep W := (iSupIndep_blockSpace A hp hpF hA).mono fun D => by
    by_cases haD : a ∈ D.1 <;> simp [hW, haD]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [le_antisymm hle hge, hker, TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hind] at hrn
  have hsum : ∑ D, Module.finrank F ↥(W D) =
      nOut (fun D : Hyperplane A p => D.1) (fun D => Module.finrank F ↥(blockSpace A D.1)) a := by
    unfold nOut
    refine Finset.sum_congr rfl fun D _ => ?_
    by_cases haD : a ∈ D.1
    · simp [hW, haD]
    · have hWD : W D = blockSpace A D.1 := by simp only [hW, haD, if_false]
      rw [hWD]
      simp [haD]
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
