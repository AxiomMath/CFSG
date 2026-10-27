module

public import CFSG.LieType.AlgebraicGroups.KernelRootGroup
public import CFSG.LieType.AlgebraicGroups.KernelRootCoordinates
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat
public import CFSG.HardMathSupport.Timmesfeld.Torality.Conjugacy
import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.AlgebraicGroups

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open scoped Pointwise


variable {τ : Tag} {M : Type} [CommGroup M]

theorem posRoots_kernelRoots_closed (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    ∀ α ∈ posRoots (kernelRoots χ), ∀ β ∈ posRoots (kernelRoots χ), ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ posRoots (kernelRoots χ) := by
  rintro α ⟨⟨-, hα⟩, hαh⟩ β ⟨⟨-, hβ⟩, hβh⟩ a b ha hb hr
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  refine ⟨⟨hr, ?_⟩, ?_⟩
  · rw [ofAdd_add, map_mul, ofAdd_nsmul, ofAdd_nsmul, map_pow, map_pow, hα, hβ, one_pow,
      one_pow, one_mul]
  · rw [height_nsmul_add_nsmul]
    exact add_pos (mul_pos ha' hαh) (mul_pos hb' hβh)

theorem posRoots_kernelRoots_neg_closed (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (w : WeylGroup τ) :
    ∀ α ∈ {α | α ∈ posRoots (kernelRoots χ) ∧ height (w • α) < 0},
      ∀ β ∈ {α | α ∈ posRoots (kernelRoots χ) ∧ height (w • α) < 0}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot τ (a • α + b • β) →
          a • α + b • β ∈ {α | α ∈ posRoots (kernelRoots χ) ∧ height (w • α) < 0} := by
  rintro α ⟨hα, hwα⟩ β ⟨hβ, hwβ⟩ a b ha hb hr
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  refine ⟨posRoots_kernelRoots_closed χ α hα β hβ a b ha hb hr, ?_⟩
  rw [smul_nsmul_add_nsmul, height_nsmul_add_nsmul]
  exact add_neg (mul_neg_of_pos_of_neg ha' hwα) (mul_neg_of_pos_of_neg hb' hwβ)

theorem mem_torus_sup_rootSpan_of_baseChangeGL_mem {K L : Type} [Field K] [Field L]
    (ι : K →+* L) (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {x : ModGL τ K}
    (hx : x ∈ adjointGroup τ K)
    (hxL : baseChangeGL ι x ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ)) :
    x ∈ torusGroup τ K ⊔ rootSpan τ K (kernelRoots χ) := by
  have hSig : ∀ α ∈ kernelRoots χ, IsRoot τ α := fun α hα => hα.1
  obtain ⟨w, h, hh, u, hu, v, hv, rfl⟩ := bruhat_factor_exists τ K x hx
  have hxL' : baseChangeGL ι (h * u * canonicalRep (coxeterSystem τ) K w * v) ∈
      (torusGroup τ L : Set (ModGL τ L)) * (rootSpan τ L (kernelRoots χ) : Set (ModGL τ L)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (torusGroup_le_normalizer_rootSpan (K := L) hSig)]
    exact hxL
  obtain ⟨t, ht, s, hs, hts⟩ := hxL'
  obtain ⟨w', hw', h', hh', u', hu', v', hv', rfl⟩ := exists_kernelRoots_bruhat_factor χ hs
  have hu'P : u' ∈ posUnipotent τ L :=
    rootSpan_mono (S := posRoots (kernelRoots χ)) (T := {α | IsRoot τ α ∧ 0 < height α})
      (fun α hα => ⟨hα.1.1, hα.2⟩) hu'
  have hv'I : v' ∈ rootSpan τ L (inversionSet w') :=
    rootSpan_mono (S := {α | α ∈ posRoots (kernelRoots χ) ∧ height (w' • α) < 0})
      (T := inversionSet w') (fun α hα => ⟨hα.1.1.1, hα.1.2, IsRoot.smul hα.1.1.1 w', hα.2⟩) hv'
  have heq : baseChangeGL ι h * baseChangeGL ι u * canonicalRep (coxeterSystem τ) L w *
      baseChangeGL ι v = (t * h') * u' * canonicalRep (coxeterSystem τ) L w' * v' := by
    rw [map_mul, map_mul, map_mul, baseChangeGL_canonicalRep] at hts
    rw [← hts]
    simp only [mul_assoc]
  obtain ⟨hww, -, huu, hvv⟩ := bruhat_factor_unique τ L w w' _ _ _ _ _ _
    (baseChangeGL_mem_torusGroup ι hh) (mul_mem ht hh') (baseChangeGL_mem_rootSpan ι hu) hu'P
    (baseChangeGL_mem_rootSpan ι hv) hv'I heq
  subst hww
  have hPfin : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.Finite :=
    (finite_setOf_isRoot τ).subset fun _ hα => hα.1
  have huK : u ∈ rootSpan τ K (posRoots (kernelRoots χ)) :=
    mem_rootSpan_of_baseChangeGL_mem ι hPfin (fun α hα => ⟨hα.1.1, hα.2⟩) (fun α hα => hα)
      posRoots_closed (posRoots_kernelRoots_closed χ) hu (by rw [huu]; exact hu')
  have hvK : v ∈ rootSpan τ K {α | α ∈ posRoots (kernelRoots χ) ∧ height (w • α) < 0} :=
    mem_rootSpan_of_baseChangeGL_mem ι (inversionSet_finite w)
      (fun α hα => ⟨hα.1.1.1, hα.1.2, IsRoot.smul hα.1.1.1 w, hα.2⟩)
      (fun α hα => ⟨hα.1, hα.2.1⟩) (inversionSet_closed w) (posRoots_kernelRoots_neg_closed χ w)
      hv (by rw [hvv]; exact hv')
  have hU : ∀ {S : Set (Fin τ.rank → ℤ)}, S ⊆ kernelRoots χ →
      rootSpan τ K S ≤ torusGroup τ K ⊔ rootSpan τ K (kernelRoots χ) :=
    fun hS => (rootSpan_mono hS).trans le_sup_right
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hh) (hU (fun α hα => hα.1) huK))
    (canonicalRep_mem_torus_sup_rootSpan_kernelRoots hw')) (hU (fun α hα => hα.1.1) hvK)

end CFSG.LieType.AlgebraicGroups
