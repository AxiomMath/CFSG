module

public import CFSG.LieType.Chevalley.ToralCentralizerQuotient

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Steinberg

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem toralCentralizer_eq_toralRootGroup_of_stabilizer_le (τ : Tag) (K : Type) [Field K]
    (a : Fin τ.rank → Kˣ) (h : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    toralCentralizer τ K a = toralRootGroup τ K a := by
  obtain ⟨hMle, -, hWle, -, φ, hφ, hφapp⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient τ K a
  refine le_antisymm (fun g hg => ?_) hMle
  obtain ⟨c, hc⟩ := hφ (QuotientGroup.mk ⟨g, hg⟩)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective c
  have hw : (QuotientGroup.mk w : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) = 1 :=
    (QuotientGroup.eq_one_iff w).2 (Subgroup.mem_subgroupOf.2 (h w.2))
  rw [hw, map_one] at hc
  have := (QuotientGroup.eq_one_iff (⟨g, hg⟩ : toralCentralizer τ K a)).1 hc.symm
  exact Subgroup.mem_subgroupOf.1 this

end CFSG.HardMathSupport.Timmesfeld.Steinberg
