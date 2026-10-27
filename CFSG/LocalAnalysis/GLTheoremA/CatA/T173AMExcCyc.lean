module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Quot
import CFSG.HardMathSupport.Solomon.Coordinator.I10_20Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem uexc_cycModSylow_map {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} (hS : S.Normal) (Z : Subgroup Ω) [Z.Normal] (hZ : ¬ p ∣ Nat.card Z)
    (hcyc : CycModSylow p S) : CycModSylow p (S.map (QuotientGroup.mk' Z)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hker : ¬ p ∣ Nat.card (QuotientGroup.mk' Z).ker := by
    rw [QuotientGroup.ker_mk']
    exact hZ
  intro E hE hEp
  obtain ⟨Et, hEtp, hEtmap, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i1020_frattini_lift
    (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) hEp
  have hcyc' : IsCyclic Et := by
    refine hcyc _ (fun g hg => ?_) hEtp
    have hgE : QuotientGroup.mk' Z g ∈ E := by rw [← hEtmap]; exact ⟨g, hg, rfl⟩
    have h1 := hE _ hgE
    rw [centMod_iff] at h1 ⊢
    have hgS : g ∈ Subgroup.normalizer (S : Set Ω) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hS]
      exact Subgroup.mem_top g
    exact (S267.mem_centModSubgroup_map_iff hp (QuotientGroup.mk' Z) hker hgS).2 h1
  let f : ↥Et →* ↥E := ((QuotientGroup.mk' Z).comp Et.subtype).codRestrict E (fun x => by
    rw [← hEtmap]; exact ⟨x, x.2, rfl⟩)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : Ω ⧸ Z) ∈ Et.map (QuotientGroup.mk' Z) := by rw [hEtmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact isCyclic_of_surjective f hsurj

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
