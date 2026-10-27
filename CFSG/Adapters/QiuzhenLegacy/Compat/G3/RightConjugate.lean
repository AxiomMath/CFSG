module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.theorem_6_4

public section

namespace CFSG.BenderSuzuki.PFchapter1section1

theorem rightConjugate_eq_self_of_mem_normalizer
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    rightConjugate H g = H := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    have hg_inv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hg
    exact (Subgroup.mem_normalizer_iff.mp hg_inv y).1 hy
  · intro hx
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hg x).1 hx
    · calc
        (MulAut.conj g⁻¹) (g * x * g⁻¹) =
            g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ := rfl
        _ = x := by group

theorem mem_normalizer_of_rightConjugate_eq_self
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : rightConjugate H g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  apply CFSG.mem_normalizer_of_conjBy_eq_local
  have h' : H.conjBy g⁻¹ = H := by
    simpa [rightConjugate] using h
  simpa [h'] using (Subgroup.conjBy_inv' H g)

end CFSG.BenderSuzuki.PFchapter1section1
