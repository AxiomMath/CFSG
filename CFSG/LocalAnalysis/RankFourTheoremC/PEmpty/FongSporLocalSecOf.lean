module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalGenW
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermSecDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open Subgroup

theorem secW_of_parts {G : Type} [Group G] (a b : G) (c : PGen) (h1 h2 : List (ℕ × ℕ))
    (hp : c.p.Prime) (hbase : c.holdsBase a b)
    (hS : IsSimpleGroup ↥(closure ({evalIdx (c.regs a b) h1, evalIdx (c.regs a b) h2} : Set G)) ∧
      ¬ IsMulCommutative ↥(closure ({evalIdx (c.regs a b) h1,
        evalIdx (c.regs a b) h2} : Set G)) ∧
      evalPW a b c.z ∈ closure ({evalIdx (c.regs a b) h1, evalIdx (c.regs a b) h2} : Set G) ∧
      3 ∣ Nat.card ↥(closure ({evalIdx (c.regs a b) h1, evalIdx (c.regs a b) h2} : Set G))) :
    SecW G c.p := by
  have hfact : Fact c.p.Prime := ⟨hp⟩
  obtain ⟨hS1, hS2, hS3, hS4⟩ := hS
  refine ⟨evalPW a b c.z, {x | ∃ n ∈ c.ns, x = evalPW a b n.1},
    {x | ∃ m ∈ c.ms, x = evalPW a b m.1},
    closure ({evalIdx (c.regs a b) h1, evalIdx (c.regs a b) h2} : Set G), ?_, ?_, ?_, ?_, hS1, hS2,
    hS3, hS4⟩
  · exact orderOf_eq_prime hbase.1 hbase.2.1
  · rintro x ⟨n, hn, rfl⟩
    obtain ⟨h4, h5⟩ := hbase.2.2.2.1 n hn
    exact mem_normalizer_zpowers_of _ _ n.2.1 n.2.2 h4 h5
  · rintro x ⟨m, hm, rfl⟩
    obtain ⟨w, hw, hcomm⟩ := hbase.2.2.2.2 m hm
    obtain ⟨hw1, hw2, hw3⟩ := hbase.2.2.1 w hw
    exact ⟨evalPW a b w, hw1, hw2, hw3, hcomm⟩
  · rw [Subgroup.closure_le]
    have hreg : ∀ x ∈ c.regs a b, x ∈ closure (({x | ∃ n ∈ c.ns, x = evalPW a b n.1} ∪
        {x | ∃ m ∈ c.ms, x = evalPW a b m.1} : Set G)) := by
      intro x hx
      simp only [PGen.regs, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨n, hn, rfl⟩ | ⟨m, hm, rfl⟩
      · exact subset_closure (Or.inl ⟨n, hn, rfl⟩)
      · exact subset_closure (Or.inr ⟨m, hm, rfl⟩)
    exact Set.insert_subset_iff.mpr ⟨evalIdx_mem _ _ hreg h1,
      Set.singleton_subset_iff.mpr (evalIdx_mem _ _ hreg h2)⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
