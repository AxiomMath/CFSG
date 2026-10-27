module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428SuzukiModelBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428SuzukiTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428SuzukiUnipotent

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open TauCeti

theorem suzukiS_eq_unipotentMatrix (m : ℕ) (u v : GaloisField 2 (2 * m + 1)) :
    CFSG.Blueprint.suzukiS m u v =
      TauCeti.Suzuki.unipotentMatrix m u (v + u ^ (2 ^ (m + 1) + 1)) := by
  have hv : u ^ (2 ^ (m + 1) + 1) + (v + u ^ (2 ^ (m + 1) + 1)) = v := by
    rw [← add_assoc, add_comm (u ^ (2 ^ (m + 1) + 1)) v, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  have h := suzukiS_eq_unipotent m u (v + u ^ (2 ^ (m + 1) + 1))
  rwa [hv] at h

theorem blueprint_suzukiGroup_eq_tauCeti (m : ℕ) :
    CFSG.Blueprint.suzukiGroup m (GaloisField 2 (2 * m + 1)) = TauCeti.suzukiGroup m := by
  refine le_antisymm ?_ ?_
  ·
    refine (Subgroup.closure_le (TauCeti.suzukiGroup m)).mpr ?_
    rintro g (⟨u, v, hg⟩ | ⟨l, hg⟩ | hg)
    · have hg' : g = TauCeti.Suzuki.unipotent m u (v + u ^ (2 ^ (m + 1) + 1)) := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        rw [hg, suzukiS_eq_unipotentMatrix, TauCeti.Suzuki.coe_unipotent]
      rw [hg']
      exact TauCeti.Suzuki.unipotent_mem_suzukiGroup (n := m) _ _
    · have hg' : g = TauCeti.Suzuki.torus m (l ^ (1 + 2 ^ m)) := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        rw [hg, suzukiD_eq_torusMatrix, TauCeti.Suzuki.coe_torus]
      rw [hg']
      exact TauCeti.Suzuki.torus_mem_suzukiGroup (m := m) _
    · have hg' : g = TauCeti.Suzuki.weyl m := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        rw [hg, suzukiW_eq_weylMatrix, TauCeti.Suzuki.coe_weyl]
      rw [hg']
      exact TauCeti.Suzuki.weyl_mem_suzukiGroup
  ·
    rw [TauCeti.Suzuki.suzukiGroup_le_iff]
    refine ⟨?_, ?_⟩
    · intro a b
      refine Subgroup.subset_closure (Or.inl ⟨a, a ^ (2 ^ (m + 1) + 1) + b, ?_⟩)
      rw [TauCeti.Suzuki.coe_unipotent, suzukiS_eq_unipotent]
    · refine Subgroup.subset_closure (Or.inr (Or.inr ?_))
      rw [TauCeti.Suzuki.coe_weyl]
      exact (suzukiW_eq_weylMatrix m).symm

end CFSG.LocalAnalysis.GLTheoremA
