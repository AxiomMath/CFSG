module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0L
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIProdDefs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped MatrixGroups

theorem gs82Step6ProdInputA0_of_cf (hCF : CFL4U4Prod) :
    ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
      ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) →
      ¬ (c.s.p = 3 ∧ c.s.f = 1) →
      ∃ N : Subgroup X, N ≤ Seven.Lay c.s.h c.s.y ⊓
          centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) ∧
        IsPComponent 2 (N.subgroupOf (Seven.Lay c.s.h c.s.y ⊓
          centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) ∧
        c.s.h.a * c.b * c.Z.z ∈ N ∧
        ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
          Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) := by
  intro X _ _ c hA hq3
  have hJ0Lie : Blueprint.LieModel (↥(Seven.J0 c.s.h c.s.y) ⧸
      pPrimeCore 2 ↥(Seven.J0 c.s.h c.s.y)) .PSL 2 c.s.p (2 * c.s.f) := by
    rcases c.isSec8JType_J0 with h1 | ⟨h3, h1, -⟩
    · exact h1
    · exact absurd ⟨h3, h1⟩ hq3
  exact Seven.exists_sl2_of_cfL4U4 hCF c.s.hp c.s.hp2 c.s.hf hq3 (c.lieModel_Lay hA) c.ab_mem_Lay
    c.ab_mul_ab c.ab_ne_one c.Z.hzz c.Z.hz1 c.ab_comm_z c.z_ne_ab (Seven.J0_le_Lay c.s.h c.s.y)
    c.J0_le_centralizer_ab c.Lay_inf_centralizer_ab_le
    (Hyp52.isPComponent_secJ0 (h := c.s.h) (y := c.s.y)) hJ0Lie (c.s.D_le_J0 c.Z.hzD)

theorem gs82Step6ProdInputA0Card_of_cf (hCF : CFL4U4ProdCard) :
    ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
      ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) →
      ¬ (c.s.p = 3 ∧ c.s.f = 1) →
      ∃ N : Subgroup X, N ≤ Seven.Lay c.s.h c.s.y ⊓
          centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) ∧
        IsPComponent 2 (N.subgroupOf (Seven.Lay c.s.h c.s.y ⊓
          centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) ∧
        c.s.h.a * c.b * c.Z.z ∈ N ∧
        ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
          Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) ∧
          p' ^ n = c.s.p ^ c.s.f := by
  intro X _ _ c hA hq3
  have hJ0Lie : Blueprint.LieModel (↥(Seven.J0 c.s.h c.s.y) ⧸
      pPrimeCore 2 ↥(Seven.J0 c.s.h c.s.y)) .PSL 2 c.s.p (2 * c.s.f) := by
    rcases c.isSec8JType_J0 with h1 | ⟨h3, h1, -⟩
    · exact h1
    · exact absurd ⟨h3, h1⟩ hq3
  exact Seven.exists_sl2_of_cfL4U4Card hCF c.s.hp c.s.hp2 c.s.hf hq3 (c.lieModel_Lay hA)
    c.ab_mem_Lay c.ab_mul_ab c.ab_ne_one c.Z.hzz c.Z.hz1 c.ab_comm_z c.z_ne_ab
    (Seven.J0_le_Lay c.s.h c.s.y) c.J0_le_centralizer_ab c.Lay_inf_centralizer_ab_le
    (Hyp52.isPComponent_secJ0 (h := c.s.h) (y := c.s.y)) hJ0Lie (c.s.D_le_J0 c.Z.hzD)

end CFSG.ComponentClassification.GSThmB
