module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0Defs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIRed
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CaseASplit
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalA

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped MatrixGroups

namespace Eight2

namespace CtxA0

variable {X : Type} [Group X] [Finite X] (c : CtxA0 X)

theorem conj_t_az : c.s.t⁻¹ * (c.s.h.a * c.Z.z) * c.s.t = c.s.h.a * c.Z.z := by
  calc c.s.t⁻¹ * (c.s.h.a * c.Z.z) * c.s.t =
      (c.s.t⁻¹ * c.s.h.a * c.s.t) * (c.s.t⁻¹ * c.Z.z * c.s.t) := by group
    _ = c.Z.z * c.b * (c.s.h.a * c.b) := by rw [c.conj_t_a, c.hzb]
    _ = c.Z.z * (c.b * c.s.h.a) * c.b := by group
    _ = c.Z.z * (c.s.h.a * c.b) * c.b := by rw [c.hba]
    _ = c.Z.z * c.s.h.a * (c.b * c.b) := by group
    _ = c.s.h.a * c.Z.z := by rw [c.hbb, mul_one, c.hza]

theorem t_mem_centralizer_az : c.s.t ∈ centralizer ({c.s.h.a * c.Z.z} : Set X) := by
  rw [mem_centralizer_singleton_iff]
  calc c.s.t * (c.s.h.a * c.Z.z) = c.s.t * (c.s.t⁻¹ * (c.s.h.a * c.Z.z) * c.s.t) := by
        rw [c.conj_t_az]
    _ = c.s.h.a * c.Z.z * c.s.t := by group

end CtxA0

end Eight2

@[expose] def GS82Step2FuseInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
    ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) →
    (c.s.h.secG0 c.s.y).relIndex c.s.h.S ≠ 2 →
    ∃ g : X, g⁻¹ * c.s.h.a * g = c.s.h.a * c.b * c.Z.z ∧ g⁻¹ * c.Z.z * g = c.b

theorem gs82CaseAL4U4Input_of_fuse (hS : SchreierFor Blueprint.Catalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hCF : CFL4U4Prod) (h2 : GS82Step2FuseInput) (h6U : GS82Step6PumpInputA0)
    (h6T : GS82Step6ThreeInputA0) : GS82CaseAL4U4Input := by
  intro X _ _ c hA
  obtain ⟨g, hga, hgz⟩ : ∃ g : X, g⁻¹ * c.s.h.a * g = c.s.h.a * c.b * c.Z.z ∧
      g⁻¹ * c.Z.z * g = c.b := by
    by_cases hidx : (c.s.h.secG0 c.s.y).relIndex c.s.h.S = 2
    · have hxb := Eight2.CtxA.conj_x_b
        { toCtxA0 := c, hbU := c.b_mem_upperP_two_of_relIndex_eq_two hidx }
      exact ⟨c.s.t * c.s.h.x, c.conj_tu_a c.s.h.x_mem hxb, c.conj_tu_z c.s.h.x_mem hxb⟩
    · exact h2 X c hA hidx
  by_cases hq3 : c.s.p = 3 ∧ c.s.f = 1
  · exact h6T X c hA _ hga hgz hq3.1 hq3.2
  have := c.s.isSimpleGroup
  obtain ⟨N, hNX, hN, hδN, p', n, hp', hp'2, hn, ⟨eN⟩⟩ :
      ∃ N : Subgroup X, N ≤ centralizer ({c.b} : Set X) ⊓
          centralizer ({c.s.h.a * c.b * c.Z.z} : Set X) ∧
        IsPComponent 2 (N.subgroupOf (centralizer ({c.b} : Set X) ⊓
          centralizer ({c.s.h.a * c.b * c.Z.z} : Set X))) ∧
        c.s.h.a * c.b * c.Z.z ∈ N ∧
        ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
          Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n)) := by
    by_cases hLb : ((Seven.Lay c.s.h c.s.y).subgroupOf (centralizer ({c.b} : Set X))).IsSubnormal
    · obtain ⟨N, hNX, hN, hδN, hrest⟩ := gs82Step6ProdInputA0_of_cf hCF X c hA hq3
      obtain ⟨hNX', hN'⟩ := c.isPComponent_inf_of_subnormal hLb hNX hN
      exact ⟨N, hNX', hN', hδN, hrest⟩
    · exact h6U X c hA hq3 hLb
  exact Eight2.false_of_sl2_conj hS hCI hUc c.s.nonab c.s.kProper c.s.unbal c.s.notU
    c.s.h.orderOf_a c.s.h.J_le c.s.h.isPComponent_J c.s.J_normal (c.s.h.D_le_J c.Z.hzD) c.Z.hzz
    c.a_not_mem_J hga hgz hNX hN hδN hp' hp'2 hn eN

end CFSG.ComponentClassification.GSThmB
