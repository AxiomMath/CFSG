module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Out
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import Certificates.Certificate110

public section

namespace CFSG.ComponentClassification.RankTwoM11

open Subgroup

theorem exists_inv_mul_mem_centralizer {G : Type} [Group G] {B : Subgroup G}
    (hB : Nonempty (↥B ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) {n : G}
    (hn : n ∈ normalizer (B : Set G)) : ∃ y ∈ B, y⁻¹ * n ∈ centralizer (B : Set G) := by
  obtain ⟨y, hy, hyx⟩ := CFSG.QuasithinUnique.m11OutTrivial G B hB n hn
  refine ⟨y, hy, mem_centralizer_iff.mpr fun x hx => ?_⟩
  calc x * (y⁻¹ * n) = y⁻¹ * (y * x * y⁻¹) * n := by group
    _ = y⁻¹ * (n * x * n⁻¹) * n := by rw [hyx x hx]
    _ = y⁻¹ * n * x := by group

theorem hypII_of_equiv {A : Type*} [Group A]
    (e : A ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) : AS76b.HypII A := by
  intro H _ _ B T ⟨f⟩ hT _ t ht
  obtain ⟨y, hy, hk⟩ := exists_inv_mul_mem_centralizer ⟨f.trans e⟩ (hT.2.2.1 ht)
  rw [show t = y * (y⁻¹ * t) by group]
  exact mul_mem_sup hy hk

end CFSG.ComponentClassification.RankTwoM11
