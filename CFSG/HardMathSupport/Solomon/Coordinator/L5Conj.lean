module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Count

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Balance.Alt

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem glaPComponent_gLBConj_of_mem {X L : Subgroup G} (hL : GLAPComponent p X L) {t : G}
    (ht : t ∈ X) : GLAPComponent p X (GLBConj t L) := by
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL t
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer ht)] at h

theorem barX_gLBConj_ne {X L : Subgroup G} (hL : GLAPComponent p X L) {t : G} (ht : t ∈ X)
    (htN : t ∉ Subgroup.normalizer (L : Set G)) : barX p X (GLBConj t L) ≠ barX p X L := by
  intro h
  apply htN
  rw [mem_normalizer_iff_gLBConj_eq]
  exact glaPComponent_uniqueAux (glaPComponent_gLBConj_of_mem hL ht) hL h

omit [Finite G] in
theorem conjQuotEquiv_mk (g : G) (X : Subgroup G) (x : ↥X) :
    conjQuotEquiv p g X (QuotientGroup.mk x) = QuotientGroup.mk (conjEquiv g X x) := rfl

omit [Finite G] in
theorem centB_le_centB_gLBConj {B L : Subgroup G} {t : G} (htB : ∀ b ∈ B, b * t = t * b) :
    centB p B L ≤ centB p B (GLBConj t L) := by
  intro b hb
  obtain ⟨hbN, hbB, h1⟩ := mem_centB.1 hb
  have hc : Commute b t := htB b hbB
  have hbt : t * b * t⁻¹ = b := by rw [← hc.eq, mul_inv_cancel_right]
  have hbN' : b ∈ Subgroup.normalizer (GLBConj t L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_gLBConj, mem_gLBConj]
    have : t * (b * y * b⁻¹) * t⁻¹ = b * (t * y * t⁻¹) * b⁻¹ := by
      calc t * (b * y * b⁻¹) * t⁻¹ = (t * b * t⁻¹) * (t * y * t⁻¹) * (t * b * t⁻¹)⁻¹ := by group
        _ = b * (t * y * t⁻¹) * b⁻¹ := by rw [hbt]
    rw [this]
    exact Subgroup.mem_normalizer_iff.1 hbN _
  have key : ∀ x : ↥L, barAut p (GLBConj t L) ⟨b, hbN'⟩ (conjQuotEquiv p t L (QuotientGroup.mk x)) =
      conjQuotEquiv p t L (barAut p L ⟨b, hbN⟩ (QuotientGroup.mk x)) := by
    intro x
    rw [conjQuotEquiv_mk, barAut_mk, barAut_mk, conjQuotEquiv_mk]
    congr 1
    apply Subtype.ext
    show b * (t⁻¹ * (x : G) * t) * b⁻¹ = t⁻¹ * (b * (x : G) * b⁻¹) * t
    calc b * (t⁻¹ * (x : G) * t) * b⁻¹ = (b * t⁻¹) * (x : G) * (t * b⁻¹) := by group
      _ = (t⁻¹ * b) * (x : G) * (b⁻¹ * t) := by rw [hc.inv_right.eq, hc.symm.inv_right.eq]
      _ = t⁻¹ * (b * (x : G) * b⁻¹) * t := by group
  refine mem_centB.2 ⟨hbN', hbB, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := (conjQuotEquiv p t L).surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [key x, h1]
  rfl

omit [Finite G] in
theorem nonempty_barOf_gLBConj (_hp : p.Prime) (L : Subgroup G) (t : G) :
    Nonempty (barOf p L ≃* barOf p (GLBConj t L)) :=
  ⟨conjQuotEquiv p t L⟩

end CFSG.HardMathSupport.Solomon.Coordinator
