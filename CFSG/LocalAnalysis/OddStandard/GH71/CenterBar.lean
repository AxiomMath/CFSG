module

public import CFSG.LocalAnalysis.OddStandard.GH71.Setup

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

variable {G : Type} [Group G] [Finite G]

theorem not_mem_center_bar {v x : G} (hcard : Nat.card (center (HBar (Cen v))) = 2)
    (hv2 : v * v = 1) (hv1 : v ≠ 1) (hxv : x ∈ Cen v) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxv1 : x ≠ v) (hxv2 : x * v * (x * v) = 1) :
    (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen v)) ⟨x, hxv⟩ : HBar (Cen v)) ∉
      center (HBar (Cen v)) := by
  intro hc
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(Cen v))
  have hvC : v ∈ Cen v := mem_centralizer_singleton_iff.mpr rfl
  have hvc : π ⟨v, hvC⟩ ∈ center (HBar (Cen v)) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp g'.2)
  have hv1' : π ⟨v, hvC⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨v, hvC⟩ : ↥(Cen v)) ∈ pPrimeCore 2 ↥(Cen v) := (QuotientGroup.eq_one_iff _).mp h1
    exact not_mem_pPrimeCore_of_involution (Subtype.ext hv2)
      (fun h1' => hv1 (congrArg Subtype.val h1')) hmem
  have hx1' : π ⟨x, hxv⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨x, hxv⟩ : ↥(Cen v)) ∈ pPrimeCore 2 ↥(Cen v) := (QuotientGroup.eq_one_iff _).mp h1
    exact not_mem_pPrimeCore_of_involution (Subtype.ext hx2)
      (fun h1' => hx1 (congrArg Subtype.val h1')) hmem
  have hxz' : π ⟨x, hxv⟩ = π ⟨v, hvC⟩ := by
    by_contra hne
    have h3 : ({1, π ⟨v, hvC⟩, π ⟨x, hxv⟩} : Set (HBar (Cen v))) ⊆
        (center (HBar (Cen v)) : Set (HBar (Cen v))) := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact (center _).one_mem
      · exact hvc
      · exact hc
    have h4 := Set.ncard_le_ncard h3 (Set.toFinite _)
    have h5 : ({1, π ⟨v, hvC⟩, π ⟨x, hxv⟩} : Set (HBar (Cen v))).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨1, _, _, hv1'.symm, hx1'.symm, fun e => hne e.symm, rfl⟩
    have h6 : ((center (HBar (Cen v)) : Set (HBar (Cen v)))).ncard = 2 := by
      rw [← Nat.card_coe_set_eq]; exact hcard
    omega
  have hmem : (⟨x, hxv⟩ * ⟨v, hvC⟩ : ↥(Cen v)) ∈ pPrimeCore 2 ↥(Cen v) := by
    have h1 : π (⟨x, hxv⟩ * ⟨v, hvC⟩) = 1 := by
      rw [map_mul, hxz', ← map_mul]
      have : (⟨v, hvC⟩ * ⟨v, hvC⟩ : ↥(Cen v)) = 1 := Subtype.ext hv2
      rw [this, map_one]
    exact (QuotientGroup.eq_one_iff _).mp h1
  refine not_mem_pPrimeCore_of_involution (Subtype.ext hxv2) ?_ hmem
  intro h1
  apply hxv1
  have h2 : x * v = 1 := congrArg Subtype.val h1
  calc x = x * v * v := by rw [mul_assoc, hv2, mul_one]
    _ = v := by rw [h2, one_mul]

end CFSG.OddStandard.GH71
