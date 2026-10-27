module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingDihedral
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingDefs

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G] {H : Subgroup G} {z : G}

theorem product_smul_eq_iff (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (h1 : ProductUniqueContainment H z) {s t : G}
    (hs : s ∈ involutionPointClass z) (ht : t ∈ involutionPointClass z)
    (hst : Commute s t) (hne : t ≠ s) (ω : G ⧸ H) :
    (s * t) • ω = ω ↔ s • ω = ω := by
  obtain ⟨g, rfl⟩ := hs
  change (g⁻¹ * z * g * t) • ω = ω ↔ (g⁻¹ * z * g) • ω = ω
  change Commute (g⁻¹ * z * g) t at hst
  change t ≠ g⁻¹ * z * g at hne
  have ht' : g * t * g⁻¹ ∈ involutionPointClass z := by
    simpa only [inv_inv] using class_conj_mem ht g⁻¹
  have hzt' : Commute z (g * t * g⁻¹) := by
    have h := hst.map (MulAut.conj g).toMonoidHom
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel, mul_one] using h
  have hne' : g * t * g⁻¹ ≠ z := by
    intro heq
    apply hne
    rw [← heq]
    group
  have hprod : g⁻¹ * z * g * t = g⁻¹ * (z * (g * t * g⁻¹)) * g := by group
  have hfix : ∀ ω' : G ⧸ H, (z * (g * t * g⁻¹)) • ω' = ω' ↔ ω' = QuotientGroup.mk 1 := by
    intro ω'
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective ω'
    rw [smul_mk_eq_mk_iff, h1 _ ht' hzt' hne' k, mk_eq_base_iff]
  rw [hprod, conj_smul_eq_iff, hfix, conj_smul_eq_iff, smul_eq_iff_eq_base huniq]

theorem commuting_smul_eq_iff (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (h1 : ProductUniqueContainment H z) {s t : G}
    (hs : s ∈ involutionPointClass z) (ht : t ∈ involutionPointClass z)
    (hst : Commute s t) (hne : t ≠ s) (ω : G ⧸ H) :
    s • ω = ω ↔ t • ω = ω := by
  rw [← product_smul_eq_iff huniq h1 hs ht hst hne, hst.eq,
    product_smul_eq_iff huniq h1 ht hs hst.symm hne.symm]

theorem odd_product_of_fixes_ne [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (h1 : ProductUniqueContainment H z) {s t : G}
    (hs : s ∈ involutionPointClass z) (ht : t ∈ involutionPointClass z)
    {ω : G ⧸ H} (hsω : s • ω = ω) (htω : t • ω ≠ ω) :
    Odd (orderOf (s * t)) := by
  by_contra hodd
  obtain ⟨c, hc, -, hsc, htc, hcs, hct⟩ :=
    even_product_central hz hs ht (Nat.not_odd_iff_even.mp hodd)
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc
    exact absurd hc (by decide)
  have hcs_ne : c * s ≠ s := fun h => hc1 (mul_eq_right.mp h)
  have hct_ne : c * t ≠ t := fun h => hc1 (mul_eq_right.mp h)
  have hsc' : Commute s (c * s) := hsc.mul_right (Commute.refl s)
  have htc' : Commute t (c * t) := htc.mul_right (Commute.refl t)
  have hss := class_mul_self hz hs
  have htt := class_mul_self hz ht
  have hcs_eq : s * (c * s) = c := by rw [← mul_assoc, hsc.eq, mul_assoc, hss, mul_one]
  have hct_eq : t * (c * t) = c := by rw [← mul_assoc, htc.eq, mul_assoc, htt, mul_one]
  have hcfix : c • ω = ω := by
    rw [← hcs_eq, product_smul_eq_iff huniq h1 hs hcs hsc' hcs_ne]
    exact hsω
  apply htω
  rw [← product_smul_eq_iff huniq h1 ht hct htc' hct_ne, hct_eq]
  exact hcfix

theorem conj_in_join_of_fixes_ne [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (h1 : ProductUniqueContainment H z) {s t : G}
    (hs : s ∈ involutionPointClass z) (ht : t ∈ involutionPointClass z)
    {ω : G ⧸ H} (hsω : s • ω = ω) (htω : t • ω ≠ ω) :
    ∃ g ∈ Subgroup.closure ({s, t} : Set G), t = g⁻¹ * s * g := by
  obtain ⟨g, hg, hgt⟩ := odd_product_conj hz hs ht (odd_product_of_fixes_ne hz huniq h1 hs ht
    hsω htω)
  refine ⟨g, ?_, hgt⟩
  have hst : s * t ∈ Subgroup.closure ({s, t} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  exact (Subgroup.zpowers_le.mpr hst) hg

end CFSG.ComponentClassification.AschbacherStrongEmbedding
