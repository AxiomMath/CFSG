module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCInner

public section

namespace CFSG.GH74.GLS.IVK

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatFactsSp4

section Sp4Inner

variable {F : Type} [Field F]

omit [Field F] in
theorem even_card_center_of_order_two {G : Type*} [Group G] {z : G} (hz : z ∈ center G)
    (hz2 : orderOf z = 2) : Even (Nat.card (center G)) := by
  have h := orderOf_dvd_natCard (⟨z, hz⟩ : center G)
  rw [Subgroup.orderOf_mk, hz2] at h
  exact even_iff_two_dvd.2 h

theorem even_card_center_E1 (h2 : (2 : F) ≠ 0) : Even (Nat.card (center (E1 F))) := by
  have hz : (⟨u1 F, u1_mem_E1⟩ : E1 F) ∈ center (E1 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := mem_centralizer_singleton_iff.1 (E1_le_centralizer_u1 h2 g.2)
    exact Subtype.ext this
  refine even_card_center_of_order_two hz ?_
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)

omit [Field F] in
theorem E2_le_centralizer_u1' [Field F] (h2 : (2 : F) ≠ 0) : E2 F ≤ centralizer {u1 F} := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := E2_le_map_E1 hz
  rw [mem_centralizer_singleton_iff]
  have hx1 : x * u1 F = u1 F * x := (mem_centralizer_singleton_iff.1 (E1_le_centralizer_u1 h2 hx))
  have hu : u2 F * u1 F = u1 F * u2 F := u2_mul_u1
  have hu' : (u2 F)⁻¹ * u1 F = u1 F * (u2 F)⁻¹ := by
    calc (u2 F)⁻¹ * u1 F = (u2 F)⁻¹ * (u1 F * u2 F) * (u2 F)⁻¹ := by group
      _ = (u2 F)⁻¹ * (u2 F * u1 F) * (u2 F)⁻¹ := by rw [hu]
      _ = u1 F * (u2 F)⁻¹ := by group
  change u2 F * x * (u2 F)⁻¹ * u1 F = u1 F * (u2 F * x * (u2 F)⁻¹)
  calc u2 F * x * (u2 F)⁻¹ * u1 F = u2 F * x * (u1 F * (u2 F)⁻¹) := by rw [mul_assoc, hu']
    _ = u2 F * (x * u1 F) * (u2 F)⁻¹ := by group
    _ = u2 F * (u1 F * x) * (u2 F)⁻¹ := by rw [hx1]
    _ = (u2 F * u1 F) * x * (u2 F)⁻¹ := by group
    _ = (u1 F * u2 F) * x * (u2 F)⁻¹ := by rw [hu]
    _ = u1 F * (u2 F * x * (u2 F)⁻¹) := by group

theorem even_card_center_E2 (h2 : (2 : F) ≠ 0) : Even (Nat.card (center (E2 F))) := by
  have hz : (⟨u1 F, u1_mem_E2⟩ : E2 F) ∈ center (E2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := mem_centralizer_singleton_iff.1 (E2_le_centralizer_u1' h2 g.2)
    exact Subtype.ext this
  refine even_card_center_of_order_two hz ?_
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)

variable [Finite F]

theorem psp4_inner_false (hodd : Odd (Nat.card F)) {W : Type} [Group W]
    (ψ : W ≃* StatedProj (StatedSp 2 F)) {K₀ : Subgroup W}
    (hZ : Odd (Nat.card (center K₀)))
    (hterm : ∀ w : W, orderOf w = 2 → w ∈ centralizer (K₀ : Set W) →
      K₀ ≤ centralizer {w} ∧ CFSG.IsPComponent 2 (K₀.subgroupOf (centralizer {w})))
    {v : W} (hv : orderOf v = 2) (hvK : v ∈ centralizer (K₀ : Set W)) : False := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have key : ∀ (φ : W ≃* StatedProj (StatedSp 2 F)) (w : W), orderOf w = 2 →
      w ∈ centralizer (K₀ : Set W) → φ w = u1 F → False := by
    intro φ w hw hwK hφ
    obtain ⟨hle, hcomp⟩ := hterm w hw hwK
    have hmap := isPComponent_map_subgroupOf 2 φ hle hcomp
    have hC : (centralizer {w}).map φ.toMonoidHom = centralizer {u1 F} := by
      rw [map_centralizer_singleton, hφ]
    rw [hC] at hmap
    have hMX : K₀.map φ.toMonoidHom ≤ centralizer {u1 F} := by
      rw [← hC]
      exact Subgroup.map_mono hle
    obtain ⟨hE, -⟩ := pComponent_centralizer_u1 hodd hMX hmap
    have hev : Even (Nat.card (center (K₀.map φ.toMonoidHom))) := by
      rcases hE with hE | hE
      · rw [hE]
        exact even_card_center_E1 h2
      · rw [hE]
        exact even_card_center_E2 h2
    have hcard : Nat.card (center K₀) = Nat.card (center (K₀.map φ.toMonoidHom)) := by
      let e : K₀ ≃* K₀.map φ.toMonoidHom := K₀.equivMapOfInjective φ.toMonoidHom φ.injective
      have h1 := Subgroup.map_center_eq e
      rw [← h1]
      exact (Subgroup.card_map_of_injective e.injective).symm
    rw [hcard] at hZ
    exact (Nat.not_even_iff_odd.2 hZ) hev
  have hvu : orderOf (ψ v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
  obtain ⟨φ, hφ⟩ := exists_model_conj hodd hvu
  rcases hφ with h | h
  · exact key (ψ.trans φ) v hv hvK h
  · obtain ⟨hle, hcomp⟩ := hterm v hv hvK
    have hmap := isPComponent_map_subgroupOf 2 (ψ.trans φ) hle hcomp
    have hC : (centralizer {v}).map (ψ.trans φ).toMonoidHom = centralizer {u2 F} := by
      rw [map_centralizer_singleton]
      exact congrArg _ (congrArg _ h)
    rw [hC] at hmap
    have hMX : K₀.map (ψ.trans φ).toMonoidHom ≤ centralizer {u2 F} := by
      rw [← hC]
      exact Subgroup.map_mono hle
    obtain ⟨hL, -⟩ := pComponent_centralizer_u2 hodd hMX hmap
    refine key (ψ.trans φ) ((ψ.trans φ).symm (u1 F)) ?_ ?_ ((ψ.trans φ).apply_symm_apply _)
    · rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hkL : (ψ.trans φ) k ∈ Lsub F := by
        rw [← hL]
        exact ⟨k, hk, rfl⟩
      have := u1_commute_Lsub hkL
      apply (ψ.trans φ).injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact this.symm

end Sp4Inner

end CFSG.GH74.GLS.IVK
