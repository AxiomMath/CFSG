module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFieldAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK3Cover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4Cover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2Cover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem ff6m_classify :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      s ∈ centralizer (L : Set G) ∨ InducesTypeSome L s 6 (-1) 4 1 ∨
        InducesTypeSome L s 6 (-1) 4 (-1) ∨ InducesProjective L 6 (-1) s ∨
        (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α) ∨ (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) ∨
        InducesOutsideGStar L 6 (-1) s := by
  intro G _ _ L hL s hs2 hsn
  obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx2⟩ := ff6m_model_data hL hs2 hsn
  rcases ff6m_model_classify hQ hdim hsgn hx2 with h1 | h0 | hn1 | h2 | h3 | hn2 | h4
  · exact Or.inl ((ff6m_centralizer_iff_eq_one hL.1 hQ (by omega) e hs).mpr h1)
  · exact Or.inr (Or.inl ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim,
      hsgn, hs, h0⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x,
      hdim, hsgn, hs, hn1⟩))
  · obtain ⟨α, hα⟩ := h2
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨α, V, inferInstance, inferInstance,
      inferInstance, Q, hQ, e, x, hdim, hsgn, hs, hα⟩))))
  · obtain ⟨α, hα⟩ := h3
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨α, V, inferInstance, inferInstance,
      inferInstance, Q, hQ, e, x, hdim, hsgn, hs, hα⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ,
      e, x, hdim, hsgn, hs, hn2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨V, inferInstance, inferInstance,
      inferInstance, Q, hQ, e, x, hdim, hsgn, hs, hx2, h4⟩)))))

theorem ff6m_nontrivial :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (InducesTypeSome L s 6 (-1) 4 1 ∨ InducesTypeSome L s 6 (-1) 4 (-1) ∨
        InducesProjective L 6 (-1) s ∨ (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 1 α) ∨
        (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) ∨ InducesOutsideGStar L 6 (-1) s) →
        s ∉ centralizer (L : Set G) := by
  intro G _ _ L hL s hs2 hsn h
  rcases h with ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩ |
      ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩ |
      ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩ |
      ⟨α, V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩ |
      ⟨α, V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩ |
      ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx2, hx⟩
  · exact ff6m_not_centralizer hL hdim hs (simHasType_ne_one hx)
  · exact ff6m_not_centralizer hL hdim hs (simHasType_ne_one hx)
  · exact ff6m_not_centralizer hL hdim hs (ff6m_KN2_ne_one hx)
  · exact ff6m_not_centralizer hL hdim hs (simHasType_ne_one hx)
  · exact ff6m_not_centralizer hL hdim hs (simHasType_ne_one hx)
  · refine ff6m_not_centralizer hL hdim hs (fun h1 => hx ?_)
    rw [h1]
    exact ⟨1, map_one _⟩

theorem ff6m_inner_iff :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ((InnerOn L s ∧ s ∉ centralizer (L : Set G)) ↔ InducesTypeSome L s 6 (-1) 4 1) := by
  intro G _ _ L hL s hs2 hsn
  constructor
  · rintro ⟨hin, hnc⟩
    obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx2⟩ := ff6m_model_data hL hs2 hsn
    have hxne : x ≠ 1 := fun h1 =>
      hnc ((ff6m_centralizer_iff_eq_one hL.1 hQ (by omega) e hs).mpr h1)
    obtain ⟨y, hy, hyx⟩ := (ff6m_innerOn_iff hL.1 hQ (by omega) e hs).mp hin
    have hu : (⟨y, hy⟩ : ↥(omegaProj hQ)) * ⟨y, hy⟩ = 1 := by
      apply Subtype.ext
      apply projOrthToProjSim_injective (Q := Q)
      rw [Subgroup.coe_mul, map_mul, hyx, hx2, Subgroup.coe_one, map_one]
    have hu1 : (⟨y, hy⟩ : ↥(omegaProj hQ)) ≠ 1 := by
      intro h1
      apply hxne
      rw [← hyx]
      have h2 : y = 1 := congrArg Subtype.val h1
      rw [h2, map_one]
    have hk := ff6m_involution_kind hQ hdim hsgn hu hu1
    rw [show ((⟨y, hy⟩ : ↥(omegaProj hQ)) : ProjOrth Q) = y from rfl, hyx] at hk
    exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, x, hdim, hsgn, hs, hk⟩
  · rintro ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx⟩
    exact ⟨(ff6m_innerOn_iff hL.1 hQ (by omega) e hs).mpr (ff6m_KM0_inner hQ hx),
      ff6m_not_centralizer hL hdim hs (simHasType_ne_one hx)⟩

theorem ff6m_inv_one_class :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ u u' : G, u ∈ L → u' ∈ L → orderOf u = 2 → orderOf u' = 2 → u' ∈ conjClassIn L u := by
  intro G _ _ L hL u u' hu hu' hu2 hu2'
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff6m_exists_model hL
  have hodd := ff6m_odd_center hL
  obtain ⟨h2, h1⟩ := ff6m_phi_involution hQ e hodd hu hu2
  obtain ⟨h2', h1'⟩ := ff6m_phi_involution hQ e hodd hu' hu2'
  obtain ⟨a, ha⟩ := ff6m_conj_involutions hQ hdim hsgn h2 h2' h1 h1'
  exact (ff6m_mem_conjClass_iff hQ e hodd hu hu' (ff6m_sq_of_orderOf_eq_two hu2)
    (ff6m_sq_of_orderOf_eq_two hu2')).mpr ⟨a, ha⟩

theorem ff6m_ex_u_outer :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → ¬ InnerOn L s →
      ∃ u ∈ twoRes (L ⊓ centralizer ({s} : Set G)), orderOf u = 2 ∧ s * u ∈ conjClassIn L s := by
  intro G _ _ L hL s hs2 hsn hnin
  obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hx2⟩ := ff6m_model_data hL hs2 hsn
  have hodd := ff6m_odd_center hL
  have hss := ff6m_sq_of_orderOf_eq_two hs2
  have hxout : ¬ SimInOmegaStar hQ x := fun h =>
    hnin ((ff6m_innerOn_iff hL.1 hQ (by omega) e hs).mpr h)
  refine ff6m_ex_u_of_cover hQ (by omega) e hodd hs hss ?_
  rcases ff6m_model_classify hQ hdim hsgn hx2 with h1 | h0 | hn1 | h2 | h3 | hn2 | h4
  · exact absurd ⟨1, (omegaProj hQ).one_mem, by rw [h1, map_one]⟩ hxout
  · exact absurd (ff6m_KM0_inner hQ h0) hxout
  · exact ff6m_N1_cover hQ hdim hsgn hn1
  · exact ff6m_K2_cover hQ hdim hsgn h2
  · exact ff6m_K3_cover hQ hdim hsgn h3
  · exact ff6m_N2_cover hQ hdim hsgn hn2
  · exact ff6m_K4_cover hQ hdim hsgn hx2 h4

end CFSG.OddStandard.SmallF3.Omega
