module

public import CFSG.Dihedral.OriginalCosetModel
public import CFSG.Dihedral.OriginalCosetSetup
public import CFSG.Dihedral.OriginalCharacterKernelBounds
public import CFSG.Dihedral.FourgroupActionTransport
public import CFSG.Dihedral.GorensteinWalter.ASevenRotationThreeCycle
public import CFSG.Dihedral.GorensteinWalter.ASevenFourgroupFullActionInputs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicOrderThreeAutomorphism

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem r_inverts_R_of_aligned_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) :
    ∀ x : G, x ∈ d.R → d.r * x * d.r⁻¹ = x⁻¹ := by
  have hn := d.n_eq_three_of_aSeven_model e
  have hrN : d.r ∈ d.N := d.centralizer_le_normalizer
    (d.sylow_le_centralizer d.r_mem_sylow)
  let alpha : MulAut d.R := d.R.normalizerMonoidHom ⟨d.r, hrN⟩
  rcases mulAut_eq_one_or_apply_eq_inv_of_card_eq_three
      (d.R_card_of_aSeven_model hR e) alpha with hidentity | hinverts
  · exfalso
    have ha : a7a ∈ d.R.map e.toMonoidHom := by
      rw [d.R_map_eq_a7U hR e ht, a7U_eq_zpowers]
      exact Subgroup.mem_zpowers _
    obtain ⟨x, hx, hex⟩ := Subgroup.mem_map.mp ha
    have hfix : d.r * x * d.r⁻¹ = x := by
      have h := congrArg Subtype.val (DFunLike.congr_fun hidentity (⟨x, hx⟩ : d.R))
      simpa [alpha, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
    have hcomm : e d.r * a7a = a7a * e d.r := by
      have hc : d.r * x = x * d.r := mul_inv_eq_iff_eq_mul.mp hfix
      change e x = a7a at hex
      simpa only [map_mul, hex] using congrArg e hc
    have hr4 : d.r ^ 4 = 1 := by
      simpa [d.order_r, hn] using pow_orderOf_eq_one d.r
    have hr2 : d.r ^ 2 ≠ 1 := by
      intro h
      have hdiv := orderOf_dvd_of_pow_eq_one h
      norm_num [d.order_r, hn] at hdiv
    apply aSeven_order_four_not_centralizes_a7a (e d.r)
      (by simpa only [map_pow, map_one] using congrArg e hr4) _ hcomm
    intro h
    apply hr2
    apply e.injective
    simpa only [map_pow, map_one] using h
  · intro x hx
    exact congrArg Subtype.val (hinverts ⟨x, hx⟩)

theorem exists_original_fourgroup_fixed_of_aligned_aSeven_model (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t) :
    ∃ i : Fin 2, d.E i = d.R := by
  have hsN : d.s ∈ d.N := d.centralizer_le_normalizer
    (d.sylow_le_centralizer d.s_mem_sylow)
  let alpha : MulAut d.R := d.R.normalizerMonoidHom ⟨d.s, hsN⟩
  have hrot := d.r_inverts_R_of_aligned_aSeven_model hR e ht
  rcases mulAut_eq_one_or_apply_eq_inv_of_card_eq_three
      (d.R_card_of_aSeven_model hR e) alpha with hidentity | hinverts
  · refine ⟨0, ?_⟩
    rw [← d.original_reflection_fixed]
    apply inf_eq_left.mpr
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val (DFunLike.congr_fun hidentity (⟨x, hx⟩ : d.R))
    have hfix : d.s * x * d.s⁻¹ = x := by
      simpa [alpha, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
    simpa using (mul_inv_eq_iff_eq_mul.mp hfix).symm
  · refine ⟨1, ?_⟩
    rw [← d.original_reflection_fixed]
    apply inf_eq_left.mpr
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hs : d.s * x * d.s⁻¹ = x⁻¹ := congrArg Subtype.val (hinverts ⟨x, hx⟩)
    have hsxinv : d.s * x⁻¹ * d.s⁻¹ = x := by
      simpa [mul_assoc] using congrArg Inv.inv hs
    have hfix : (d.s * d.r) * x * (d.s * d.r)⁻¹ = x := by
      calc
        (d.s * d.r) * x * (d.s * d.r)⁻¹ =
            d.s * (d.r * x * d.r⁻¹) * d.s⁻¹ := by group
        _ = d.s * x⁻¹ * d.s⁻¹ := by rw [hrot x hx]
        _ = x := hsxinv
    simpa using (mul_inv_eq_iff_eq_mul.mp hfix).symm

theorem cycles_of_fixed_original_fourgroup_of_aligned_aSeven_model
    (hR : d.R ≠ ⊥) (e : G ≃* alternatingGroup (Fin 7)) (ht : e d.t = a7t)
    (i : Fin 2) (hi : d.E i = d.R) : Cycles d.N (d.V i) := by
  apply cycles_normalizer_of_map_equiv e d.R (d.V i)
  rw [d.R_map_eq_a7U hR e ht]
  apply a7U_fourgroup_cycles
  · exact isKleinFour_map_mulEquiv_cross (d.V i) (d.V_isKleinFour_general i) e
  · rw [← d.R_map_eq_a7U hR e ht]
    exact centralizer_map_le_of_mulEquiv e d.R (d.V i)
      (d.fourgroup_le_R_centralizer i hi)

end CFSG.DihedralBlueprint.OriginalData
