module

public import CFSG.CharacterTheory.Semidihedral.Local.LayerCoverParameter
public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage

theorem normal_odd_index_subgroup_preserves_actual_local_layer {G : Type} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (hodd : Odd H.index) (hH : ∀ U : Subgroup H, U.index ≠ 2)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S)
    (t : G) (htH : t ∈ H) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (heven : Even (Nat.card (CFSG.generalizedFitting (Gamma t))))
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥) :
    let B : Subgroup (C t) := H.subgroupOf (C t)
    let R := CFSG.pPrimeCore 2 B
    let Δ := B ⧸ (R ⊔ (Z t).subgroupOf B)
    let L := CFSG.generalizedFitting (Gamma t)
    let J := CFSG.generalizedFitting Δ
    (∃ S' : Sylow 2 G, (S' : Subgroup G) = S.toSubgroup.map H.subtype) ∧
      (∀ U : Subgroup G, U.index ≠ 2) ∧
      (∀ g : G, ∃ h ∈ H, ∃ c ∈ C t, g = h * c) ∧
      B.index = H.index ∧
      R.map B.subtype = B ⊓ N t ∧
      ∃ ι : Δ →* Gamma t, Function.Injective ι ∧
        (∀ b : B, ι (QuotientGroup.mk' (R ⊔ (Z t).subgroupOf B) b) = kappa t b) ∧
        ι.range.Normal ∧ Odd ι.range.index ∧ L ≤ ι.range ∧ J.map ι = L ∧
        IsSimpleGroup J ∧ (∃ a b : J, a * b ≠ b * a) ∧ Even (Nat.card J) ∧
        Subgroup.centralizer (J : Set Δ) = ⊥ ∧
        (∃ e : J ≃* L, ∀ x : J, (e x : Gamma t) = ι x) ∧
        (∀ p f : ℕ, p.Prime → Odd p → 1 ≤ f →
          CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 2 p f →
          CFSG.Assembly.LowTwoRank.StatedClassicalModel J .PSL 2 p f) ∧
        ((∀ U : Sylow 2 L, ¬ IsCyclic U) → ∀ U : Sylow 2 J, ¬ IsCyclic U) := by
  intro B R Δ L J
  have hnot2 : ¬ 2 ∣ H.index := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hSyl : ∃ S' : Sylow 2 G, (S' : Subgroup G) = S.toSubgroup.map H.subtype := by
    refine ⟨Sylow.ofCard _ ?_, Sylow.coe_ofCard _ _⟩
    rw [Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity,
      ← H.card_mul_index, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnot2, add_zero]
  have hG2 : ∀ U : Subgroup G, U.index ≠ 2 := by
    intro U hU
    have hUn : U.Normal := Subgroup.normal_of_index_eq_two hU
    by_cases hHU : H ≤ U
    · have h1 := Subgroup.index_dvd_of_le hHU
      rw [hU] at h1
      exact hnot2 h1
    · have h1 := Subgroup.relIndex_dvd_index_of_normal U H
      rw [hU] at h1
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact hHU (Subgroup.relIndex_eq_one.mp h)
      · exact hH _ h
  have hord : ∀ g : G, orderOf (g * t * g⁻¹) = 2 := fun g => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have hHC : ∀ g : G, ∃ h ∈ H, ∃ c ∈ C t, g = h * c := by
    intro g
    have hgt : g * t * g⁻¹ ∈ H := (inferInstance : H.Normal).conj_mem t htH g
    have h1 := CFSG.Semidihedral.InvolutionFusion.ambient_involution_isConj_z n hn S fS hH
      ⟨t, htH⟩ (by rw [Subgroup.orderOf_mk, ht])
    have h2 := CFSG.Semidihedral.InvolutionFusion.ambient_involution_isConj_z n hn S fS hH
      ⟨g * t * g⁻¹, hgt⟩ (by rw [Subgroup.orderOf_mk, hord g])
    obtain ⟨h, hh⟩ := isConj_iff.mp (h2.trans h1.symm)
    have hh' : (h : G) * (g * t * g⁻¹) * (h : G)⁻¹ = t := congrArg Subtype.val hh
    refine ⟨(h : G)⁻¹, H.inv_mem h.2, (h : G) * g, ?_, by group⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (h : G) * g * t = (h : G) * (g * t * g⁻¹) * (h : G)⁻¹ * ((h : G) * g) := by group
      _ = t * ((h : G) * g) := by rw [hh']
  have hsup : H ⊔ C t = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨h, hh, c, hc, rfl⟩ := hHC g
    exact Subgroup.mul_mem_sup hh hc
  have hindex : B.index = H.index := by
    change H.relIndex (C t) = H.index
    rw [← Subgroup.relIndex_sup_left, hsup, Subgroup.relIndex_top_right]
  have hTn : (B.map (kappa t)).Normal :=
    (inferInstance : B.Normal).map _ (QuotientGroup.mk'_surjective _)
  have hTodd : Odd (B.map (kappa t)).index := by
    have h := Subgroup.index_map_dvd B (QuotientGroup.mk'_surjective (NZ t))
    rw [hindex] at h
    exact Odd.of_dvd_nat hodd h
  have hLn : L.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := Gamma t)).2
  have hLT : L ≤ B.map (kappa t) := by
    have hnorm : ((B.map (kappa t) ⊓ L).subgroupOf L).Normal :=
      (Subgroup.normal_inf_normal _ _).subgroupOf _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((B.map (kappa t) ⊓ L).subgroupOf L)
      with h | h
    · exfalso
      have hbot : B.map (kappa t) ⊓ L = ⊥ :=
        (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_right
      have h1 := Subgroup.relIndex_dvd_index_of_normal (B.map (kappa t)) L
      have h2 := Subgroup.relIndex_mul_card (B.map (kappa t)) L
      rw [hbot, Subgroup.card_bot, mul_one] at h2
      rw [h2] at h1
      exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hTodd h1)) heven
    · exact (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left
  have hcover := centralizer_layer_cover_preserves_actual_local_parameter (C := C t) (tInC t)
    (tInC_central t) (by rw [tInC, Subgroup.orderOf_mk, ht]) hnonab heven hcentral B htH hLT
  obtain ⟨hR, ι, hinj, hι, hrange, hJL, hCJ, ⟨e, he⟩, hmod, hsyl⟩ := hcover
  have hJsimple : IsSimpleGroup J := e.isSimpleGroup
  have hJnc : ∃ a b : J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h1 := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h1
  have hJeven : Even (Nat.card J) := by
    rw [Nat.card_congr e.toEquiv]
    exact heven
  refine ⟨hSyl, hG2, hHC, hindex, hR, ι, hinj, hι, ?_, ?_, ?_, hJL, hJsimple, hJnc, hJeven, hCJ,
    ⟨e, he⟩, hmod, hsyl⟩
  · rw [hrange]
    exact hTn
  · rw [hrange]
    exact hTodd
  · rw [hrange]
    exact hLT

end CFSG.Semidihedral.Local
