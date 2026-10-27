module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeLayerFacts

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion

private theorem sd_s_mul_quarter_facts (n : ℕ) (hn : 4 ≤ n) :
    orderOf (s n * r n ^ 2 ^ (n - 3)) = 2 ∧ s n * r n ^ 2 ^ (n - 3) ≠ z n := by
  have hs2 : s n * s n = 1 := by
    have h := pow_orderOf_eq_one (s n)
    rwa [orderOf_s n (by omega), pow_two] at h
  have hsinv : (s n)⁻¹ = s n := inv_eq_of_mul_eq_one_right hs2
  have hconj := sd_s_conj_quarter hn
  rw [hsinv] at hconj
  have hrot : ∀ y, s n * r n ^ 2 ^ (n - 3) = y → y ∈ rotationSubgroup n →
      False := by
    intro y hy hyR
    apply s_not_mem_rotationSubgroup hn
    have hs : s n = y * (r n ^ 2 ^ (n - 3))⁻¹ := by rw [← hy]; group
    rw [hs]
    exact (rotationSubgroup n).mul_mem hyR
      ((rotationSubgroup n).inv_mem (sdV_mem_rotationSubgroup n))
  refine ⟨orderOf_eq_prime ?_ ?_, fun h => hrot _ h (z_mem_rotationSubgroup n)⟩
  · rw [pow_two]
    calc s n * r n ^ 2 ^ (n - 3) * (s n * r n ^ 2 ^ (n - 3))
        = (s n * r n ^ 2 ^ (n - 3) * s n) * r n ^ 2 ^ (n - 3) := by group
      _ = 1 := by rw [hconj, inv_mul_cancel]
  · intro h
    exact hrot _ h (rotationSubgroup n).one_mem

theorem frontier_h_y {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).height = 1 →
      ∃ y ∈ (frontierSetting S fS t p f).D, y ∉ centerOf (frontierSetting S fS t p f).D ∧
        y ∈ (frontierSetting S fS t p f).L₀ ∧
        ∀ S₁ : Sylow 2 G, (frontierSetting S fS t p f).D ≤ (S₁ : Subgroup G) →
          ∃ c ∈ (S₁ : Subgroup G), y = (frontierSetting S fS t p f).x₂ *
            (c * (frontierSetting S fS t p f).x₂ * c⁻¹) := by
  intro _
  obtain ⟨hz, ht2, -, -, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  set ι := FocalFusion.ambientHom n (S : Subgroup G) fS with hι
  have hinj : Function.Injective ι := FocalFusion.ambientHom_injective n _ fS
  have hιz : ι (z n) = t := hz
  have hιs : ι (s n) = (fS (s n) : G) := rfl
  set v : G := ι (r n ^ 2 ^ (n - 3)) with hv
  have := sdFourSubgroup_isKleinFour hn
  have hvD : v ∈ (frontierSetting S fS t p f).D := by
    rw [frontierSetting_D hn S fS t ht p f]
    exact Subgroup.mem_map_of_mem _ (sd_kleinFour_facts hn (sdFourSubgroup n)).2.2.1
  have hsD : (fS (s n) : G) ∈ (frontierSetting S fS t p f).D := by
    rw [frontierSetting_D hn S fS t ht p f, ← hιs]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.le_normalizer (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
  have hvC : v ∈ C t := frontier_S_le_C hn S fS t ht p f (ambientHom_mem _ fS _)
  have hvL : v ∈ (frontierSetting S fS t p f).L₀ := by
    obtain ⟨F', hfield', hfinite', A', rho', data'⟩ :=
      actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf
        hmodel
    have hx4 : orderOf (⟨v, hvC⟩ : C t) = 4 := by
      rw [Subgroup.orderOf_mk, hv, orderOf_ambientHom, orderOf_sdV hn]
    exact ⟨_, actual_order_four_image_mem_layer n hn S fS hG t ht2 F' A' p f rho' data' _ hx4,
      rfl⟩
  have hv4 : orderOf v = 4 := by rw [hv, orderOf_ambientHom, orderOf_sdV hn]
  have hvZ : v ∉ centerOf (frontierSetting S fS t p f).D := by
    rw [frontierSetting_centerOf_D hn S fS t ht p f,
      KleinFourOddKernel.mem_zpowers_involution t v ht2]
    rintro (h | h)
    · rw [h, orderOf_one] at hv4
      omega
    · rw [h, ht2] at hv4
      omega
  refine ⟨v, hvD, hvZ, hvL, fun S₁ hD => ?_⟩
  change ∃ c ∈ (S₁ : Subgroup G), v = (fS (s n) : G) * (c * (fS (s n) : G) * c⁻¹)
  obtain ⟨hw2, hwz⟩ := sd_s_mul_quarter_facts n hn
  set e : SemidihedralGroup n ≃* (S₁ : Subgroup G) := fS.trans (Sylow.equiv S S₁) with he
  set ι₁ := FocalFusion.ambientHom n (S₁ : Subgroup G) e with hι₁
  have hinj₁ : Function.Injective ι₁ := FocalFusion.ambientHom_injective n _ e
  have hz₁ : ι₁ (z n) = t := frontier_sylow_z_eq hn S fS t ht p f _ e hD
  have hsS₁ : (fS (s n) : G) ∈ (S₁ : Subgroup G) := hD hsD
  have hsvS₁ : (fS (s n) : G) * v ∈ (S₁ : Subgroup G) := hD (Subgroup.mul_mem _ hsD hvD)
  set a : SemidihedralGroup n := e.symm ⟨(fS (s n) : G), hsS₁⟩ with ha
  set b : SemidihedralGroup n := e.symm ⟨(fS (s n) : G) * v, hsvS₁⟩ with hb
  have hιa : ι₁ a = (fS (s n) : G) := by
    change ((e (e.symm ⟨(fS (s n) : G), hsS₁⟩) : (S₁ : Subgroup G)) : G) = _
    rw [MulEquiv.apply_symm_apply]
  have hιb : ι₁ b = (fS (s n) : G) * v := by
    change ((e (e.symm ⟨(fS (s n) : G) * v, hsvS₁⟩) : (S₁ : Subgroup G)) : G) = _
    rw [MulEquiv.apply_symm_apply]
  have hιw : ι (s n * r n ^ 2 ^ (n - 3)) = (fS (s n) : G) * v := by
    rw [map_mul, hιs]
  have ha2 : orderOf a = 2 := by
    rw [← orderOf_injective ι₁ hinj₁ a, hιa, hs2]
  have hb2 : orderOf b = 2 := by
    rw [← orderOf_injective ι₁ hinj₁ b, hιb, ← hιw, orderOf_injective ι hinj, hw2]
  have haz : a ≠ z n := by
    intro h
    apply hst
    rw [← hιa, h, hz₁]
  have hbz : b ≠ z n := by
    intro h
    apply hwz
    apply hinj
    rw [hιw, ← hιb, h, hz₁, hιz]
  have hab : IsConj a b := by
    rcases sd_involution_cases hn a ha2 with h | h
    · exact absurd h haz
    rcases sd_involution_cases hn b hb2 with h' | h'
    · exact absurd h' hbz
    exact h.symm.trans h'
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  refine ⟨ι₁ c, ambientHom_mem _ e c, ?_⟩
  have hc' : ι₁ c * (fS (s n) : G) * (ι₁ c)⁻¹ = (fS (s n) : G) * v := by
    have h := congrArg ι₁ hc
    rwa [map_mul, map_mul, map_inv, hιa, hιb] at h
  have hss : (fS (s n) : G) * (fS (s n) : G) = 1 := by
    have h := pow_orderOf_eq_one (fS (s n) : G)
    rwa [hs2, pow_two] at h
  rw [hc', ← mul_assoc, hss, one_mul]

end CFSG.Semidihedral.AllPrime
