module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeLayerFacts
import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizerSplit

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion

variable {G : Type} [Group G]

private theorem sd_quarter_conj_s (n : ℕ) (hn : 4 ≤ n) :
    r n ^ 2 ^ (n - 3) * s n * (r n ^ 2 ^ (n - 3))⁻¹ = z n * s n := by
  have h1 := sd_s_conj_quarter hn
  have hv2 : r n ^ 2 ^ (n - 3) * r n ^ 2 ^ (n - 3) = z n := by
    rw [← pow_add, z, half, ← two_mul, ← pow_succ', show n - 3 + 1 = n - 2 by omega]
  calc r n ^ 2 ^ (n - 3) * s n * (r n ^ 2 ^ (n - 3))⁻¹
      = r n ^ 2 ^ (n - 3) * (s n * r n ^ 2 ^ (n - 3) * (s n)⁻¹)⁻¹ * s n := by group
    _ = r n ^ 2 ^ (n - 3) * r n ^ 2 ^ (n - 3) * s n := by rw [h1, inv_inv]
    _ = z n * s n := by rw [hv2]

private theorem frontierSetting_T_isKleinFour (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    IsKleinFour (frontierSetting S fS t p f).T := by
  rw [frontierSetting_T hn S fS t ht p f]
  exact qdFour_isKleinFour hn _ fS

theorem frontier_exists_D_swap (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    ∃ d ∈ (frontierSetting S fS t p f).D,
      d * (frontierSetting S fS t p f).x * d⁻¹ = (frontierSetting S fS t p f).x ∧
        d * (frontierSetting S fS t p f).x₂ * d⁻¹ =
          (frontierSetting S fS t p f).x * (frontierSetting S fS t p f).x₂ := by
  obtain ⟨hz, -, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have := sdFourSubgroup_isKleinFour hn
  have hιz : FocalFusion.ambientHom n (S : Subgroup G) fS (z n) = t := hz
  have hιs : FocalFusion.ambientHom n (S : Subgroup G) fS (s n) = (fS (s n) : G) := rfl
  have hvz : r n ^ 2 ^ (n - 3) * z n * (r n ^ 2 ^ (n - 3))⁻¹ = z n := by
    rw [Subgroup.mem_center_iff.mp (z_mem_center n hn) _, mul_inv_cancel_right]
  refine ⟨FocalFusion.ambientHom n (S : Subgroup G) fS (r n ^ 2 ^ (n - 3)), ?_, ?_, ?_⟩
  · rw [frontierSetting_D hn S fS t ht p f]
    exact Subgroup.mem_map_of_mem _ (sd_kleinFour_facts hn (sdFourSubgroup n)).2.2.1
  · change _ * t * _ = t
    rw [← hιz, ← map_inv, ← map_mul, ← map_mul, hvz]
  · change _ * (fS (s n) : G) * _ = t * (fS (s n) : G)
    rw [← hιz, ← hιs, ← map_inv, ← map_mul, ← map_mul, sd_quarter_conj_s n hn, map_mul]

theorem frontier_F₀_eq_T (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    (frontierSetting S fS t p f).D ⊓
        Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G) =
      (frontierSetting S fS t p f).T := by
  have hT := frontierSetting_T hn S fS t ht p f
  have := sdFourSubgroup_isKleinFour hn
  have := frontierSetting_T_isKleinFour n hn S fS t ht p f
  apply le_antisymm
  · rintro g ⟨hgD, hgC⟩
    have hgS : g ∈ (S : Subgroup G) := hgD.1
    obtain ⟨a, rfl⟩ := (FocalFusion.ambientHom_range n _ fS).ge hgS
    rw [hT, qdFour] at hgC ⊢
    have ha := (mem_centralizer_map_iff (FocalFusion.ambientHom_injective n _ fS) _ a).mp hgC
    rw [(sd_kleinFour_facts hn (sdFourSubgroup n)).2.1] at ha
    exact Subgroup.mem_map_of_mem _ ha
  · refine le_inf (le_inf ?_ Subgroup.le_normalizer) (Local.kleinFour_le_centralizer _)
    rw [hT]
    exact qdFour_le _ fS

theorem frontier_F₀_sylow [Finite G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    IsSylowOf 2 ((frontierSetting S fS t p f).D ⊓
        Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G))
      (frontierSetting S fS t p f).C := by
  rw [frontier_F₀_eq_T n hn S fS t ht p f]
  have := frontierSetting_T_isKleinFour n hn S fS t ht p f
  obtain ⟨P, hP⟩ := Local.kleinFour_sylow_of_centralizer n hn S fS (frontierSetting S fS t p f).T
  refine ⟨P, ?_⟩
  rw [hP]
  exact Subgroup.map_subgroupOf_eq_of_le (Local.kleinFour_le_centralizer _)

theorem frontier_C_eq [Finite G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    oddCoreIn (frontierSetting S fS t p f).C ⊔ ((frontierSetting S fS t p f).D ⊓
        Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G)) =
      (frontierSetting S fS t p f).C := by
  rw [frontier_F₀_eq_T n hn S fS t ht p f]
  have hK := frontierSetting_T_isKleinFour n hn S fS t ht p f
  obtain ⟨hTC, -, -, N, hNn, ⟨hNodd, -⟩, -, -, -, -, e, he⟩ :=
    Local.semidihedral_four_subgroup_centralizer_split n hn S fS
      (frontierSetting S fS t p f).T hK
  refine le_antisymm (sup_le (oddCoreIn_le _) hTC) fun c hc => ?_
  have hNO : N.map (frontierSetting S fS t p f).C.subtype ≤
      oddCoreIn (frontierSetting S fS t p f).C :=
    Subgroup.map_mono (le_sSup ⟨hNn, hNodd⟩)
  obtain ⟨⟨a, b⟩, hab⟩ := e.surjective ⟨c, hc⟩
  have h : (((a : Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G)) * b :
      Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G)) : G) = c := by
    rw [← he, hab]
  rw [← h, Subgroup.coe_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp a.2))
    (Subgroup.mem_sup_left (hNO ⟨b.1, b.2, rfl⟩))

theorem frontier_C_le [Finite G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    (frontierSetting S fS t p f).C ≤
      oddCoreIn (frontierSetting S fS t p f).C ⊔ (frontierSetting S fS t p f).D :=
  (frontier_C_eq n hn S fS t ht p f).ge.trans (sup_le_sup_left inf_le_left _)

theorem frontier_quaternion_element (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    ∃ y ∈ ((frontierSetting S fS t p f).S : Subgroup G),
      y ∉ centerOf ((frontierSetting S fS t p f).S : Subgroup G) ∧
        ∀ Q : Subgroup G, Q ≤ (frontierSetting S fS t p f).S →
          Nonempty (Q ≃* QuaternionGroup 2) → y ∈ Q := by
  obtain ⟨hz, -, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have := presentation_finite n (by omega)
  have hinj := FocalFusion.ambientHom_injective n (S : Subgroup G) fS
  have hιz : FocalFusion.ambientHom n (S : Subgroup G) fS (z n) = t := hz
  refine ⟨FocalFusion.ambientHom n (S : Subgroup G) fS (r n ^ 2 ^ (n - 3)),
    ambientHom_mem _ fS _, ?_, fun Q hQS hQ => ?_⟩
  · rw [frontierSetting_centerOf_S hn S fS t ht p f, ← hιz, ← MonoidHom.map_zpowers,
      Subgroup.mem_map_iff_mem hinj,
      KleinFourOddKernel.mem_zpowers_involution _ _ (orderOf_z n (by omega))]
    have ho := orderOf_sdV hn
    rintro (h | h) <;> rw [h] at ho
    · rw [orderOf_one] at ho
      omega
    · rw [orderOf_z n (by omega)] at ho
      omega
  · have hQmap := map_comap_ambientHom (S : Subgroup G) fS Q hQS
    obtain ⟨eQ⟩ := hQ
    have e₀ : Q.comap (FocalFusion.ambientHom n (S : Subgroup G) fS) ≃* QuaternionGroup 2 :=
      ((Subgroup.equivMapOfInjective _ _ hinj).trans (MulEquiv.subgroupCongr hQmap)).trans eQ
    obtain ⟨i, -, hi⟩ := Local.eq_closure_of_quaternionEight n hn
      (MulEquiv.refl (SemidihedralGroup n)) (r := r n) (s := s n)
      (z := r n ^ (2 ^ (n - 1) / 2)) rfl rfl rfl _ e₀
    have hv : r n ^ 2 ^ (n - 3) ∈ Q.comap (FocalFusion.ambientHom n (S : Subgroup G) fS) := by
      rw [hi, ← two_pow_div_four hn]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    exact hv

theorem frontier_quaternion_element_of_le (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    ∃ y ∈ ((frontierSetting S fS t p f).S : Subgroup G),
      y ∉ centerOf ((frontierSetting S fS t p f).S : Subgroup G) ∧
        ∀ X : Subgroup G, X ≤ (frontierSetting S fS t p f).S →
          ((frontierSetting S fS t p f).S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
            (∃ Q : Subgroup G, Q ≤ X ∧ Nonempty (Q ≃* QuaternionGroup 2)) → y ∈ X := by
  obtain ⟨y, hyS, hyZ, hy⟩ := frontier_quaternion_element n hn S fS t ht p f
  exact ⟨y, hyS, hyZ, fun X hXS _ ⟨Q, hQX, hQ⟩ => hQX (hy Q (hQX.trans hXS) hQ)⟩

end CFSG.Semidihedral.AllPrime
