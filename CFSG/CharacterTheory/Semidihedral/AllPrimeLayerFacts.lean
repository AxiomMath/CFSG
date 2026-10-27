module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeSetting
public import CFSG.LocalAnalysis.ABGTheoremB.Facts
public import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI
public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralAutomizers
public import CFSG.GroupTheory.ABGLocalTools.Criteria

public noncomputable section

namespace CFSG.Semidihedral.AllPrime

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups
open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped commutatorElement Pointwise

section Model

variable {n : ℕ}

theorem sd_closure_rs_s (hn : 3 ≤ n) :
    Subgroup.closure {r n * s n, s n} = (⊤ : Subgroup (SemidihedralGroup n)) := by
  rw [eq_top_iff, ← CentralQuotients.original_generators_closure n hn, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · have hmem : r n * s n * (s n)⁻¹ ∈ Subgroup.closure {r n * s n, s n} :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    rwa [mul_inv_cancel_right] at hmem
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem sd_s_conj_quarter (hn : 4 ≤ n) :
    s n * r n ^ 2 ^ (n - 3) * (s n)⁻¹ = (r n ^ 2 ^ (n - 3))⁻¹ := by
  have hn3 : 3 ≤ n := by omega
  rw [s_eq_element n hn3, r_pow_eq_element n hn3, conjugate_rotation_by_reflection,
    element_rotation_inv, Local.twist_mul_quarter hn]

theorem sd_quarter_ne_inv (hn : 4 ≤ n) : r n ^ 2 ^ (n - 3) ≠ (r n ^ 2 ^ (n - 3))⁻¹ := by
  intro h
  have h2 : (r n ^ 2 ^ (n - 3)) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h]
    exact mul_inv_cancel _
  have hd := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_sdV hn] at hd
  norm_num at hd

theorem sd_central_mul_s_not_comm (hn : 4 ≤ n) {c : SemidihedralGroup n}
    (hc : c ∈ Subgroup.center (SemidihedralGroup n)) :
    c * s n * r n ^ 2 ^ (n - 3) ≠ r n ^ 2 ^ (n - 3) * (c * s n) := by
  intro h
  apply sd_quarter_ne_inv hn
  have hconj : c * s n * r n ^ 2 ^ (n - 3) * (c * s n)⁻¹ = r n ^ 2 ^ (n - 3) := by
    rw [h, mul_inv_cancel_right]
  have hcomm := Subgroup.mem_center_iff.mp hc (s n * r n ^ 2 ^ (n - 3) * (s n)⁻¹)
  have hinv : c * s n * r n ^ 2 ^ (n - 3) * (c * s n)⁻¹ = (r n ^ 2 ^ (n - 3))⁻¹ := by
    rw [← sd_s_conj_quarter hn]
    calc c * s n * r n ^ 2 ^ (n - 3) * (c * s n)⁻¹
        = (c * (s n * r n ^ 2 ^ (n - 3) * (s n)⁻¹)) * c⁻¹ := by group
      _ = s n * r n ^ 2 ^ (n - 3) * (s n)⁻¹ := by rw [← hcomm, mul_inv_cancel_right]
  exact hconj.symm.trans hinv

theorem sd_kleinFour_facts (hn : 4 ≤ n) (V : Subgroup (SemidihedralGroup n)) [IsKleinFour V] :
    z n ∈ V ∧ Subgroup.centralizer (V : Set (SemidihedralGroup n)) = V ∧
      r n ^ 2 ^ (n - 3) ∈ Subgroup.normalizer (V : Set (SemidihedralGroup n)) ∧
      Nat.card (Subgroup.normalizer (V : Set (SemidihedralGroup n))) = 8 := by
  obtain ⟨-, h2, -⟩ := Local.semidihedral_four_subgroup_centralizers n hn
    (MulEquiv.refl (SemidihedralGroup n))
  have hz : (MulEquiv.refl (SemidihedralGroup n)) (r n) ^ (2 ^ (n - 1) / 2) = z n := by
    rw [MulEquiv.refl_apply, two_pow_div_two hn]
    rfl
  have hv : (MulEquiv.refl (SemidihedralGroup n)) (r n) ^ (2 ^ (n - 1) / 4) =
      r n ^ 2 ^ (n - 3) := by
    rw [MulEquiv.refl_apply, two_pow_div_four hn]
  obtain ⟨hzV, hC, hN⟩ := h2 V inferInstance
  obtain ⟨x, hxV, hxz⟩ := Local.kleinFour_exists_not_mem hn (MulEquiv.refl _) V
  obtain ⟨hNeq, -, hcard⟩ := hN x hxV hxz
  refine ⟨hz ▸ hzV, hC, ?_, hcard⟩
  rw [hNeq, ← hv]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem sd_centerOf_normalizer_four (hn : 4 ≤ n) :
    centerOf (Subgroup.normalizer (sdFourSubgroup n : Set (SemidihedralGroup n))) =
      Subgroup.zpowers (z n) := by
  have := sdFourSubgroup_isKleinFour hn
  have := presentation_finite n (by omega)
  obtain ⟨hzV, hC, hvN, -⟩ := sd_kleinFour_facts hn (sdFourSubgroup n)
  have hzc := z_mem_center n hn
  apply le_antisymm
  · rintro g ⟨-, hgC⟩
    have hgV : g ∈ sdFourSubgroup n := by
      rw [← hC]
      exact Subgroup.centralizer_le (fun x hx => Subgroup.le_normalizer hx) hgC
    have hgv := Subgroup.mem_centralizer_iff.mp hgC _ hvN
    rw [sdFourSubgroup, Local.closure_pair_eq_sup] at hgV
    change g ∈ KleinFourOddKernel.fourSubgroup (z n) (s n) at hgV
    rw [KleinFourOddKernel.mem_fourSubgroup _ _ _ hzc (orderOf_z n (by omega))
      (orderOf_s n (by omega))] at hgV
    rcases hgV with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · exact absurd hgv.symm (sd_central_mul_s_not_comm hn (Subgroup.one_mem _))
    · exact absurd hgv.symm (sd_central_mul_s_not_comm hn hzc)
  · rw [Subgroup.zpowers_le]
    exact ⟨Subgroup.le_normalizer hzV, Subgroup.center_le_centralizer _ hzc⟩

theorem sd_quarter_mem_of_normal (hn : 4 ≤ n) (X : Subgroup (SemidihedralGroup n))
    (hX : X.Normal) (hXz : ¬ X ≤ Subgroup.zpowers (z n)) : r n ^ 2 ^ (n - 3) ∈ X := by
  have hn3 : 3 ≤ n := by omega
  have := presentation_finite n hn3
  obtain ⟨i, hiX, hiz⟩ : ∃ i : ZMod (modulus n), element n hn3 i 0 ∈ X ∧
      element n hn3 i 0 ∉ Subgroup.zpowers (z n) := by
    obtain ⟨x, hxX, hxz⟩ := Set.not_subset.mp hXz
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn3).symm.surjective x
    change element n hn3 i e ∈ X at hxX
    change element n hn3 i e ∉ Subgroup.zpowers (z n) at hxz
    rcases exponent_cases e with rfl | rfl
    · exact ⟨i, hxX, hxz⟩
    · refine ⟨1 - twist n, ?_, ?_⟩
      · have hc := hX.conj_mem _ hxX (element n hn3 1 0)
        rw [conjugate_reflection_by_rotation, mul_one] at hc
        have heq : element n hn3 (1 - twist n) 0 =
            element n hn3 (i + (1 - twist n)) 1 * (element n hn3 i 1)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq, element_rotation_mul, add_comm]
        rw [heq]
        exact X.mul_mem hc (X.inv_mem hxX)
      · rw [KleinFourOddKernel.mem_zpowers_involution _ _ (orderOf_z n hn3), z_eq_element n hn3,
          element_eq_one_iff, element_eq_iff]
        intro h
        have h4 : (4 : ZMod (modulus n)) * 1 = 0 := by
          refine (Local.one_sub_twist_mul_mem_iff hn 1).mp ?_
          rw [mul_one]
          rcases h with ⟨h, -⟩ | ⟨h, -⟩
          · exact Or.inl h
          · exact Or.inr h
        rw [mul_one, show (4 : ZMod (modulus n)) = ((4 : ℕ) : ZMod (modulus n)) by norm_cast,
          ZMod.natCast_eq_zero_iff] at h4
        have hle := Nat.le_of_dvd (by norm_num) h4
        have h8 : 2 ^ 3 ≤ modulus n := by
          rw [modulus]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
  have hord : orderOf (element n hn3 i 0) ∣ 2 ^ n := by
    rw [← CFSG.Semidihedral.card n hn3]
    exact orderOf_dvd_natCard _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · rw [pow_zero, orderOf_eq_one_iff] at hk'
      exact hiz (hk' ▸ Subgroup.one_mem _)
    · rw [pow_one, rotation_involution_iff] at hk'
      exact hiz (by rw [hk', ← z_eq_element n hn3]; exact Subgroup.mem_zpowers _)
  have hyX : element n hn3 i 0 ^ 2 ^ (k - 2) ∈ X := X.pow_mem hiX _
  have hy4 : orderOf (element n hn3 i 0 ^ 2 ^ (k - 2)) = 4 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hk']; exact pow_dvd_pow 2 (by omega)), hk',
      Nat.pow_div (by omega) (by norm_num), show k - (k - 2) = 2 by omega]
  have hyr : element n hn3 i 0 ^ 2 ^ (k - 2) ∈ rotationSubgroup n :=
    Subgroup.pow_mem _ ((element_mem_rotationSubgroup_iff n hn3 i 0).mpr rfl) _
  rcases sd_rotation_orderFour hn _ hyr hy4 with h | h
  · rwa [h] at hyX
  · rw [h] at hyX
    simpa using X.inv_mem hyX

theorem sd_normal_le_zpowers_z (hn : 4 ≤ n) (X V : Subgroup (SemidihedralGroup n))
    (hX : X.Normal) [IsKleinFour V]
    (h : X ⊓ Subgroup.normalizer (V : Set (SemidihedralGroup n)) ≤ Subgroup.zpowers (z n)) :
    X ≤ Subgroup.zpowers (z n) := by
  by_contra hXz
  have hv := sd_quarter_mem_of_normal hn X hX hXz
  have hvz := h ⟨hv, (sd_kleinFour_facts hn V).2.2.1⟩
  have := presentation_finite n (by omega)
  have ho := orderOf_sdV hn
  rw [KleinFourOddKernel.mem_zpowers_involution _ _ (orderOf_z n (by omega))] at hvz
  rcases hvz with h1 | h1
  · rw [h1, orderOf_one] at ho
    omega
  · rw [h1, orderOf_z n (by omega)] at ho
    omega

end Model

section Transport

variable {A G : Type*} [Group A] [Group G]

theorem mem_centralizer_map_iff {ι : A →* G} (hι : Function.Injective ι) (P : Subgroup A)
    (a : A) : ι a ∈ Subgroup.centralizer ((P.map ι : Subgroup G) : Set G) ↔
      a ∈ Subgroup.centralizer (P : Set A) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · intro h b hb
    exact hι (by simpa only [map_mul] using h (ι b) ⟨b, hb, rfl⟩)
  · rintro h _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h b hb]

theorem centerOf_map_of_injective {ι : A →* G} (hι : Function.Injective ι) (P : Subgroup A) :
    centerOf (P.map ι) = (centerOf P).map ι := by
  ext g
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hc⟩
    exact ⟨a, ⟨ha, (mem_centralizer_map_iff hι P a).mp hc⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hc⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, (mem_centralizer_map_iff hι P a).mpr hc⟩

theorem range_inf_normalizer_map {ι : A →* G} (hι : Function.Injective ι) (P : Subgroup A) :
    ι.range ⊓ Subgroup.normalizer ((P.map ι : Subgroup G) : Set G) =
      (Subgroup.normalizer (P : Set A)).map ι := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (f := ι) (H := P.map ι)
    (Subgroup.map_le_range ι P)
  rw [Subgroup.comap_map_eq_self_of_injective hι] at h
  rw [← h, Subgroup.map_comap_eq]

theorem centerOf_eq_zpowers_of_model {n : ℕ} (hn : 4 ≤ n) (P : Subgroup G)
    (f : SemidihedralGroup n ≃* P) :
    centerOf P = Subgroup.zpowers (FocalFusion.ambientHom n P f (z n)) := by
  have hP : P = (⊤ : Subgroup (SemidihedralGroup n)).map (FocalFusion.ambientHom n P f) := by
    rw [← MonoidHom.range_eq_map, FocalFusion.ambientHom_range]
  have htop : centerOf (⊤ : Subgroup (SemidihedralGroup n)) = Subgroup.center _ := by
    rw [centerOf, Subgroup.coe_top, Subgroup.centralizer_univ, top_inf_eq]
  have hc := congrArg centerOf hP
  rw [hc, centerOf_map_of_injective (FocalFusion.ambientHom_injective n P f), htop,
    center_eq_zpowers n hn, MonoidHom.map_zpowers]

theorem map_center_subtype (P : Subgroup G) :
    (Subgroup.center P).map P.subtype = centerOf P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, hg⟩)
  · rintro ⟨hxP, hxC⟩
    refine ⟨⟨x, hxP⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hxC g g.2

end Transport

section Sylow

variable {G : Type} [Group G]

theorem frontierSetting_T {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    (frontierSetting S fS t p f).T = qdFour (S : Subgroup G) fS := by
  obtain ⟨hz, -, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  rw [qdFour, sdFourSubgroup, MonoidHom.map_closure, Set.image_pair]
  change Subgroup.closure {t, (fS (s n) : G)} =
    Subgroup.closure {(fS (z n) : G), (fS (s n) : G)}
  rw [hz]

theorem frontierSetting_D {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    (frontierSetting S fS t p f).D =
      (Subgroup.normalizer (sdFourSubgroup n : Set (SemidihedralGroup n))).map
        (FocalFusion.ambientHom n (S : Subgroup G) fS) := by
  have hT := frontierSetting_T hn S fS t ht p f
  rw [qdFour] at hT
  rw [← range_inf_normalizer_map (FocalFusion.ambientHom_injective n _ fS),
    FocalFusion.ambientHom_range, ← hT]
  rfl

theorem frontierSetting_centerOf_S {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    centerOf ((frontierSetting S fS t p f).S : Subgroup G) = Subgroup.zpowers t := by
  obtain ⟨hz, -, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  rw [show ((frontierSetting S fS t p f).S : Subgroup G) = S from rfl,
    centerOf_eq_zpowers_of_model hn _ fS]
  exact congrArg Subgroup.zpowers hz

theorem frontier_S_le_C {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) : (S : Subgroup G) ≤ C t := by
  have h : t ∈ centerOf ((frontierSetting S fS t p f).S : Subgroup G) := by
    rw [frontierSetting_centerOf_S hn S fS t ht p f]
    exact Subgroup.mem_zpowers t
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h.2 g hg)

theorem frontierSetting_centerOf_D {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) :
    centerOf (frontierSetting S fS t p f).D = Subgroup.zpowers t := by
  obtain ⟨hz, -, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  rw [frontierSetting_D hn S fS t ht p f,
    centerOf_map_of_injective (FocalFusion.ambientHom_injective n _ fS),
    sd_centerOf_normalizer_four hn, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers hz

theorem frontier_sylow_z_eq [Finite G] {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (p f : ℕ) (S₁ : Subgroup G)
    (f₁ : SemidihedralGroup n ≃* S₁) (hD : (frontierSetting S fS t p f).D ≤ S₁) :
    FocalFusion.ambientHom n S₁ f₁ (z n) = t := by
  obtain ⟨-, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hinj := FocalFusion.ambientHom_injective n S₁ f₁
  have hrange := FocalFusion.ambientHom_range n S₁ f₁
  have hTD : (frontierSetting S fS t p f).T ≤ (frontierSetting S fS t p f).D :=
    le_inf (by rw [frontierSetting_T hn S fS t ht p f]; exact qdFour_le _ fS)
      Subgroup.le_normalizer
  have hTS₁ : (frontierSetting S fS t p f).T ≤ (FocalFusion.ambientHom n S₁ f₁).range :=
    hTD.trans (hD.trans hrange.ge)
  have hTmap := Subgroup.map_comap_eq_self hTS₁
  have hK : IsKleinFour (frontierSetting S fS t p f).T := by
    rw [frontierSetting_T hn S fS t ht p f]
    exact qdFour_isKleinFour hn _ fS
  have : IsKleinFour ((frontierSetting S fS t p f).T.comap (FocalFusion.ambientHom n S₁ f₁)) :=
    Local.isKleinFour_of_mulEquiv
      ((((frontierSetting S fS t p f).T.comap (FocalFusion.ambientHom n S₁ f₁)).equivMapOfInjective
        _ hinj).trans (MulEquiv.subgroupCongr hTmap)).symm
  have hzT : FocalFusion.ambientHom n S₁ f₁ (z n) ∈ (frontierSetting S fS t p f).T :=
    Subgroup.mem_comap.mp (sd_kleinFour_facts hn
      ((frontierSetting S fS t p f).T.comap (FocalFusion.ambientHom n S₁ f₁))).1
  have hzC : FocalFusion.ambientHom n S₁ f₁ (z n) ∈
      Subgroup.centralizer ((frontierSetting S fS t p f).D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨a, rfl⟩ := hrange.ge (hD hg)
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (z_mem_center n hn) a]
  have hzD : FocalFusion.ambientHom n S₁ f₁ (z n) ∈ centerOf (frontierSetting S fS t p f).D :=
    ⟨hTD hzT, hzC⟩
  rw [frontierSetting_centerOf_D hn S fS t ht p f,
    KleinFourOddKernel.mem_zpowers_involution _ _ ht2] at hzD
  rcases hzD with h1 | h1
  · exfalso
    have ho := orderOf_injective _ hinj (z n)
    rw [h1, orderOf_one, orderOf_z n (by omega)] at ho
    omega
  · exact h1

end Sylow

section Layer

theorem eq_bot_or_le_of_le_normalizer {Γ : Type*} [Group Γ] {L : Subgroup Γ} [hLn : L.Normal]
    [IsSimpleGroup L] (hcentral : Subgroup.centralizer (L : Set Γ) = ⊥) (K : Subgroup Γ)
    (hK : L ≤ Subgroup.normalizer (K : Set Γ)) : K = ⊥ ∨ L ≤ K := by
  have hinf : ((K ⊓ L).subgroupOf L).Normal := by
    constructor
    intro x hx l
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hK l.2) x).mp hx.1
    · exact L.mul_mem (L.mul_mem l.2 x.2) (L.inv_mem l.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ L).subgroupOf L) with h | h
  · left
    have hbot : K ⊓ L = ⊥ := (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_right
    have hcomm : ⁅K, L⁆ = ⊥ := by
      rw [eq_bot_iff, ← hbot, Subgroup.commutator_le]
      intro k hk l hl
      rw [commutatorElement_def]
      refine ⟨?_, L.mul_mem (hLn.conj_mem l hl k) (L.inv_mem hl)⟩
      have h1 : l * k⁻¹ * l⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hK hl) k⁻¹).mp (K.inv_mem hk)
      have h2 := K.mul_mem hk h1
      rwa [show k * (l * k⁻¹ * l⁻¹) = k * l * k⁻¹ * l⁻¹ by group] at h2
    rw [← le_bot_iff, ← hcentral]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  · right
    exact (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_left

variable {G : Type} [Group G]

theorem map_nu_NZ (t : G) : (NZ t).map (nu t) = Subgroup.zpowers (nu t (tInC t)) := by
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq, MonoidHom.map_zpowers]

theorem solvableRadical_C_eq [Finite G] (t : G) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥) :
    CFSG.solvableRadical (C t) = NZ t := by
  have := SemilinearLayerModel.generalizedFitting_normal (Gamma t)
  apply le_antisymm
  · have : (CFSG.solvableRadical (C t)).Normal := solvableRadical_normal
    have : Group.IsSolvable (CFSG.solvableRadical (C t)) := solvableRadical_isSolvable
    have hRn : ((CFSG.solvableRadical (C t)).map (kappa t)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases eq_bot_or_le_of_le_normalizer hcentral ((CFSG.solvableRadical (C t)).map (kappa t))
        (fun l _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top l) with h | h
    · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    · exfalso
      have : Group.IsSolvable ((CFSG.solvableRadical (C t)).map (kappa t)) :=
        Group.isSolvable_of_surjective ((kappa t).subgroupMap_surjective _)
      have hLs : Group.IsSolvable (CFSG.generalizedFitting (Gamma t)) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h)
          (Subgroup.inclusion_injective h)
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hLs a b)
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    have : Group.IsSolvable (N t) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Local.odd_card_N t)
    exact isSolvable_sup_of_normal (N t) (Z t)

theorem normal_le_NZ_or_layer_le (t : G) [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (K : Subgroup (C t)) [K.Normal] : K ≤ NZ t ∨ localLayerPreimage t ≤ K ⊔ NZ t := by
  have := SemilinearLayerModel.generalizedFitting_normal (Gamma t)
  have : (K.map (kappa t)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases eq_bot_or_le_of_le_normalizer hcentral (K.map (kappa t))
      (fun l _ => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top l) with h | h
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · right
    intro c hc
    have hc' : c ∈ (K.map (kappa t)).comap (kappa t) := h hc
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hc'

theorem le_N_of_odd_of_layer_le_normalizer [Finite G] (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (O : Subgroup (C t)) (hO : Odd (Nat.card O))
    (hnorm : CFSG.generalizedFitting (Gamma t) ≤
      Subgroup.normalizer ((O.map (kappa t) : Subgroup (Gamma t)) : Set (Gamma t))) :
    O ≤ N t := by
  have := SemilinearLayerModel.generalizedFitting_normal (Gamma t)
  rcases eq_bot_or_le_of_le_normalizer hcentral (O.map (kappa t)) hnorm with h | h
  · have hNZ : O ≤ NZ t := by rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have hle : O.map (nu t) ≤ Subgroup.zpowers (nu t (tInC t)) :=
      (Subgroup.map_mono hNZ).trans (map_nu_NZ t).le
    have hdvd : Nat.card (O.map (nu t)) ∣ 2 := by
      refine (Subgroup.card_dvd_of_le hle).trans ?_
      have h2 : orderOf (tInC t) = 2 := by rw [tInC, Subgroup.orderOf_mk, ht]
      rw [Nat.card_zpowers]
      exact (orderOf_map_dvd _ _).trans (by rw [h2])
    have hodd : Odd (Nat.card (O.map (nu t))) := hO.of_dvd_nat (Subgroup.card_map_dvd O (nu t))
    have h1 : Nat.card (O.map (nu t)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact h1
      · rw [h2] at hodd
        exact absurd hodd (by decide)
    have hbot : O.map (nu t) = ⊥ := Subgroup.card_eq_one.mp h1
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  · exfalso
    have hLodd : Odd (Nat.card (CFSG.generalizedFitting (Gamma t))) :=
      hO.of_dvd_nat ((Subgroup.card_dvd_of_le h).trans (Subgroup.card_map_dvd O (kappa t)))
    obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 (CFSG.generalizedFitting (Gamma t))))
    apply hnc U
    have hU : Nat.card U = 1 := by
      rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hLodd.not_two_dvd_nat,
        pow_zero]
    have : Subsingleton U := (Nat.card_eq_one_iff_unique.mp hU).1
    infer_instance

private theorem commutatorElement_mul_left_of_commute {Q : Type*} [Group Q] {a c y : Q}
    (h : Commute c y) : ⁅a * c, y⁆ = ⁅a, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * c * y * (c⁻¹ * a⁻¹) * y⁻¹ = a * (c * y * c⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = a * y * a⁻¹ * y⁻¹ := by rw [h.eq, mul_inv_cancel_right]

private theorem commutatorElement_mul_right_of_commute {Q : Type*} [Group Q] {x b d : Q}
    (h : Commute d x) : ⁅x, b * d⁆ = ⁅x, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * (b * d) * x⁻¹ * (d⁻¹ * b⁻¹) = x * b * (d * x⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = x * b * x⁻¹ * b⁻¹ := by rw [h.inv_right.eq, mul_inv_cancel_right]

theorem eq_top_of_sup_center_eq_top_of_perfect {Q : Type*} [Group Q] [Group.IsPerfect Q]
    {M : Subgroup Q} (h : M ⊔ Subgroup.center Q = ⊤) : M = ⊤ := by
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := Q), commutator_def,
    Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨m, hm, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top x)
  obtain ⟨m', hm', c', hc', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h ▸ Subgroup.mem_top y)
  rw [commutatorElement_mul_left_of_commute (Subgroup.mem_center_iff.mp hc _).symm,
    commutatorElement_mul_right_of_commute (Subgroup.mem_center_iff.mp hc' _).symm,
    commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

theorem layer_le_sup_N_of_le_sup_NZ (t : G) {F : Type} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F)
    (eta : (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F)
    (K : Subgroup (C t)) (hK : localLayerPreimage t ≤ K ⊔ NZ t) :
    localLayerPreimage t ≤ K ⊔ N t := by
  classical
  set Y := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) with hY
  have hF4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
    exact ⟨s, hs⟩
  have := CFSG.LinearGroups.special_linear_dimension_two_perfect hF4
  have : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := eta.symm.toMonoidHom) eta.symm.surjective
  have hcentralker : (barKappa t).ker ≤ Subgroup.center (H t) := by
    rw [barKappa_kernel, Subgroup.zpowers_le]
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)
      (Subgroup.mem_map_of_mem _ (tInC_central t))
  have hkerY : (barKappa t).ker ≤ Y := fun c hc => by
    change barKappa t c ∈ CFSG.generalizedFitting (Gamma t)
    rw [MonoidHom.mem_ker.mp hc]
    exact Subgroup.one_mem _
  have hsup : (K.map (nu t)).subgroupOf Y ⊔ Subgroup.center Y = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N t) y
    have hx : x ∈ localLayerPreimage t := hy
    obtain ⟨k, hk, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hK hx)
    have hcm : nu t m ∈ (barKappa t).ker := by
      rw [MonoidHom.mem_ker, barKappa_nu]
      exact (QuotientGroup.eq_one_iff m).mpr hm
    have hmY : nu t m ∈ Y := hkerY hcm
    have hkY : nu t k ∈ Y := by
      have h := Y.mul_mem hy (Y.inv_mem hmY)
      rwa [map_mul, mul_inv_cancel_right] at h
    have heq : (⟨nu t (k * m), hy⟩ : Y) = ⟨nu t k, hkY⟩ * ⟨nu t m, hmY⟩ :=
      Subtype.ext (map_mul _ _ _)
    rw [heq]
    refine Subgroup.mul_mem_sup ?_ ?_
    · exact Subgroup.mem_subgroupOf.mpr ⟨k, hk, rfl⟩
    · rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hcentralker hcm) g)
  have htop := eq_top_of_sup_center_eq_top_of_perfect hsup
  intro x hx
  have hxY : nu t x ∈ Y := hx
  have hmem : (⟨nu t x, hxY⟩ : Y) ∈ (K.map (nu t)).subgroupOf Y := htop ▸ Subgroup.mem_top _
  have h2 : x ∈ (K.map (nu t)).comap (nu t) := hmem
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2

end Layer

section Criterion

open Subgroup in
theorem pConstrainedWithin_solvableRadical_iff_of_solvableRadical_eq {H : Type*} [Group H]
    [Finite H] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (S : Sylow 2 H)
    (hrad : solvableRadical H = oddCore H ⊔ (center S).map (S : Subgroup H).subtype)
    {P : Subgroup H} (hP : IsSylowOf p P (oddCore H))
    (hSP : (S : Subgroup H) ≤ normalizer (P : Set H)) :
    PConstrainedWithin p H (solvableRadical H) ↔
      IsSylowOf 2 ((center S).map (S : Subgroup H).subtype ⊓ centralizer (P : Set H))
        (centralizer (P : Set H)) :=
  (CFSG.ABGLocalTools.pConstrainedWithin_criteria_of_solvableRadical_eq hp S hrad hP hSP).1

end Criterion

theorem frontier_center_S_eq_center_D {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    centerOf ((frontierSetting S fS t p f).S : Subgroup G) =
      centerOf (frontierSetting S fS t p f).D := by
  rw [frontierSetting_centerOf_S hn S fS t ht p f, frontierSetting_centerOf_D hn S fS t ht p f]

theorem frontier_center_involution_of_sylow {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ S₁ : Sylow 2 G, (frontierSetting S fS t p f).D ≤ (S₁ : Subgroup G) →
      (frontierSetting S fS t p f).x ∈ centerOf (S₁ : Subgroup G) ∧
        ∀ z ∈ centerOf (S₁ : Subgroup G), orderOf z = 2 → z = (frontierSetting S fS t p f).x := by
  intro S₁ hD
  obtain ⟨-, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hc := centerOf_eq_zpowers_of_model hn (S₁ : Subgroup G) (fS.trans (Sylow.equiv S S₁))
  rw [frontier_sylow_z_eq hn S fS t ht p f _ _ hD] at hc
  change t ∈ centerOf (S₁ : Subgroup G) ∧ ∀ y ∈ centerOf (S₁ : Subgroup G), orderOf y = 2 → y = t
  rw [hc]
  refine ⟨Subgroup.mem_zpowers t, fun y hy hy2 => ?_⟩
  rcases (KleinFourOddKernel.mem_zpowers_involution t y ht2).mp hy with rfl | rfl
  · rw [orderOf_one] at hy2
    omega
  · rfl

theorem frontier_normal_le_center_of_inf_D {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ S₁ : Sylow 2 G, (frontierSetting S fS t p f).D ≤ (S₁ : Subgroup G) →
      ∀ X : Subgroup G, X ≤ S₁ → (S₁ : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
        X ⊓ (frontierSetting S fS t p f).D ≤ centerOf (frontierSetting S fS t p f).D →
          X ≤ centerOf (S₁ : Subgroup G) := by
  intro S₁ hD X hXS hXn hXD
  set f₁ : SemidihedralGroup n ≃* (S₁ : Subgroup G) := fS.trans (Sylow.equiv S S₁)
  set ι₁ := FocalFusion.ambientHom n (S₁ : Subgroup G) f₁ with hι₁
  have hinj : Function.Injective ι₁ := FocalFusion.ambientHom_injective n _ f₁
  have hrange : ι₁.range = S₁ := FocalFusion.ambientHom_range n _ f₁
  have hz₁ : ι₁ (z n) = t := frontier_sylow_z_eq hn S fS t ht p f _ f₁ hD
  have hc₁ := centerOf_eq_zpowers_of_model hn (S₁ : Subgroup G) f₁
  rw [← hι₁, hz₁] at hc₁
  have hcD := frontierSetting_centerOf_D hn S fS t ht p f
  have hTD : (frontierSetting S fS t p f).T ≤ (frontierSetting S fS t p f).D :=
    le_inf (by rw [frontierSetting_T hn S fS t ht p f]; exact qdFour_le _ fS)
      Subgroup.le_normalizer
  have hTS₁ : (frontierSetting S fS t p f).T ≤ ι₁.range :=
    hTD.trans (hD.trans hrange.ge)
  have hTmap := Subgroup.map_comap_eq_self hTS₁
  have hK : IsKleinFour (frontierSetting S fS t p f).T := by
    rw [frontierSetting_T hn S fS t ht p f]
    exact qdFour_isKleinFour hn _ fS
  have : IsKleinFour ((frontierSetting S fS t p f).T.comap ι₁) :=
    Local.isKleinFour_of_mulEquiv
      ((((frontierSetting S fS t p f).T.comap ι₁).equivMapOfInjective _ hinj).trans
        (MulEquiv.subgroupCongr hTmap)).symm
  have hNmap : (Subgroup.normalizer (((frontierSetting S fS t p f).T.comap ι₁ : Subgroup _) :
      Set (SemidihedralGroup n))).map ι₁ =
        (S₁ : Subgroup G) ⊓ Subgroup.normalizer ((frontierSetting S fS t p f).T : Set G) := by
    rw [← range_inf_normalizer_map hinj, hTmap, hrange]
  have := sdFourSubgroup_isKleinFour hn
  have hDeq : (frontierSetting S fS t p f).D = (S₁ : Subgroup G) ⊓
      Subgroup.normalizer ((frontierSetting S fS t p f).T : Set G) := by
    apply Subgroup.eq_of_le_of_card_ge (le_inf hD inf_le_right)
    rw [← hNmap, Subgroup.card_map_of_injective hinj, (sd_kleinFour_facts hn _).2.2.2,
      frontierSetting_D hn S fS t ht p f,
      Subgroup.card_map_of_injective (FocalFusion.ambientHom_injective n _ fS),
      (sd_kleinFour_facts hn (sdFourSubgroup n)).2.2.2]
  have hX₀ : (X.comap ι₁).Normal := by
    refine ⟨fun x hx g => ?_⟩
    change ι₁ (g * x * g⁻¹) ∈ X
    rw [map_mul, map_mul, map_inv]
    have hg : ι₁ g ∈ (S₁ : Subgroup G) := hrange ▸ ⟨g, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hXn hg) _).mp hx
  have hX₀z : X.comap ι₁ ⊓ Subgroup.normalizer (((frontierSetting S fS t p f).T.comap ι₁ :
      Subgroup _) : Set (SemidihedralGroup n)) ≤ Subgroup.zpowers (z n) := by
    rintro y ⟨hyX, hyN⟩
    have hyD : ι₁ y ∈ (frontierSetting S fS t p f).D := by
      rw [hDeq, ← hNmap]
      exact ⟨y, hyN, rfl⟩
    have hy := hXD ⟨hyX, hyD⟩
    rw [hcD, ← hz₁, ← MonoidHom.map_zpowers] at hy
    exact (Subgroup.mem_map_iff_mem hinj).mp hy
  have hle := sd_normal_le_zpowers_z hn _ _ hX₀ hX₀z
  have hXmap : (X.comap ι₁).map ι₁ = X := Subgroup.map_comap_eq_self (hXS.trans hrange.ge)
  rw [hc₁, ← hz₁, ← MonoidHom.map_zpowers, ← hXmap]
  exact Subgroup.map_mono hle

theorem frontierSetting_solvRad {G : Type} [Group G] [Finite G] {n : ℕ} (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G) (p f : ℕ)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥) :
    solvRadIn (frontierSetting S fS t p f).N = (NZ t).map (C t).subtype := by
  change (CFSG.solvableRadical (C t)).map (C t).subtype = _
  rw [solvableRadical_C_eq t hnonab hcentral]

theorem map_subgroupOf_C_subtype {G : Type} [Group G] (t : G) {K : Subgroup G}
    (hK : K ≤ C t) : (K.subgroupOf (C t)).map (C t).subtype = K := by
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hK]

theorem frontier_automizer_T {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (_hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    automizerIndex (frontierSetting S fS t p f).T = 6 := by
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  rw [frontierSetting_T hn S fS t ht p f]
  exact automizerIndex_qdFour_eq_six hn S fS
    (InvolutionFusion.supplied_s_isConj_z n hn S fS hG)

theorem frontier_L_eq {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).L = (frontierSetting S fS t p f).L₀ ⊔
      ((frontierSetting S fS t p f).D ⊓
        Subgroup.centralizer ((frontierSetting S fS t p f).T : Set G)) := by
  have hσ := frontierSetting_isValid hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf
    hq hmodel
  obtain ⟨-, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    have hS : ((frontierSetting S fS t p f).S : Subgroup G) =
        Subgroup.closure {FocalFusion.ambientHom n (S : Subgroup G) fS (r n * s n),
          FocalFusion.ambientHom n (S : Subgroup G) fS (s n)} := by
      rw [← Set.image_pair, ← MonoidHom.map_closure, sd_closure_rs_s (by omega),
        ← MonoidHom.range_eq_map, FocalFusion.ambientHom_range]
      rfl
    rw [hS, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · apply Subgroup.mem_sup_left
      have hmem : FocalFusion.ambientHom n (S : Subgroup G) fS (r n * s n) ∈ C t :=
        (frontierSetting S fS t p f).S_le_N hσ (fS (r n * s n)).property
      have hx4 : orderOf (⟨_, hmem⟩ : C t) = 4 := by
        rw [Subgroup.orderOf_mk, orderOf_ambientHom, orderOf_rs hn]
      exact ⟨_, actual_order_four_image_mem_layer n hn S fS hG t ht2 F A p f rho data _ hx4, rfl⟩
    · apply Subgroup.mem_sup_right
      exact ⟨(frontierSetting S fS t p f).T_le_D hσ (frontierSetting S fS t p f).x₂_mem_T,
        (frontierSetting S fS t p f).T_le_C hσ (frontierSetting S fS t p f).x₂_mem_T⟩
  · exact sup_le_sup_left (inf_le_left.trans (frontierSetting S fS t p f).D_le_S) _

theorem frontier_N_oddCore_of_cover {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (_hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ K : Subgroup G, K ≤ (frontierSetting S fS t p f).N →
      ((frontierSetting S fS t p f).L₀ : Set G) ⊆
        (K : Set G) * (frontierSetting S fS t p f).ON →
      oddCoreIn K ≤ (frontierSetting S fS t p f).ON := by
  intro K hKN hcov
  obtain ⟨-, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hOC : oddCoreIn K ≤ C t := (oddCoreIn_le K).trans hKN
  have hodd : Odd (Nat.card ((oddCoreIn K).subgroupOf (C t))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv]
    exact odd_card_oddCoreIn K
  have hKnorm := le_normalizer_oddCoreIn K
  have hnorm : CFSG.generalizedFitting (Gamma t) ≤ Subgroup.normalizer
      ((((oddCoreIn K).subgroupOf (C t)).map (kappa t) : Subgroup (Gamma t)) :
        Set (Gamma t)) := by
    intro y hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (NZ t) y
    have hc : c ∈ localLayerPreimage t := hy
    obtain ⟨k, hk, m, hm, hkm⟩ := Set.mem_mul.mp (hcov ⟨c, hc, rfl⟩)
    rw [frontierSetting_ON] at hm
    obtain ⟨m', hm', rfl⟩ := hm
    have hkC : k ∈ C t := by
      rw [eq_mul_inv_of_mul_eq hkm]
      exact (C t).mul_mem c.2 ((C t).inv_mem m'.2)
    have hk'N : (⟨k, hkC⟩ : C t) ∈
        Subgroup.normalizer (((oddCoreIn K).subgroupOf (C t) : Subgroup (C t)) : Set (C t)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      exact (Subgroup.mem_normalizer_iff.mp (hKnorm hk) (h : G))
    have hkappa : kappa t (⟨k, hkC⟩ : C t) = kappa t c := by
      have hc' : c = (⟨k, hkC⟩ : C t) * m' := Subtype.ext hkm.symm
      have hm1 : kappa t m' = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left hm')
      rw [hc', map_mul, hm1, mul_one]
    change kappa t c ∈ _
    rw [← hkappa]
    exact Subgroup.le_normalizer_map (kappa t) ⟨_, hk'N, rfl⟩
  have hle := le_N_of_odd_of_layer_le_normalizer t ht2 hcentral hnc _ hodd hnorm
  rw [frontierSetting_ON, ← map_subgroupOf_C_subtype t hOC]
  exact Subgroup.map_mono hle

theorem frontier_N_solvRad {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    solvRadIn (frontierSetting S fS t p f).N = (frontierSetting S fS t p f).ON ⊔
      centerOf ((frontierSetting S fS t p f).S : Subgroup G) := by
  rw [frontierSetting_solvRad S fS t p f hnonab hcentral, frontierSetting_ON,
    frontierSetting_centerOf_S hn S fS t ht p f, Subgroup.map_sup, MonoidHom.map_zpowers]
  rfl

theorem frontier_N_minimalNormal {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (_hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (_ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ K : Subgroup G, K ≤ (frontierSetting S fS t p f).N →
      (frontierSetting S fS t p f).N ≤ Subgroup.normalizer (K : Set G) →
      ¬ K ≤ solvRadIn (frontierSetting S fS t p f).N →
      (frontierSetting S fS t p f).L₀ ≤ K ⊔ solvRadIn (frontierSetting S fS t p f).N := by
  intro K hKN hNK hKS
  rw [frontierSetting_solvRad S fS t p f hnonab hcentral] at hKS ⊢
  have : (K.subgroupOf (C t)).Normal := by
    constructor
    intro x hx c
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hNK c.2) x).mp hx
  have hKmap := map_subgroupOf_C_subtype t hKN
  rcases normal_le_NZ_or_layer_le t hcentral (K.subgroupOf (C t)) with h | h
  · exact absurd (hKmap ▸ Subgroup.map_mono h) hKS
  · calc (frontierSetting S fS t p f).L₀ = (localLayerPreimage t).map (C t).subtype := rfl
      _ ≤ (K.subgroupOf (C t) ⊔ NZ t).map (C t).subtype := Subgroup.map_mono h
      _ = K ⊔ (NZ t).map (C t).subtype := by rw [Subgroup.map_sup, hKmap]

theorem frontier_N_coverTransfer {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ K : Subgroup G, K ≤ (frontierSetting S fS t p f).N →
      (frontierSetting S fS t p f).L₀ ≤ K ⊔ solvRadIn (frontierSetting S fS t p f).N →
      ((frontierSetting S fS t p f).L₀ : Set G) ⊆
        (K : Set G) * (frontierSetting S fS t p f).ON := by
  intro K hKN hL
  obtain ⟨-, ht2, -, -, -, -⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hG := CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hGnonab
  obtain ⟨F, hfield, hfinite, A, rho, data⟩ :=
    actual_simple_layer_matrix_data n hn S fS hG t ht2 hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨eta, -, -, -⟩ := data.compatible_layer
  have hF : 4 ≤ Nat.card F := by
    rw [data.field_card]
    omega
  rw [frontierSetting_solvRad S fS t p f hnonab hcentral] at hL
  have hKmap := map_subgroupOf_C_subtype t hKN
  have hL' : localLayerPreimage t ≤ K.subgroupOf (C t) ⊔ NZ t := by
    rw [← Subgroup.map_le_map_iff_of_injective (C t).subtype_injective, Subgroup.map_sup, hKmap]
    exact hL
  have h := layer_le_sup_N_of_le_sup_NZ t hF eta _ hL'
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨k, hk, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h hc)
  rw [frontierSetting_ON]
  exact Set.mul_mem_mul hk ⟨m, hm, rfl⟩

theorem frontier_N_constraint_criterion {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (_hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card (frontierSetting S fS t p f).ON → ∀ R : Subgroup G,
      IsSylowOf r R (frontierSetting S fS t p f).ON →
      ((frontierSetting S fS t p f).S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) →
      ((frontierSetting S fS t p f).Constrained r ↔
        IsSylowOf 2 (centerOf ((frontierSetting S fS t p f).S : Subgroup G) ⊓
          Subgroup.centralizer (R : Set G))
          ((frontierSetting S fS t p f).N ⊓ Subgroup.centralizer (R : Set G))) := by
  intro ℓ hℓ hℓdvd R hR hSR
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (frontierSetting S fS t p f).odd_card_ON)
      (even_iff_two_dvd.mpr hℓdvd)
  have hSC : (S : Subgroup G) ≤ C t := frontier_S_le_C hn S fS t ht p f
  set SH : Sylow 2 (C t) := S.subtype hSC with hSH
  have hSHcoe : (SH : Subgroup (C t)) = (S : Subgroup G).subgroupOf (C t) := Sylow.coe_subtype _ _
  have hRC : R ≤ C t := hR.le.trans (frontierSetting S fS t p f).ON_le_N
  set P : Subgroup (C t) := R.subgroupOf (C t) with hPdef
  have hPR : P.map (C t).subtype = R := map_subgroupOf_C_subtype t hRC
  have hZ : (Subgroup.center SH).map (SH : Subgroup (C t)).subtype = Z t := by
    rw [map_center_subtype]
    apply Subgroup.map_injective (C t).subtype_injective
    rw [← centerOf_map_of_injective (C t).subtype_injective, hSHcoe,
      map_subgroupOf_C_subtype t hSC, MonoidHom.map_zpowers]
    exact frontierSetting_centerOf_S hn S fS t ht p f
  have hrad : CFSG.solvableRadical (C t) = CFSG.oddCore (C t) ⊔
      (Subgroup.center SH).map (SH : Subgroup (C t)).subtype := by
    rw [solvableRadical_C_eq t hnonab hcentral, hZ,
      QuaternionFocalFactorization.oddCore_eq_twoPrimeCore]
  have hP : IsSylowOf ℓ P (CFSG.oddCore (C t)) := by
    rw [← isSylowOf_map_subtype_iff (C t), hPR]
    exact hR
  have hSP : (SH : Subgroup (C t)) ≤ Subgroup.normalizer (P : Set (C t)) := by
    intro x hx
    rw [hSHcoe, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hPdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hSR hx) y
  have key := pConstrainedWithin_solvableRadical_iff_of_solvableRadical_eq hℓ2 SH hrad hP hSP
  have hcent : (Subgroup.centralizer (P : Set (C t))).map (C t).subtype =
      C t ⊓ Subgroup.centralizer (R : Set G) := by
    rw [← centralizer_of_original_subtype_image (C t) P, hPR, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have hZt : (Z t).map (C t).subtype = Subgroup.zpowers t := MonoidHom.map_zpowers _ _
  have hinf : Subgroup.zpowers t ⊓ (C t ⊓ Subgroup.centralizer (R : Set G)) =
      Subgroup.zpowers t ⊓ Subgroup.centralizer (R : Set G) := by
    rw [← inf_assoc, inf_of_le_left (Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl))]
  change PConstrainedWithin ℓ (C t) (CFSG.solvableRadical (C t)) ↔ _
  rw [key, ← isSylowOf_map_subtype_iff (C t), Subgroup.map_inf _ _ _ (C t).subtype_injective,
    hcent, hZ, hZt, hinf, frontierSetting_centerOf_S hn S fS t ht p f]
  rfl

theorem frontier_nStructure {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
    (t : G) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    (frontierSetting S fS t p f).NStructure where
  L_eq := frontier_L_eq hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
  N_oddCore_of_cover := frontier_N_oddCore_of_cover hGnonab n hn S fS t ht hnonab hcentral hnc
    p f hp hpodd hf hq hmodel
  N_solvRad := frontier_N_solvRad hGnonab n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq
    hmodel
  N_minimalNormal := frontier_N_minimalNormal hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel
  N_coverTransfer := frontier_N_coverTransfer hGnonab n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel
  N_constraint_criterion := frontier_N_constraint_criterion hGnonab n hn S fS t ht hnonab hcentral
    hnc p f hp hpodd hf hq hmodel
  center_S_eq_center_D := frontier_center_S_eq_center_D hGnonab n hn S fS t ht hnonab hcentral
    hnc p f hp hpodd hf hq hmodel
  center_involution_of_sylow := frontier_center_involution_of_sylow hGnonab n hn S fS t ht hnonab
    hcentral hnc p f hp hpodd hf hq hmodel
  normal_le_center_of_inf_D := frontier_normal_le_center_of_inf_D hGnonab n hn S fS t ht hnonab
    hcentral hnc p f hp hpodd hf hq hmodel

end CFSG.Semidihedral.AllPrime
