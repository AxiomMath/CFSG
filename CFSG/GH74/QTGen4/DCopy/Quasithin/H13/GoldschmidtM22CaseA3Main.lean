module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseA3Fix
public import CFSG.Quasithin.H13.GoldschmidtM22CaseA3Sign
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndKu

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

theorem m22CaseAThree_holds_F4 : M22CaseAThree_F4 := by
  intro G _ _ T M L V g D z hl h hk hA hz
  have hZ : Nat.card (quasithinOmegaOneCenter T) = 2 := (hl.h622 G T M L V h).2.1
  obtain ⟨e⟩ := (hl.h622 G T M L V h).1
  obtain ⟨P⟩ := endN2_F4 hl.g64 hl.h621 hl.h622 hl.h626 hl.h629 hl.h6210 hl.h6211 hl.h6212 h
    hk.hZS
  have hCV : Subgroup.centralizer (V : Set G) = V := centralizer_eq_of_le h hA
  obtain ⟨φ, hφs, hφk⟩ := exists_hom_perm5 hk.normalizer_eq e
  have hzZ : z ∈ quasithinOmegaOneCenter T := hz ▸ Subgroup.mem_zpowers z
  have hzV : z ∈ V := Z_le_V h hZ hzZ
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot] at hz
    rw [hz] at hZ
    simp at hZ
  have hVL_norm : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have := le_normalizer_oTwoUpper (Subgroup.normalizer (V : Set G))
    rwa [hk.oTwoUpper_normalizer] at this
  have hVL : V ≤ L := CaseA3.le_of_commutator_eq h.natural.commutator_eq
    (h.toHyp611.le_T.trans (h.toHyp611.T_le_normalizer.trans hVL_norm))
  have hker : ∀ x : ↥(Subgroup.normalizer (V : Set G)), φ x = 1 ↔ (x : G) ∈ V := by
    intro x
    rw [← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf, hCV]
  have hnle : ¬ L ≤ V := fun hLV =>
    h.natural.not_le_centralizer (hLV.trans (V_le_centralizer_V h))
  have hD_le_T : D ≤ T :=
    hk.kData.D_le_CHU.trans (P.CHU_le_T_F4 h hZ hl.h621 hl.h629 hl.h6210 hl.h6212)
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := h.toHyp611.T_le_normalizer
  have hCHU : CHU T L V = pCoreOf 2 (HH T) := (hl.h6212 G T M L V h).2.2
  have hzs_le_D : ch6ZS T L V ≤ D := by
    intro u hu
    have hu1 : u ∈ CHU T L V := by
      rw [hCHU]
      exact UU_le_pCore_F4 h hl.h6210 (le_conjClosure _ _ hu)
    rw [hk.kData.D_eq]
    exact ⟨Subgroup.mem_sup_left hu.1, hu1⟩
  have hnotDL : ¬ D ≤ L := by
    intro hDL
    have hA1 : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤ L := by
      rw [KData.conj_inf_normalizer_eq_F4 hk.kData h P hZ hl.h6210 hl.h6211]
      exact (hk.kData.V1_le_D).trans hDL
    exact hk.kData.case2.not_le (A4.autOn_mono hA1)
  have hVD : V ⊓ D = V ⊓ CHU T L V :=
    le_antisymm (inf_le_inf_left _ hk.kData.D_le_CHU) (le_inf inf_le_left hk.kData.V0_le_D)
  have hz2 : z ^ 2 = 1 := h.toHyp611.isElemAbelian.2 z hzV
  have C : CaseA3.Setup T L V D z φ :=
    { T_le := hTN
      L_le := h.toHyp611.L_le_normalizer
      normalizes_L := hVL_norm
      V_le_T := h.toHyp611.le_T
      V_le_L := hVL
      isElemAbelian_V := h.toHyp611.isElemAbelian
      isPGroup_T := h.sylow.1
      odd_index_T := fun hd =>
        h.sylow.2 (dvd_trans hd (Subgroup.relIndex_dvd_index_of_le hTN))
      ker_phi := hker
      mem_L_iff := fun x => CaseA3.mem_L_iff_sign φ hφs hker h.toHyp611.L_le_normalizer hVL_norm hVL
        hk.oTwoUpper_normalizer hnle x
      centralizer_le := fun x hx hxz => by
        have hxH : x ∈ HH T := by
          rw [HH_eq_centralizer_of_gen hz, Subgroup.mem_centralizer_singleton_iff]
          exact hxz
        have : x ∈ HH T ⊓ M := ⟨hxH, (hl.h621 G T M L V h).2 hx⟩
        rwa [P.HH_inf_M_eq_T_F4 h hZ hl.h629 hl.h6210 hl.h6212] at this
      transitive := fun v hv w hw hv1 hw1 => h.natural.exists_conj_eq hv hw hv1 hw1
      z_mem := hzV
      z_ne_one := hz1
      T_centralizes := fun t ht =>
        Subgroup.mem_centralizer_iff.mp (omegaOneCenter_le_centralizer T hzZ) t ht
      eq_one_or_eq := fun u hu hcomm => by
        have huZ : u ∈ quasithinOmegaOneCenter T :=
          Subgroup.subset_closure ⟨⟨h.toHyp611.le_T hu, Subgroup.mem_centralizer_iff.mpr hcomm⟩,
            h.toHyp611.isElemAbelian.2 u hu⟩
        rw [hz] at huZ
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp huZ
        rw [zpow_eq_zpow_emod k (show z ^ (2 : ℤ) = 1 by simpa using hz2)]
        rcases Int.emod_two_eq_zero_or_one k with h0 | h0 <;> simp [h0]
      exists_zs := by
        obtain ⟨u, hu, huZ⟩ := exists_ZS_not_Z h hZ
        exact ⟨u, hu, fun h1 => huZ (h1 ▸ Subgroup.one_mem _), fun h1 => huZ (h1 ▸ hzZ)⟩
      card_zs := card_ZS_eq_four h
      D_le_T := hD_le_T
      D_comm := fun x hx =>
        (Subgroup.mem_centralizer_iff.mp (hk.kData.D_le_HH hx) z hzZ).symm
      card_D := by rw [hk.kData.extra.2.1]; norm_num
      not_D_le_L := hnotDL
      card_V_inf_D := by rw [hVD]; exact KData.card_V0_F4 h hl.h6211
      zs_le_D := hzs_le_D }
  obtain ⟨d₀, -, hdD, hdz, hinter⟩ := C.exists_inter
  refine ⟨d₀⁻¹, by simpa using hdD, by simpa using hdz, ?_, ?_⟩
  · rw [hinter]
    exact B2F.isElemAbelian_mono inf_le_left h.toHyp611.isElemAbelian
  · rw [hinter]
    exact card_ZS_eq_four h

end CFSG.Quasithin.H13.GM22
