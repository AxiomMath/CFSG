module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Set5
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4GCentA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y6SCore_mem_zpowers_eq_one_or_self {z v : G} (hz2 : z ^ 2 = 1)
    (hv : v ∈ zpowers z) : v = 1 ∨ v = z := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have h2 : z ^ (2 : ℤ) = 1 := by simpa using hz2
  rw [zpow_eq_zpow_emod m h2]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem y6_K_core (c : Ctx5 G L) (hH : F33Hyp c.s c.e) {x : G}
    (hxY : x ∈ normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G))
    (hc : ∀ a ∈ c.s.fr.A, ⁅a, x⁆ ∈ zpowers c.s.fr.z) : x ∈ C1 c.e := by
  classical
  have cfg := c.y6cfg5 hH
  have hcomm_gen : ∀ g ∈ c.s.fr.A, ⁅x, g⁆ = 1 ∨ ⁅x, g⁆ = c.s.fr.z := by
    intro g hgA
    have hxgz : ⁅x, g⁆ ∈ zpowers c.s.fr.z := by
      have hmem := Subgroup.inv_mem _ (hc g hgA)
      rwa [commutatorElement_inv] at hmem
    exact y6SCore_mem_zpowers_eq_one_or_self cfg.rel.z_sq hxgz
  have hz_cent : ∀ a ∈ (closure {c.s.fr.a₁, c.s.fr.b₁, c.s.fr.a₂, c.s.fr.b₂} : Subgroup G),
      a * c.s.fr.z = c.s.fr.z * a := y6q8_z_central cfg.rel
  have hza₁ : ⁅c.s.fr.z, c.s.fr.a₁⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (hz_cent c.s.fr.a₁ (Subgroup.subset_closure (by simp))).symm
  have hzb₁ : ⁅c.s.fr.z, c.s.fr.b₁⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (hz_cent c.s.fr.b₁ (Subgroup.subset_closure (by simp))).symm
  have hza₂ : ⁅c.s.fr.z, c.s.fr.a₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (hz_cent c.s.fr.a₂ (Subgroup.subset_closure (by simp))).symm
  have hzb₂ : ⁅c.s.fr.z, c.s.fr.b₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (hz_cent c.s.fr.b₂ (Subgroup.subset_closure (by simp))).symm
  have hy : ∀ a ∈ ({c.s.fr.a₁, c.s.fr.b₁, c.s.fr.a₂, c.s.fr.b₂} : Set G),
      ⁅x, a⁆ = 1 ∨ ⁅x, a⁆ = c.s.fr.z := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hcomm_gen c.s.fr.a₁ (by rw [cfg.hA]; exact Subgroup.subset_closure (by simp))
    · exact hcomm_gen c.s.fr.b₁ (by rw [cfg.hA]; exact Subgroup.subset_closure (by simp))
    · exact hcomm_gen c.s.fr.a₂ (by rw [cfg.hA]; exact Subgroup.subset_closure (by simp))
    · exact hcomm_gen c.s.fr.b₂ (by rw [cfg.hA]; exact Subgroup.subset_closure (by simp))
  obtain ⟨a₀, ha₀A, ha₀C⟩ :=
    y4_central_aut cfg.rel.z_sq hza₁ hzb₁ hza₂ hzb₂ cfg.rel.comm1 cfg.rel.comm2
      cfg.rel.a1a2 cfg.rel.a1b2 cfg.rel.b1a2 cfg.rel.b1b2 hy
  have ha₀A' : a₀ ∈ c.s.fr.A := by rw [cfg.hA]; exact ha₀A
  let w : G := a₀⁻¹ * x
  have hw_cent_A : w ∈ centralizer (c.s.fr.A : Set G) := by
    dsimp only [w]
    rw [cfg.hA]
    exact ha₀C
  have hA_le_Y : c.s.fr.A ≤ normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) :=
    (le_sup_left : c.s.fr.A ≤ c.s.fr.A ⊔ zpowers c.s.t).trans
      (Subgroup.le_normalizer : (c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) ≤
        normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G))
  have hwY : w ∈ normalizer ((c.s.fr.A ⊔ zpowers c.s.t : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hA_le_Y ha₀A')) hxY
  have hwt_cases : w * c.s.t * w⁻¹ = c.s.t ∨ w * c.s.t * w⁻¹ = c.s.fr.z * c.s.t :=
    s5_hY_conj c hH hwY
  have hzt_le_C0 : zt c.s ≤ C0 c.e :=
    s3_zt_le_C0 c.s (lfactsA_of_setting hH.hS hH.hZ c.s) c.e
  have hwC0 : w ∈ C0 c.e := by
    rcases hwt_cases with hwt | hwt
    · have hwH : w ∈ c.s.H := by
        show w ∈ Subgroup.centralizer ({c.s.t} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have hwt_comm : w * c.s.t = c.s.t * w := by
          calc w * c.s.t = (w * c.s.t * w⁻¹) * w := by group
            _ = c.s.t * w := by rw [hwt]
        exact hwt_comm.symm
      have hwcent : w ∈ centIn c.s.H c.s.fr.A := Subgroup.mem_inf.mpr ⟨hwH, hw_cent_A⟩
      rw [y5_centHA hH] at hwcent
      exact hzt_le_C0 hwcent
    · let v : G := c.d * w
      have hv_t : v * c.s.t * v⁻¹ = c.s.t := by
        have hzsq : c.s.fr.z * c.s.fr.z = 1 := by simpa [pow_two] using cfg.rel.z_sq
        dsimp only [v]
        calc (c.d * w) * c.s.t * (c.d * w)⁻¹
            = c.d * (w * c.s.t * w⁻¹) * c.d⁻¹ := by group
          _ = c.d * (c.s.fr.z * c.s.t) * c.d⁻¹ := by rw [hwt]
          _ = (c.d * c.s.fr.z * c.d⁻¹) * (c.d * c.s.t * c.d⁻¹) := by group
          _ = c.s.fr.z * (c.s.fr.z * c.s.t) := by
                rw [y5_dz (c := c) hH, y5_dtd (c := c) hH]
          _ = c.s.t := by rw [← mul_assoc, hzsq, one_mul]
      have hv_cent_A : v ∈ centralizer (c.s.fr.A : Set G) := by
        rw [Subgroup.mem_centralizer_iff] at hw_cent_A ⊢
        intro a ha
        dsimp only [v]
        have hda : a * c.d = c.d * a := s6_d_comm_A c ha
        calc a * (c.d * w) = (a * c.d) * w := by group
          _ = (c.d * a) * w := by rw [hda]
          _ = c.d * (a * w) := by group
          _ = c.d * (w * a) := by rw [hw_cent_A a ha]
          _ = (c.d * w) * a := by group
      have hvH : v ∈ c.s.H := by
        show v ∈ Subgroup.centralizer ({c.s.t} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have hvt_comm : v * c.s.t = c.s.t * v := by
          calc v * c.s.t = (v * c.s.t * v⁻¹) * v := by group
            _ = c.s.t * v := by rw [hv_t]
        exact hvt_comm.symm
      have hvcent : v ∈ centIn c.s.H c.s.fr.A := Subgroup.mem_inf.mpr ⟨hvH, hv_cent_A⟩
      rw [y5_centHA hH] at hvcent
      have hvC0 : v ∈ C0 c.e := hzt_le_C0 hvcent
      have hw_eq : c.d⁻¹ * v = w := by dsimp only [v]; group
      have hprod : c.d⁻¹ * v ∈ C0 c.e :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ c.d_mem) hvC0
      rwa [hw_eq] at hprod
  have hx_eq : x = a₀ * w := by dsimp only [w]; group
  rw [hx_eq]
  exact Subgroup.mul_mem_sup ha₀A' hwC0

end CFSG.OddStandard.HigherRank.YamadaG23
