module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec5S
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCentT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5IntroCore
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YD8
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem sec5Intro_of (hDef : Fusion3Def) (h32 : Fusion32) (hZ : OddCentre) (hC : CentTA) :
    Sec5Intro := by
  classical
  intro G _ _ L hS hL s e hnb
  have hLF := lfactsA_of_setting hS (hZ G L hS hL) s
  have hdef := hDef G L hS hL s e
  have hf32 := h32 G L hS hL s e
  have hCs := hC G L hS hL s
  obtain ⟨d, hdC0, hd2, hdQ, hdT, hdt4, hdt2, hCeq⟩ :=
    intro5_core e hLF hdef hf32 hCs hnb
  have hR1T1 : e.R₁ ≤ e.T₁ := by
    unfold Setting3.Ext.R₁
    split_ifs with hRT
    · exact le_rfl
    · exact inf_le_left
  have hC0R1 : C0 e ≤ e.R₁ := by
    intro x hx
    have hxT1 : x ∈ e.T₁ := hx.1
    have hxcent : x ∈ centralizer (s.fr.A : Set G) := hx.2
    have hcA : closure ({s.fr.a₁, s.fr.b₁} : Set G) ≤ s.fr.A := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases (by simpa using hy : y = s.fr.a₁ ∨ y = s.fr.b₁) with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    unfold Setting3.Ext.R₁
    split_ifs with hRT
    · exact hxT1
    · refine ⟨hxT1, ?_⟩
      change ∀ y : G, y ∈ (Subgroup.closure {s.fr.a₁, s.fr.b₁} : Set G) ↔
        x * y * x⁻¹ ∈ (Subgroup.closure {s.fr.a₁, s.fr.b₁} : Set G)
      intro y
      constructor
      · intro hy
        have hA : y ∈ s.fr.A := hcA hy
        have hcomm : y * x = x * y := hxcent y hA
        have hconj : x * y * x⁻¹ = y := by
          rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
        rw [hconj]; exact hy
      · intro hy
        have hA' : x * y * x⁻¹ ∈ s.fr.A := hcA hy
        have hcomm : (x * y * x⁻¹) * x = x * (x * y * x⁻¹) := hxcent _ hA'
        have hc : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
          have h2 := congrArg (fun t => x⁻¹ * t) hcomm
          simpa [mul_assoc] using h2
        have hy_eq : y = x⁻¹ * (x * y * x⁻¹) * x := by group
        rw [hy_eq, hc]; exact hy
  have hgen : C0 e = closure ({s.t, d} : Set G) := by
    rw [hCeq]
    have ht_mem : s.t ∈ closure ({s.t, d} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert s.t {d})
    have hd_mem : d ∈ closure ({s.t, d} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem s.t (Set.mem_singleton d))
    have hdt_mem : d * s.t ∈ closure ({s.t, d} : Set G) :=
      Subgroup.mul_mem _ hd_mem ht_mem
    have hz_mem : s.fr.z ∈ closure ({s.t, d} : Set G) := by
      rw [← hdt2]
      exact (closure ({s.t, d} : Set G)).pow_mem hdt_mem 2
    apply le_antisymm
    · apply sup_le
      · simp only [zt]
        rw [Subgroup.closure_le]
        intro x hx
        rcases (by simpa using hx : x = s.fr.z ∨ x = s.t) with rfl | rfl
        · exact hz_mem
        · exact ht_mem
      · rw [Subgroup.zpowers_le]
        exact hd_mem
    · rw [Subgroup.closure_le]
      intro x hx
      rcases (by simpa using hx : x = s.t ∨ x = d) with hxt | hxd
      · rw [hxt]
        exact Subgroup.mem_sup_left
          (Subgroup.subset_closure (Set.mem_insert_of_mem s.fr.z (Set.mem_singleton s.t)))
      · rw [hxd]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have h4 : orderOf (d * s.t) = 4 := by
    have hz1 : s.fr.z ≠ 1 := by
      intro h1
      have h1' : orderOf s.fr.z = 1 := by rw [h1, orderOf_one]
      rw [s3_z_order s hLF] at h1'
      norm_num at h1'
    have hnot : ¬ (d * s.t) ^ 2 ^ 1 = 1 := by
      rw [pow_one, hdt2]
      exact hz1
    have hfin : (d * s.t) ^ 2 ^ (1 + 1) = 1 := by
      norm_num
      exact hdt4
    rw [orderOf_eq_prime_pow hnot hfin]
    norm_num
  have hdih : Nonempty (↥(C0 e) ≃* DihedralGroup 4) :=
    dihedral_of_involutions' (C := C0 e) (t := s.t) (d := d) hgen s.t_order hd2 h4
  have heStar : maxElemAbelian (C0 e) = {zt s, closure {s.fr.z, d}} := by
    have h := d8_maxElemAbelian (C := C0 e) (t := s.t) (d := d) hgen hdih s.t_order hd2
    rw [hdt2] at h
    simpa [zt] using h
  have heqR1 : C0 e = centIn e.R₁ s.fr.A := by
    apply le_antisymm
    · intro x hx
      exact ⟨hC0R1 hx, hx.2⟩
    · intro x hx
      exact ⟨hR1T1 hx.1, hx.2⟩
  have hR1eq : e.R₁ = s.R ⊔ zpowers d := by
    have hdR1 : d ∈ e.R₁ := hC0R1 hdC0
    have h := eq_sup_zpowers_of_relIndex_two (H := s.T) (K := e.T₁) (X := e.R₁) hR1T1
      hdef.2.1 hdR1 hdT
    rw [h, hf32.2.2.1]
  exact ⟨d, hdC0, hd2, hdQ,
    { centT := hCs, dihedral := hdih, eq_R1 := heqR1, gen := hgen, eStar := heStar,
      R1_eq := hR1eq }⟩

end CFSG.OddStandard.HigherRank.YamadaG23
