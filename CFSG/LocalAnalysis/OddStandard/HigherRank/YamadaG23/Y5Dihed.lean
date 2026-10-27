module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YD8
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YDihedral
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31CenT
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YIdx2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Hyp

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y5_d_sq (c : Ctx5 G L) : c.d ^ 2 = 1 := by
  simpa [c.d_order] using pow_orderOf_eq_one c.d

theorem y5_d_mem_T1 (c : Ctx5 G L) : c.d ∈ c.e.T₁ := by
  have h := c.d_mem
  simp only [C0, centIn, Subgroup.mem_inf] at h
  exact h.1

theorem y5_d_cent_A (c : Ctx5 G L) : ∀ a ∈ c.s.fr.A, c.d * a * c.d⁻¹ = a := by
  have hdCentA : c.d ∈ centralizer (c.s.fr.A : Set G) := by
    have h := c.d_mem
    simp only [C0, centIn, Subgroup.mem_inf] at h
    exact h.2
  intro a ha
  have hcomm : a * c.d = c.d * a :=
    (Subgroup.mem_centralizer_iff.mp hdCentA) a ha
  rw [← hcomm]
  group

theorem y5_z_mem_C0 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : c.s.fr.z ∈ C0 c.e := by
  have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  exact s3_zt_le_C0 c.s hA c.e (Subgroup.subset_closure (by simp))

theorem y5_dz {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    c.d * c.s.fr.z * c.d⁻¹ = c.s.fr.z :=
  y5_d_cent_A c c.s.fr.z (s3_z_mem_A c.s)

theorem y5_dtd {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    c.d * c.s.t * c.d⁻¹ = c.s.fr.z * c.s.t := by
  have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  have hz2 : orderOf c.s.fr.z = 2 := s3_z_order c.s hA
  obtain ⟨hord, hu2⟩ := Ctx5pre.u_facts c.toCtx5pre hz2
  have h4 : (c.d * c.s.t) ^ 4 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  exact (d8_rel c.s.t_order c.d_order h4 hu2).1

theorem y5_d_not_mem_T {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : c.d ∉ c.s.T := by
  intro hdT
  apply c.d_not_mem
  have hdcent : c.d ∈ centralizer (c.s.fr.A : Set G) := by
    have h := c.d_mem
    simp only [C0, centIn, Subgroup.mem_inf] at h
    exact h.2
  have hmem : c.d ∈ centIn c.s.T c.s.fr.A := Subgroup.mem_inf.mpr ⟨hdT, hdcent⟩
  rwa [c.intro5.centT] at hmem

theorem y5_T1_eq {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : c.e.T₁ = c.s.T ⊔ zpowers c.d := by
  refine (eq_of_relIndex_two (H := c.s.T) (K := c.e.T₁) (X := c.s.T ⊔ zpowers c.d)
    le_sup_left ?_ hH.hDef.2.1 ?_).symm
  · exact sup_le c.e.T_le (Subgroup.zpowers_le.mpr (y5_d_mem_T1 c))
  · intro hle
    exact y5_d_not_mem_T hH (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.d)))

theorem y5_T1_conj_d {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    ∀ x ∈ c.e.T₁, x * c.d * x⁻¹ = c.d ∨ x * c.d * x⁻¹ = c.s.fr.z * c.d := by
  intro x hx
  have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  have hz2 : orderOf c.s.fr.z = 2 := s3_z_order c.s hA
  have hu := Ctx5pre.u_facts c.toCtx5pre hz2
  have hdT1 : c.d ∈ c.e.T₁ := y5_d_mem_T1 c
  have hdCentA : c.d ∈ centralizer (c.s.fr.A : Set G) := by
    have h := c.d_mem
    simp only [C0, centIn, Subgroup.mem_inf] at h
    exact h.2
  have hwC0 : x * c.d * x⁻¹ ∈ C0 c.e := by
    simp only [C0, centIn, Subgroup.mem_inf]
    constructor
    · exact c.e.T₁.mul_mem (c.e.T₁.mul_mem hx hdT1) (c.e.T₁.inv_mem hx)
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha' : x⁻¹ * a * x ∈ c.s.fr.A := by
        have h := s3_conj_A c.s c.e hH.h32 (c.e.T₁.inv_mem hx) ha
        simpa using h
      have hdcomm : (x⁻¹ * a * x) * c.d = c.d * (x⁻¹ * a * x) :=
        (Subgroup.mem_centralizer_iff.mp hdCentA) (x⁻¹ * a * x) ha'
      calc a * (x * c.d * x⁻¹)
          = x * ((x⁻¹ * a * x) * c.d) * x⁻¹ := by group
        _ = x * (c.d * (x⁻¹ * a * x)) * x⁻¹ := by rw [hdcomm]
        _ = (x * c.d * x⁻¹) * a := by group
  have hd2 : c.d ^ 2 = 1 := y5_d_sq c
  have hw2 : (x * c.d * x⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hd2]
    group
  have hwne : x * c.d * x⁻¹ ≠ 1 := by
    intro h
    have hdne : c.d ≠ 1 := by
      intro hd1
      have hdord : orderOf c.d = 2 := c.d_order
      rw [hd1, orderOf_one] at hdord
      norm_num at hdord
    apply hdne
    have h' : x⁻¹ * (x * c.d * x⁻¹) * x = c.d := by group
    rw [h] at h'
    simpa using h'.symm
  have hword : orderOf (x * c.d * x⁻¹) = 2 := orderOf_eq_prime hw2 hwne
  have hzt_norm : c.e.T₁ ≤ Subgroup.normalizer (zt c.s : Set G) := by
    have h := c.e.sylow.1
    rwa [s3_cen_R_eq c.s hH.hS hH.hZ (s3_T_inf_centralizer c.s hH.h31)] at h
  have hwn : x * c.d * x⁻¹ ∉ closure {(c.d * c.s.t) ^ 2, c.s.t} := by
    rw [hu.2]
    intro hmem
    change x * c.d * x⁻¹ ∈ zt c.s at hmem
    have hdmem : c.d ∈ zt c.s := by
      have h := (Subgroup.mem_normalizer_iff.mp
        (hzt_norm (c.e.T₁.inv_mem hx)) (x * c.d * x⁻¹)).mp hmem
      have heq : x⁻¹ * (x * c.d * x⁻¹) * (x⁻¹)⁻¹ = c.d := by group
      rwa [heq] at h
    exact c.d_not_mem hdmem
  have hcases := d8_involution_outside (C := C0 c.e) (t := c.s.t) (d := c.d)
    (w := x * c.d * x⁻¹) c.intro5.gen c.intro5.dihedral c.s.t_order c.d_order hwC0 hword hwn
  rcases hcases with hw | hw
  · exact Or.inl hw
  · exact Or.inr (by rw [hu.2] at hw; exact hw)

end CFSG.OddStandard.HigherRank.YamadaG23
