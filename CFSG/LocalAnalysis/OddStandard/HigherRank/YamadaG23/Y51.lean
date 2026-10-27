module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec5S
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YDihedral
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSetBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YD8
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem sec51_of (hDef : Fusion3Def) (h32 : Fusion32) (hZ : OddCentre) : Sec51 := by
  intro G _ _ L hS hL c hRT
  have hLF : LFactsA c.s := lfactsA_of_setting hS (hZ G L hS hL) c.s
  have hdef := hDef G L hS hL c.s c.e
  have hf32 : c.e.Fact32 := h32 G L hS hL c.s c.e
  have hz2 : orderOf c.s.fr.z = 2 := s3_z_order c.s hLF
  have hu := Ctx5pre.u_facts c hz2
  have h4 : (c.d * c.s.t) ^ 4 = 1 := by
    rw [← hu.1]
    exact pow_orderOf_eq_one _
  have hrel := d8_rel c.s.t_order c.d_order h4 hu.2
  have hzsq : c.s.fr.z * c.s.fr.z = 1 := by
    simpa [hz2, pow_two] using pow_orderOf_eq_one c.s.fr.z
  have hzne : c.s.fr.z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  have hd2 : c.d ^ 2 = 1 := by
    simpa [c.d_order] using pow_orderOf_eq_one c.d
  have hdne : c.d ≠ 1 := by
    intro h
    have hdord : orderOf c.d = 2 := c.d_order
    rw [h, orderOf_one] at hdord
    norm_num at hdord
  obtain ⟨-, g, hgT, hgR, hgA, hg2⟩ := hdef.1 hRT
  have hgT1 : g ∈ c.e.T₁ := c.e.T_le hgT
  have hgt : g * c.s.t = c.s.t * g := s3_comm_t_of_mem_T c.s hgT
  have hgz : g * c.s.fr.z * g⁻¹ = c.s.fr.z := s3_conj_z c.s hLF c.e hf32 hgT1
  have hg_zt : ∀ y ∈ zt c.s, g * y * g⁻¹ = y := by
    intro y hy
    rw [s3_mem_zt_iff c.s hLF] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · simp
    · exact hgz
    · calc g * c.s.t * g⁻¹ = c.s.t * g * g⁻¹ := by rw [hgt]
        _ = c.s.t := by group
    · calc g * (c.s.fr.z * c.s.t) * g⁻¹
          = (g * c.s.fr.z * g⁻¹) * (g * c.s.t * g⁻¹) := by group
        _ = c.s.fr.z * c.s.t := by rw [hgz, hgt]; group
  have hg_zt_inv : ∀ y ∈ zt c.s, g⁻¹ * y * g = y := by
    intro y hy
    have h := hg_zt y hy
    exact (calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = g⁻¹ * y * g := by rw [h]).symm
  have hdT1 : c.d ∈ c.e.T₁ := by
    have h := c.d_mem
    simp only [C0, centIn, Subgroup.mem_inf] at h
    exact h.1
  have hdCentA : c.d ∈ centralizer (c.s.fr.A : Set G) := by
    have h := c.d_mem
    simp only [C0, centIn, Subgroup.mem_inf] at h
    exact h.2
  have hmain : ∀ g' : G, g' * c.d * g'⁻¹ = c.d →
      (g' ^ 2 = 1 ∨ g' ^ 2 = c.s.t) → g' ^ 2 = 1 := by
    intro g' hcomm hg'2
    rcases hg'2 with h | h
    · exact h
    · exfalso
      have hgd : g' * c.d = c.d * g' := by
        have h' := congrArg (fun x => x * g') hcomm
        simpa [mul_assoc] using h'
      have hconj : c.d * g' * c.d⁻¹ = g' := by
        rw [← hgd]; group
      have hsq : c.d * g' ^ 2 * c.d⁻¹ = g' ^ 2 := by
        rw [← conj_pow, hconj]
      have hdt : c.d * c.s.t * c.d⁻¹ = c.s.t := by
        rw [← h]
        exact hsq
      have hzt : c.s.fr.z * c.s.t = c.s.t := by
        rw [← hrel.1]
        exact hdt
      have hz1 : c.s.fr.z = 1 := by
        have h' := congrArg (fun x => x * c.s.t⁻¹) hzt
        simpa [mul_assoc] using h'
      exact hzne hz1
  have hwC0 : g * c.d * g⁻¹ ∈ C0 c.e := by
    simp only [C0, centIn, Subgroup.mem_inf]
    constructor
    · exact c.e.T₁.mul_mem (c.e.T₁.mul_mem hgT1 hdT1) (c.e.T₁.inv_mem hgT1)
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha' : g⁻¹ * a * g ∈ c.s.fr.A := by
        have h := s3_conj_A c.s c.e hf32 (c.e.T₁.inv_mem hgT1) ha
        simpa using h
      have hdcomm : (g⁻¹ * a * g) * c.d = c.d * (g⁻¹ * a * g) :=
        (Subgroup.mem_centralizer_iff.mp hdCentA) (g⁻¹ * a * g) ha'
      calc a * (g * c.d * g⁻¹)
          = g * ((g⁻¹ * a * g) * c.d) * g⁻¹ := by group
        _ = g * (c.d * (g⁻¹ * a * g)) * g⁻¹ := by rw [hdcomm]
        _ = (g * c.d * g⁻¹) * a := by group
  have hw2 : (g * c.d * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hd2]
    group
  have hwne : g * c.d * g⁻¹ ≠ 1 := by
    intro h
    apply hdne
    have h' : g⁻¹ * (g * c.d * g⁻¹) * g = c.d := by group
    rw [h] at h'
    simpa using h'.symm
  have hword : orderOf (g * c.d * g⁻¹) = 2 := orderOf_eq_prime hw2 hwne
  have hwn : g * c.d * g⁻¹ ∉ closure {(c.d * c.s.t) ^ 2, c.s.t} := by
    rw [hu.2]
    intro hmem
    change g * c.d * g⁻¹ ∈ zt c.s at hmem
    have hconj : g⁻¹ * (g * c.d * g⁻¹) * g = c.d := by group
    have hmem' : c.d ∈ zt c.s := by
      rw [← hconj]
      rw [hg_zt_inv (g * c.d * g⁻¹) hmem]
      exact hmem
    exact c.d_not_mem hmem'
  have hcases := d8_involution_outside (C := C0 c.e) (t := c.s.t) (d := c.d)
    (w := g * c.d * g⁻¹) c.intro5.gen c.intro5.dihedral c.s.t_order c.d_order hwC0 hword hwn
  rcases hcases with hw | hw
  · exact ⟨g, hgT, hgR, hgA, hmain g hw hg2, hw⟩
  · rw [hu.2] at hw
    have htR : c.s.t ∈ c.s.R := s3_t_mem_R c.s
    have ht2 : c.s.t ^ 2 = 1 := by simpa [c.s.t_order] using pow_orderOf_eq_one c.s.t
    have hg'T : c.s.t * g ∈ c.s.T := c.s.T.mul_mem (s3_t_mem_T c.s) hgT
    have hg'R : c.s.t * g ∉ c.s.R := by
      intro h
      apply hgR
      have hmem : c.s.t⁻¹ * (c.s.t * g) ∈ c.s.R := c.s.R.mul_mem (c.s.R.inv_mem htR) h
      simpa using hmem
    have hg'A : ActsAs L (c.s.t * g) c.s.fr'.σ := by
      intro x
      obtain ⟨y, hy1, hy2⟩ := hgA x
      refine ⟨y, ?_, hy2⟩
      have htcomm : (y : G) * c.s.t = c.s.t * (y : G) := s3_comm_t_of_mem_L c.s y.2
      calc (y : G) = c.s.t * (y : G) * c.s.t⁻¹ := by rw [← htcomm]; group
        _ = c.s.t * (g * x * g⁻¹) * c.s.t⁻¹ := by rw [hy1]
        _ = (c.s.t * g) * x * (c.s.t * g)⁻¹ := by group
    have htg2 : (c.s.t * g) ^ 2 = g ^ 2 := by
      calc (c.s.t * g) ^ 2 = c.s.t * (g * c.s.t) * g := by rw [pow_two]; group
        _ = c.s.t * (c.s.t * g) * g := by rw [hgt]
        _ = c.s.t ^ 2 * g ^ 2 := by rw [pow_two, pow_two]; group
        _ = g ^ 2 := by rw [ht2, one_mul]
    have hg'2 : (c.s.t * g) ^ 2 = 1 ∨ (c.s.t * g) ^ 2 = c.s.t := by
      rcases hg2 with h | h
      · exact Or.inl (by rw [htg2, h])
      · exact Or.inr (by rw [htg2, h])
    have hzt : c.s.t * c.s.fr.z * c.s.t⁻¹ = c.s.fr.z := by
      have hcomm := s3_comm_t_of_mem_L c.s (s3_z_mem_L c.s)
      rw [← hcomm]; group
    have hg'd : (c.s.t * g) * c.d * (c.s.t * g)⁻¹ = c.d := by
      calc (c.s.t * g) * c.d * (c.s.t * g)⁻¹
          = c.s.t * (g * c.d * g⁻¹) * c.s.t⁻¹ := by group
        _ = c.s.t * (c.s.fr.z * c.d) * c.s.t⁻¹ := by rw [hw]
        _ = (c.s.t * c.s.fr.z * c.s.t⁻¹) * (c.s.t * c.d * c.s.t⁻¹) := by group
        _ = c.s.fr.z * (c.s.fr.z * c.d) := by rw [hzt, hrel.2]
        _ = c.d := by rw [← mul_assoc, hzsq, one_mul]
    exact ⟨c.s.t * g, hg'T, hg'R, hg'A, hmain (c.s.t * g) hg'd hg'2, hg'd⟩

end CFSG.OddStandard.HigherRank.YamadaG23

end
