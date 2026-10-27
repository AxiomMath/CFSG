module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Cfg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private lemma y7a_d_ne_one (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : d ≠ 1 := by
  intro hd
  have hord := h.d_ord
  rw [hd, orderOf_one] at hord
  omega

private lemma y7a_z_ne_d (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : z ≠ d := by
  intro hzd
  have hzt : z * t = t * z := h.cfg.t_cent z (y7a_z_mem_A h)
  have h1 : (z * t) ^ 2 = 1 := by
    rw [pow_two]
    calc (z * t) * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [hzt.symm]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [y7a_z_sq h, y7a_t_sq h, one_mul]
  have h2 : (d * t) ^ 2 = 1 := by rw [← hzd]; exact h1
  rw [h.cfg.u_sq] at h2
  exact h.cfg.z_ne h2

private lemma y7a_t_conj_zd (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    t * (z * d) * t⁻¹ = d := by
  calc t * (z * d) * t⁻¹ = t * (t * d * t⁻¹) * t⁻¹ := by rw [← y7a_tdt h]
    _ = (t * t) * d * (t⁻¹ * t⁻¹) := by group
    _ = d := by
      have htinv : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, y7a_t_sq h, inv_one]
      rw [y7a_t_sq h, htinv, one_mul, mul_one]

private lemma y7a_mem_centIn_iff (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {C : Subgroup G}
    (hCz : ∀ c ∈ C, c * z * c⁻¹ = z) {c : G} (hc : c ∈ C) :
    c ∈ centIn C V ↔ c * d * c⁻¹ = d := by
  unfold centIn
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  have hcz : c * z = z * c := by
    have := hCz c hc
    rwa [mul_inv_eq_iff_eq_mul] at this
  constructor
  · rintro ⟨-, hcent⟩
    have hcd : d * c = c * d := hcent d (y7a_d_mem_V h)
    rw [← hcd]
    group
  · intro hcd
    have hcd' : c * d = d * c := by
      have := hcd
      rwa [mul_inv_eq_iff_eq_mul] at this
    refine ⟨hc, fun v hv => ?_⟩
    rcases y7a_V_elems h v hv with rfl | rfl | rfl | rfl
    · simp
    · exact hcz.symm
    · exact hcd'.symm
    · calc (z * d) * c = z * (d * c) := by rw [mul_assoc]
        _ = z * (c * d) := by rw [hcd'.symm]
        _ = (z * c) * d := by rw [mul_assoc]
        _ = (c * z) * d := by rw [hcz.symm]
        _ = c * (z * d) := by rw [mul_assoc]

private lemma y7a_conj_d_elems (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {C : Subgroup G}
    (hCz : ∀ c ∈ C, c * z * c⁻¹ = z) (hCV : C ≤ normalizer (V : Set G)) {c : G} (hc : c ∈ C) :
    c * d * c⁻¹ = d ∨ c * d * c⁻¹ = z * d := by
  have hmemV : c * d * c⁻¹ ∈ V :=
    (Subgroup.le_set_normalizer_iff.mp hCV) c hc d (y7a_d_mem_V h)
  rcases y7a_V_elems h _ hmemV with h1 | hz | hd | hzd
  · exfalso
    have hh : d = 1 := by
      calc d = c⁻¹ * (c * d * c⁻¹) * c := by group
        _ = c⁻¹ * 1 * c := by rw [h1]
        _ = 1 := by group
    exact y7a_d_ne_one h hh
  · exfalso
    have hcz : c * z = z * c := by
      have := hCz c hc
      rwa [mul_inv_eq_iff_eq_mul] at this
    have hzcinv : c⁻¹ * z * c = z := by
      calc c⁻¹ * z * c = c⁻¹ * (z * c) := by rw [mul_assoc]
        _ = c⁻¹ * (c * z) := by rw [hcz.symm]
        _ = (c⁻¹ * c) * z := by rw [mul_assoc]
        _ = z := by rw [inv_mul_cancel, one_mul]
    have hh : d = z := by
      calc d = c⁻¹ * (c * d * c⁻¹) * c := by group
        _ = c⁻¹ * z * c := by rw [hz]
        _ = z := hzcinv
    exact (y7a_z_ne_d h).symm hh
  · exact Or.inl hd
  · exact Or.inr hzd

theorem y7a_index_two (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {C : Subgroup G} (htC : t ∈ C)
    (hCV : C ≤ normalizer (V : Set G)) (hCz : ∀ c ∈ C, c * z * c⁻¹ = z) :
    Nat.card ↥(centIn C V) * 2 = Nat.card ↥C ∧ C = centIn C V ⊔ zpowers t := by
  have hle : centIn C V ≤ C := by unfold centIn; exact inf_le_left
  have htK : t ∉ centIn C V := by
    rw [y7a_mem_centIn_iff h hCz htC]
    intro htd
    have hzd : z * d = 1 * d := by rw [one_mul, ← y7a_tdt h]; exact htd
    exact h.cfg.z_ne (mul_right_cancel hzd)
  have hdisj : ∀ b ∈ C, (t * b ∈ centIn C V) ∨ (b ∈ centIn C V) := by
    intro b hb
    by_cases hbK : b ∈ centIn C V
    · exact Or.inr hbK
    · left
      have hbd : b * d * b⁻¹ = z * d := by
        rcases y7a_conj_d_elems h hCz hCV hb with hbd | hbd
        · exact absurd ((y7a_mem_centIn_iff h hCz hb).mpr hbd) hbK
        · exact hbd
      rw [y7a_mem_centIn_iff h hCz (mul_mem htC hb)]
      calc (t * b) * d * (t * b)⁻¹ = t * (b * d * b⁻¹) * t⁻¹ := by group
        _ = t * (z * d) * t⁻¹ := by rw [hbd]
        _ = d := y7a_t_conj_zd h
  refine ⟨?_, ?_⟩
  · have hrel : (centIn C V).relIndex C = 2 :=
      (Subgroup.relIndex_eq_two_iff_exists_notMem_and' (H := centIn C V) (K := C)).mpr
        ⟨t, htC, htK, hdisj⟩
    have hcard := Subgroup.relIndex_mul_card (H := centIn C V) (K := C)
    rw [hrel, inf_eq_left.mpr hle] at hcard
    rw [Nat.mul_comm (Nat.card ↥(centIn C V)) 2]
    exact hcard
  · apply le_antisymm
    · intro c hc
      by_cases hcK : c ∈ centIn C V
      · exact Subgroup.mem_sup_left hcK
      · have hcd : c * d * c⁻¹ = z * d := by
          rcases y7a_conj_d_elems h hCz hCV hc with hcd | hcd
          · exact absurd ((y7a_mem_centIn_iff h hCz hc).mpr hcd) hcK
          · exact hcd
        have hct : c * t⁻¹ ∈ centIn C V := by
          rw [y7a_mem_centIn_iff h hCz (mul_mem hc (inv_mem htC))]
          have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (y7a_t_sq h)
          have htdt : t⁻¹ * d * t = z * d := by simpa [htinv] using y7a_tdt h
          calc (c * t⁻¹) * d * (c * t⁻¹)⁻¹ = c * (t⁻¹ * d * t) * c⁻¹ := by group
            _ = c * (z * d) * c⁻¹ := by rw [htdt]
            _ = (c * z * c⁻¹) * (c * d * c⁻¹) := by group
            _ = z * (z * d) := by rw [hCz c hc, hcd]
            _ = d := by rw [← mul_assoc, y7a_z_sq h, one_mul]
        rw [show c = (c * t⁻¹) * t by group]
        exact mul_mem (Subgroup.mem_sup_left hct)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr htC)

end CFSG.OddStandard.HigherRank.YamadaG23
