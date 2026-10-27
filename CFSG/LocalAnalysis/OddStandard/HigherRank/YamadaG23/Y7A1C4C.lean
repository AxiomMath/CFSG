module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1OddN
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Core
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1KF
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1RegD
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Two

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7a_C4_conj_C1 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    ∀ w ∈ C4 c.s, ∀ u ∈ C1 c.e, w * u * w⁻¹ ∈ C1 c.e := by
  have hEC0 : c.s.fr.E ⊔ C0 c.e ≤ C1 c.e :=
    sup_le ((s3_E_le_A c.s).trans le_sup_left) le_sup_right
  intro w hw u hu
  have hcomm : ⁅u, w⁆ ∈ c.s.fr.E ⊔ C0 c.e :=
    y56_comm_C1_C4 c.toCtx5 hH (Subgroup.commutator_mem_commutator hu hw)
  have hwu : ⁅w, u⁆ ∈ C1 c.e := by
    rw [← commutatorElement_inv]
    exact (C1 c.e).inv_mem (hEC0 hcomm)
  have he : w * u * w⁻¹ = ⁅w, u⁆ * u := by
    rw [commutatorElement_def]; group
  rw [he]
  exact (C1 c.e).mul_mem hwu hu

private theorem y7a_mem_Z_eq_one_or (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (x : G)
    (hx : x ∈ c.s.fr.Z) : x = 1 ∨ x = f3phi c.s c.d := by
  have hz2 : c.s.fr.z ^ 2 = 1 := by
    rw [pow_two]
    exact y7a_z_sq (c.y7acfg hH)
  rw [SFrame.Z] at hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : c.s.fr.z ^ (2 : ℤ) = 1 := by simpa using hz2
  rw [zpow_eq_zpow_emod m h2]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left; rw [h]; simp
  · right
    rw [h]
    simpa using (y56_phi_d c.toCtx5 hH).symm

theorem y7a_C4_le_X (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    C4 c.s ≤ y7aX c := by
  rw [← y7a_NC1_eq c hH hF]
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact y7a_C4_conj_C1 c hH w hw u hu
  · intro hu
    have h := y7a_C4_conj_C1 c hH w⁻¹ ((C4 c.s).inv_mem hw) (w * u * w⁻¹) hu
    have he : w⁻¹ * (w * u * w⁻¹) * (w⁻¹)⁻¹ = u := by group
    rwa [he] at h

theorem y7a_C4_le_C6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    C4 c.s ≤ C6 c.e := by
  obtain ⟨ψ, lab, P, hP⟩ := y7a_reg_data c hH hF
  obtain ⟨N₃, hN⟩ := y7a_exists_N3 hH
  obtain ⟨k, hkK, hk3, hfpf⟩ := y7a_exists_k_E hH
  have hkA : k ∈ normIn L c.s.fr.A := hkK.1
  have hkE : k ∈ normIn L c.s.fr.E := hkK.2
  have hkA1 : k ^ (3 ^ 1) ∈ c.s.fr.A := by
    rw [show (3 : ℕ) ^ 1 = 3 by norm_num, hk3]
    exact Subgroup.one_mem _
  have hkN₃ : k ∈ N₃ := hN.char k hkA 1 hkA1
  have hkX : k ∈ y7aX c := y7a_Y_le_X c hH (s5_NLA_le_Y c.toCtx5 hH hkA)
  have hkN : k ∈ e4N c.s := y56_NL_le_N hH hkE
  have hcand := y56_C4_cand c.toCtx5 hH
  have hC4Y : C4 c.s ≤ e4Y c.s := hcand.2.1
  have hdC4 : c.d ∈ C4 c.s := hcand.2.2.2.2.2
  have hQle : e4Q c.s ≤ C1 c.e :=
    sup_le ((s3_E_le_A c.s).trans le_sup_left)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (y7a_t_mem_C0 (c.y7acfg hH))))
  have hkF : ∀ f ∈ c.s.fr.E, k * f * k⁻¹ ∈ c.s.fr.E :=
    fun f hf => (Subgroup.mem_normalizer_iff.mp hkE.2 f).mp hf
  have hdD : c.d ∈ C6 c.e := y7a_C1_le_C6 c hH hF (Subgroup.mem_sup_right c.d_mem)
  refine y7a_core (W := C4 c.s) (D := C6 c.e) (F := c.s.fr.E) (Z := c.s.fr.Z)
    (φ := f3phi c.s) (k := k) (d := c.d) hk3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfpf
    (y7a_mem_Z_eq_one_or c hH) hdD hdC4 ?_ ?_
  · exact fun w hw => hcand.2.2.1 k hkE w hw
  · exact y7a_C6_normal c hH hF k hkX
  · exact fun w hw => y56_phi_mem hH w (hC4Y hw)
  · exact fun w hw w' hw' => y56_phi_mul hH w (hC4Y hw) w' (hC4Y hw')
  · exact y56_phi_conj hH k hkN
  · exact y56_E_sq hH
  · exact y56_E_comm hH
  · exact hkF
  · intro w hw hφw
    have hwX0 : w ∈ e4X0 c.s := (y56_phi_eq_one hH w (hC4Y hw)).mp hφw
    have hwQ : w ∈ e4Q c.s := by
      rw [← hcand.2.2.2.1]
      exact Subgroup.mem_inf.mpr ⟨hw, hwX0⟩
    exact y7a_C1_le_C6 c hH hF (hQle hwQ)
  · intro w hw
    have hwX : w ∈ y7aX c := y7a_C4_le_X c hH hF hw
    have hwC4 : k * w * k⁻¹ ∈ C4 c.s := hcand.2.2.1 k hkE w hw
    have hcomC4 : ⁅k, w⁆ ∈ C4 c.s := by
      rw [commutatorElement_def]
      exact (C4 c.s).mul_mem hwC4 ((C4 c.s).inv_mem hw)
    have hsq : (⁅k, w⁆ ^ 2) ^ 2 = 1 :=
      y56_Q_sq hH (⁅k, w⁆ ^ 2) (y56_Y_sq c.toCtx5 hH ⁅k, w⁆ (hC4Y hcomC4))
    have h4 : ⁅k, w⁆ ^ (2 ^ 2) = 1 := by
      rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul]
      exact hsq
    simpa [commutatorElement_def] using
      y7a_comm_in_C6 c hH hF hP hN hkN₃ hwX (j := 2) h4

end CFSG.OddStandard.HigherRank.YamadaG23
