module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B8a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3d

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7b8b_B_le_H (c : Ctx7 G L) (hb : B5Std c) : c.s.fr.B ≤ c.s.H :=
  (s3_B_le_S c.s).trans ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS))

private lemma y7b8b_zpow_two_eq_one_or_self {x : G} (hx : x ^ 2 = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · left
    rw [orderOf_eq_one_iff.mp h1, one_zpow]
  · have hmod := zpow_mod_orderOf x k
    rw [h2] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← hmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
      simp
    · right
      rw [← hmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
      simp

theorem y7b_cs3_B (c : Ctx7 G L) (hb : B5Std c) {b : G} (hbB : b ∈ c.s.fr.B)
    (hcs : b ∈ y7bCS3 c) : ∃ e ∈ c.s.fr.E, ∃ f ∈ c.s.fr.F, b = e * f := by
  simp only [centralizerSection, Set.mem_setOf_eq] at hcs
  obtain ⟨-, -, hcomm⟩ := hcs
  have hbH : b ∈ c.s.H := y7b8b_B_le_H c hb hbB
  have hbA : b ∈ c.s.fr.A := by
    refine y7b_CF hb.hH b (s3_B_le_S c.s hbB) fun f hfF => ?_
    have hfBM : f ∈ c.s.fr.B ⊓ M3 c.s := by rw [y7b_B_inf_M3 c hb]; exact hfF
    obtain ⟨hfB, hfM3⟩ := Subgroup.mem_inf.mp hfBM
    have hbfV1 : ⁅b, f⁆ ∈ V1 c.e := by
      have h := (V1 c.e).inv_mem (hcomm f hfM3)
      rwa [commutatorElement_inv] at h
    have hbfH : ⁅b, f⁆ ∈ c.s.H := by
      rw [commutatorElement_def]
      exact c.s.H.mul_mem
        (c.s.H.mul_mem (c.s.H.mul_mem hbH (y7b8b_B_le_H c hb hfB)) (c.s.H.inv_mem hbH))
        (c.s.H.inv_mem (y7b8b_B_le_H c hb hfB))
    have hmem : ⁅b, f⁆ ∈ c.s.H ⊓ V1 c.e := Subgroup.mem_inf.mpr ⟨hbfH, hbfV1⟩
    rwa [y7b_H_inf_V1 c hb] at hmem
  exact (y7b_mem_EF hb.hH).mp (Subgroup.mem_inf.mpr ⟨hbA, hbB⟩)

theorem y7b_cs3_BM (c : Ctx7 G L) (hb : B5Std c) {y : G} (hy : y ∈ y7bBM c.s)
    (hcs : y ∈ y7bCS3 c) : ∃ e ∈ c.s.fr.E, ∃ m ∈ M3 c.s, y = e * m := by
  obtain ⟨b, hbB, m, hmM3, hy_eq⟩ := (y7b_mem_BM c hb).mp hy
  have hmM5 : m ∈ M5 c.e := by
    unfold M5
    exact Subgroup.mem_sup_left hmM3
  have hmCS3 : m ∈ y7bCS3 c := y7b_M6_le_CS3 c hb (y7b_M5_le_M6 c hb hmM5)
  have hbCS3 : b ∈ y7bCS3 c := by
    have h : y * m⁻¹ ∈ y7bCS3 c := (y7bCS3 c).mul_mem hcs ((y7bCS3 c).inv_mem hmCS3)
    rwa [show y * m⁻¹ = b from by rw [hy_eq]; group] at h
  obtain ⟨e, heE, f, hfF, hbf⟩ := y7b_cs3_B c hb hbB hbCS3
  have hfM3 : f ∈ M3 c.s := by
    have hfBM : f ∈ c.s.fr.B ⊓ M3 c.s := by rw [y7b_B_inf_M3 c hb]; exact hfF
    exact (Subgroup.mem_inf.mp hfBM).2
  refine ⟨e, heE, f * m, (M3 c.s).mul_mem hfM3 hmM3, ?_⟩
  rw [hy_eq, hbf]
  group

theorem y7b_E_quot (c : Ctx7 G L) (hb : B5Std c) {e₁ e₂ : G} (h₁ : e₁ ∈ c.s.fr.E)
    (h₁' : e₁ ∉ M3 c.s) (h₂ : e₂ ∈ c.s.fr.E) (h₂' : e₂ ∉ M3 c.s) :
    e₁⁻¹ * e₂ ∈ M3 c.s := by
  have hE_le_B : c.s.fr.E ≤ c.s.fr.B :=
    (le_sup_left.trans (le_of_eq (y7b_EF_eq hb.hH))).trans inf_le_right
  have hEM3 : c.s.fr.E ⊓ M3 c.s = cen c.s.fr.B := by
    have h1 : c.s.fr.E ⊓ M3 c.s = c.s.fr.E ⊓ (c.s.fr.B ⊓ M3 c.s) := by
      rw [← inf_assoc, inf_eq_left.mpr hE_le_B]
    rw [h1, y7b_B_inf_M3 c hb, y7b_E_inf_F hb.hH]
  have hcard : Nat.card ↥(c.s.fr.E) = 2 * Nat.card ↥(c.s.fr.E ⊓ M3 c.s) := by
    rw [y7b_card_E hb.hH, hEM3, y7b_card_V hb.hH]
  have hrel : (c.s.fr.E ⊓ M3 c.s).relIndex c.s.fr.E = 2 :=
    relIndex_eq_of_card_eq_mul inf_le_left hcard
  have hxM : e₁ ∉ c.s.fr.E ⊓ M3 c.s := fun hx => h₁' (Subgroup.mem_inf.mp hx).2
  rcases mem_or_mem_of_relIndex_two inf_le_left hrel h₁ hxM h₂ with h | h
  · exact absurd (Subgroup.mem_inf.mp h).2 h₂'
  · exact (Subgroup.mem_inf.mp h).2

theorem y7b_g_comm_e0_not_mem_V1 (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ⁅c.g, c.s.fr.a₁ * c.s.fr.b₁ * c.s.fr.a₂⁆ ∉ V1 c.e := by
  intro h
  rw [y7b_g_comm_e0 c hb hRT] at h
  obtain ⟨hb12, hz, hw1, hzne, hwz, -⟩ := y56_v0 hb.hH
  have hmem_cen : c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z ∈ cen c.s.fr.B :=
    (cen c.s.fr.B).mul_mem hb12 hz
  have hmem_H : c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z ∈ c.s.H :=
    y7b8b_B_le_H c hb (Subgroup.mem_inf.mp hmem_cen).1
  have hmem : c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z ∈ c.s.fr.Z := by
    have h' : c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z ∈ c.s.H ⊓ V1 c.e :=
      Subgroup.mem_inf.mpr ⟨hmem_H, h⟩
    rwa [y7b_H_inf_V1 c hb] at h'
  rw [SFrame.Z, Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hzsq : c.s.fr.z ^ 2 = 1 := (s3_srel hb.hH.hS hb.hH.hZ c.s).z_sq
  have hzz : c.s.fr.z * c.s.fr.z = 1 := by rw [← pow_two]; exact hzsq
  rcases y7b8b_zpow_two_eq_one_or_self hzsq k with hk1 | hkz
  · refine hwz ?_
    have hw : c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z = 1 := by rw [← hk, hk1]
    have h' : c.s.fr.b₁ * c.s.fr.b₂ = (c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z) * c.s.fr.z := by
      rw [mul_assoc, hzz, mul_one]
    rwa [hw, one_mul] at h'
  · refine hw1 ?_
    have hw : c.s.fr.b₁ * c.s.fr.b₂ * c.s.fr.z = c.s.fr.z := by rw [← hk, hkz]
    exact mul_right_cancel (by rw [hw, one_mul])

end CFSG.OddStandard.HigherRank.YamadaG23
