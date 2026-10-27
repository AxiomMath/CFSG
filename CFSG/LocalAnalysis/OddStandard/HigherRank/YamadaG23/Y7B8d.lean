module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B8c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7l
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_not_A_le_K (c : Ctx7 G L) (hb : B5Std c) :
    ¬ c.s.fr.A ≤ centralizerSection (y7bBM c.s) (M3 c.s) := by
  intro hA
  set K : Subgroup G := centralizerSection (y7bBM c.s) (M3 c.s)
  have hS : c.s.fr.S ≤ K := y7b_S_le_K_of_A c hb hA
  obtain ⟨k, hkN, hk3, hk1, -, hfpf, hknorm⟩ := y7b_exists_k c hb
  have hkH : k ∈ normIn c.s.H c.s.fr.B :=
    ⟨s3_L_le_H c.s hb.hH.hS hkN.1, hkN.2⟩
  obtain ⟨hkBMn, hkM3n⟩ := y7b_normIn_norm_BM c hb hkH
  have hkK : k ∈ normalizer (K : Set G) :=
    mem_normalizer_centralizerSection hkBMn hkM3n
  have hk'K : k⁻¹ ∈ normalizer (K : Set G) := (normalizer (K : Set G)).inv_mem hkK
  have hk3' : k * k * k = 1 := by simpa [pow_three'] using hk3
  have hksq : k⁻¹ * k⁻¹ = k := by
    rw [← mul_inv_rev]
    exact (eq_inv_of_mul_eq_one_right hk3').symm
  obtain ⟨m₀, -, -, hmE, hmM3⟩ := y7b_exists_seed c hb
  have hE_le_B : c.s.fr.E ≤ c.s.fr.B := by
    calc c.s.fr.E ≤ c.s.fr.E ⊔ c.s.fr.F := le_sup_left
      _ = c.s.fr.A ⊓ c.s.fr.B := y7b_EF_eq hb.hH
      _ ≤ c.s.fr.B := inf_le_right
  have hmBM : ⁅m₀, c.s.t⁆ ∈ y7bBM c.s := Subgroup.mem_sup_left (hE_le_B hmE)
  have hclaim : ∀ s ∈ c.s.fr.S, ∃ b' ∈ c.s.fr.B, s * k * s⁻¹ = k * b' := by
    intro s hs
    have hsN : s ∈ normIn L c.s.fr.B :=
      ⟨s3_S_le_L c.s hs, (y7b_S_le_normIn c hb hs).2⟩
    obtain ⟨b', hb'B, h | h⟩ := hknorm s hsN
    · exact ⟨b', hb'B, h⟩
    · exfalso
      have hsK : s ∈ K := hS hs
      have hs'K : s⁻¹ ∈ K := K.inv_mem hsK
      have hκ : s * k * s⁻¹ * k⁻¹ ∈ K := by
        have h1 : k * s⁻¹ * k⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp hkK s⁻¹).mp hs'K
        have h2 := K.mul_mem hsK h1
        rwa [show s * (k * s⁻¹ * k⁻¹) = s * k * s⁻¹ * k⁻¹ from by group] at h2
      have hb'K : b' ∈ K := y7b_B_le_K c hb hb'B
      have hkb' : k⁻¹ * b' * k ∈ K := by
        have h2 := (Subgroup.mem_normalizer_iff.mp hk'K b').mp hb'K
        simpa using h2
      have hkkK : k⁻¹ * k⁻¹ ∈ K := by
        have h2 := K.mul_mem (K.inv_mem hkb') hκ
        rw [h] at h2
        rwa [show (k⁻¹ * b' * k)⁻¹ * (k⁻¹ * b' * k⁻¹) = k⁻¹ * k⁻¹ from by group] at h2
      have hkK' : k ∈ K := by rwa [hksq] at hkkK
      have hBMleM3 : y7bBM c.s ≤ M3 c.s := by
        intro u hu
        have hcomm : ⁅u⁻¹, k⁆ ∈ M3 c.s := hkK'.2.2 u⁻¹ ((y7bBM c.s).inv_mem hu)
        rw [show ⁅u⁻¹, k⁆ = u⁻¹ * (k * u * k⁻¹) from by
          simp only [commutatorElement_def]; group] at hcomm
        exact hfpf u hu hcomm
      exact hmM3 (hBMleM3 hmBM)
  have hk'invN : k⁻¹ ∈ normalizer (c.s.fr.S : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    intro s hs
    obtain ⟨b', hb'B, hb'⟩ := hclaim s hs
    have hconv : k⁻¹ * s * (k⁻¹)⁻¹ = b' * s := by
      calc k⁻¹ * s * (k⁻¹)⁻¹ = k⁻¹ * (s * k * s⁻¹) * s := by group
        _ = k⁻¹ * (k * b') * s := by rw [hb']
        _ = b' * s := by group
    rw [hconv]
    exact c.s.fr.S.mul_mem (s3_B_le_S c.s hb'B) hs
  have hkN_S : k ∈ normalizer (c.s.fr.S : Set G) := by
    simpa using (normalizer (c.s.fr.S : Set G)).inv_mem hk'invN
  have hkS : k ∈ c.s.fr.S := le_of_eq (y7b_NL_S hb.hH) ⟨hkN.1, hkN_S⟩
  exact hk1 (eq_one_of_isPGroup_of_pow_prime (p := 2) (q := 3) (by norm_num)
    (s3_isPGroup_S c.s) hkS hk3)

theorem y7b_A_acts_BM (c : Ctx7 G L) (hb : B5Std c) :
    ∃ a ∈ c.s.fr.A, ∃ u ∈ y7bBM c.s, ⁅a, u⁆ ∉ M3 c.s := by
  by_contra h
  push_neg at h
  apply y7b_not_A_le_K c hb
  intro a ha
  have haN : a ∈ normIn c.s.H c.s.fr.B := y7b_S_le_normIn c hb (s3_A_le_S c.s ha)
  obtain ⟨haBM, haM3⟩ := y7b_normIn_norm_BM c hb haN
  refine ⟨haBM, haM3, fun u hu => ?_⟩
  have hcomm : ⁅a, u⁆ ∈ M3 c.s := h a ha u hu
  have hinv : (⁅a, u⁆)⁻¹ = ⁅u, a⁆ := commutatorElement_inv a u
  rw [← hinv]
  exact (M3 c.s).inv_mem hcomm

end CFSG.OddStandard.HigherRank.YamadaG23
