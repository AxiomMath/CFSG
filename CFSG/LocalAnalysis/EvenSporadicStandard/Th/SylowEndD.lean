module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndP

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
  (hD : DHyp A Aa t D)

include H W W2 hD

theorem ThCyc.b_mem_normalizer : b ∈ normalizer ((W5 A t : Subgroup G) : Set G) :=
  (H.b_mem_Bp W W2).2

theorem ThCyc.b_conj_mem_D {d : G} (hd : d ∈ D) : b * d * b⁻¹ ∈ D :=
  hD.norm b (H.b_mem_normalizer W W2 hD) d hd

theorem ThCyc.D_theta_eq_one_iff {d : G} (hd : d ∈ D) : theta t d = 1 ↔ d ∈ Aa := by
  have hdBp : d ∈ Bp A t := H.D_le_Bp W W2 hD hd
  rw [H.theta_eq_one_iff W hdBp]
  constructor
  · intro hdW
    have hdC : d ∈ centralizer ((W5 A t : Subgroup G) : Set G) ⊓ centralizer (Aa : Set G) :=
      ⟨hdW, (hD.le_C hd).2⟩
    obtain ⟨x, hx, k, hk⟩ := (H.mem_centralizer_W5_inf_centralizer_Aa_iff W W2).1 hdC
    have htk : t ^ k ∈ D := by
      have : t ^ k = x⁻¹ * d := by rw [hk]; group
      rw [this]
      exact D.mul_mem (D.inv_mem (hD.Aa_le hx)) hd
    rcases zpow_eq_one_or_self H.sq_t k with h | h
    · rw [hk, h, mul_one]
      exact hx
    · exfalso
      rw [h] at htk
      have h1 : t = 1 := disjoint_def.1 hD.disjoint htk (mem_zpowers t)
      have := H.order_two
      rw [h1, orderOf_one] at this
      omega
  · intro hdAa
    exact (H.mem_centralizer_W5_iff W).2 ⟨d, W2.Aa_le hdAa, 0, by simp⟩

theorem ThCyc.D_sq_mem_Aa {d : G} (hd : d ∈ D) : d ^ 2 ∈ Aa := by
  have hdBp : d ∈ Bp A t := H.D_le_Bp W W2 hD hd
  have hd2 : d ^ 2 ∈ D := D.pow_mem hd 2
  rw [← H.D_theta_eq_one_iff W W2 hD hd2, sq, H.theta_mul W hdBp hdBp, ← sq]
  exact W.A_sq _ (H.theta_mem_A W hdBp)

theorem ThCyc.D_exists_theta_eq {a : G} (ha : a ∈ A) : ∃ d ∈ D, theta t d = a := by
  obtain ⟨c, hc, hca⟩ := H.exists_theta_eq_of_mem_inf_centralizer_Aa W W2 ha
  have hc' : c ∈ D ⊔ zpowers t := hD.sup_eq ▸ hc
  have hz : zpowers t ≤ normalizer (D : Set G) :=
    zpowers_le.2 (le_normalizer_of_conj_mem hD.norm (H.t_mem_normalizer W W2 hD))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D (zpowers t) hz] at hc'
  obtain ⟨d, hd, r, hr, rfl⟩ := hc'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
  refine ⟨d, hd, ?_⟩
  rw [← hca]
  simp only [theta]
  group

theorem ThCyc.D_alpha_mem {d : G} (hd : d ∈ D) : b * d * b⁻¹ * d⁻¹ ∈ Aa :=
  hD.BpC b (H.b_mem_Bp W W2) d (hD.le_C hd)

end

end CFSG.EvenSporadicStandard.ThStd
