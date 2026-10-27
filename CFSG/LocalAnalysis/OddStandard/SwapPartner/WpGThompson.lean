module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGSylow
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapThompson

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

theorem false_of_outer_conjugates {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} {ι : Perm (Fin 10) →* G} (hC : CentData z ι)
    (hfr : IsConj z (ι τ₀)) (hP2 : ¬ IsConj z (z * ι τ₀))
    (hAll : ∀ c : G, IsConj z c → c ∈ centralizer ({z * ι τ₀} : Set G) →
      pairOrder c (z * ι τ₀) = N10 1)
    (Nhat : Subgroup G) (hNidx : Nhat.relIndex (centralizer ({z * ι τ₀} : Set G)) = 2)
    (hout : ∀ c : G, IsConj z c → c ∈ centralizer ({z * ι τ₀} : Set G) → c ∉ Nhat) :
    False := by
  obtain ⟨Q, hQ⟩ := exists_goodQ
  have hT2 : IsPGroup 2 (Tgrp z ι Q) := Tgrp_isPGroup hC hQ.pgroup
  have hTC : Tgrp z ι Q ≤ centralizer ({z * ι τ₀} : Set G) := Tgrp_le_centralizer_x₂ hC hQ
  obtain ⟨T₂, hTT₂, hT₂C, h2, hodd⟩ := exists_sylow_ge hT2 hTC
  have hN : normalizer (T₂ : Set G) ≤ centralizer ({z * ι τ₀} : Set G) :=
    normalizer_le_centralizer_x₂ hC hQ hfr hP2 hAll hTT₂ hT₂C h2
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp h2
  have hcard : T₂.relIndex (centralizer ({z * ι τ₀} : Set G)) * Nat.card T₂ =
      Nat.card (centralizer ({z * ι τ₀} : Set G)) := by
    have := Subgroup.relIndex_mul_card (H := T₂) (K := centralizer ({z * ι τ₀} : Set G))
    rwa [inf_of_le_left hT₂C] at this
  have hHcard : ¬ 2 ^ (a + 1) ∣ Nat.card (centralizer ({z * ι τ₀} : Set G)) := by
    intro hdvd
    rw [← hcard, ha, pow_succ, mul_comm (T₂.relIndex _) (2 ^ a)] at hdvd
    exact hodd (Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num) a) hdvd)
  have hTidx : ¬ 2 ∣ T₂.index := not_two_dvd_index_of_normalizer_le h2 hN ha hHcard
  have hzC : z ∈ centralizer ({z * ι τ₀} : Set G) := z_mem_centralizer_x₂ hC
  have hzT₂ : z ∈ T₂ := hTT₂ (z_mem_Tgrp (z := z) (ι := ι) Q)
  have hzN : z ∉ Nhat := hout z (IsConj.refl z) hzC
  have hrel : Nhat.relIndex T₂ = 2 := by
    have hle : Nhat.relIndex T₂ ≤ Nhat.relIndex (centralizer ({z * ι τ₀} : Set G)) :=
      Subgroup.relIndex_le_of_le_right hT₂C (by rw [hNidx]; norm_num)
    have hne : Nhat.relIndex T₂ ≠ 1 := by
      intro h1
      exact hzN (Subgroup.relIndex_eq_one.mp h1 hzT₂)
    have hpos : Nhat.relIndex T₂ ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hUidx : (Nhat ⊓ T₂).relIndex T₂ = 2 := by
    rw [Subgroup.inf_relIndex_right]; exact hrel
  refine false_of_thompson_involution hnonab h2 hTidx inf_le_right hUidx hC.order hzT₂
    (fun hzU => hzN hzU.1) ?_
  intro g hg
  have hgT₂ : g⁻¹ * z * g ∈ T₂ := hg.2
  have hconj : IsConj z (g⁻¹ * z * g) := isConj_iff.mpr ⟨g⁻¹, by simp⟩
  exact hout _ hconj (hT₂C hgT₂) hg.1

end CFSG.OddStandard.AltStdSec.SwapPartner
