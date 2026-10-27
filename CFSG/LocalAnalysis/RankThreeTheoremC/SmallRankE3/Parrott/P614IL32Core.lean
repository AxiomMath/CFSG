module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Parab
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IIndex
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Point

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z b : G} {f : ↥K →* GL32}

theorem L32Data.z_pow (h : L32Data M B H S K z b f) : z ^ 3 = 1 := by
  rw [← h.z_order]
  exact pow_orderOf_eq_one z

theorem L32Data.z_mem_H (h : L32Data M B H S K z b f) : z ∈ H := h.K_le h.z_mem_K

theorem L32Data.exists_core_not_comm (h : L32Data M B H S K z b f) :
    ∃ o ∈ pCoreOf 2 H, o * z ≠ z * o := by
  by_contra hcon
  push Not at hcon
  exact h.z_not_mem (h.charTwo H h.twoLocal ⟨h.z_mem_H,
    mem_centralizer_iff.2 fun o ho => hcon o ho⟩)

theorem coprime_three_of_isPGroup_two {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    Nat.Coprime 3 (Nat.card Q) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem L32Data.stage620iii_of_block (h : L32Data M B H S K z b f) {A₀ B₀ : Subgroup G}
    (hAB : A₀ ≤ B₀) (hBW : B₀ ≤ omegaCenter (K ⊓ pCoreOf 2 H))
    (hXB : K ⊔ pCoreOf 2 H ≤ normalizer (B₀ : Set G)) (hKA : K ≤ centralizer (A₀ : Set G))
    (hKW : ∀ w ∈ K ⊓ pCoreOf 2 H, ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ B₀)
    (h8 : A₀.relIndex B₀ = 8)
    (hker : ∀ g ∈ K ⊔ pCoreOf 2 H, (∀ u ∈ B₀, g * u * g⁻¹ * u⁻¹ ∈ A₀) → g ∈ pCoreOf 2 H) :
    Stage620iii H S z := by
  set O := pCoreOf 2 H
  have hz3 := h.z_pow
  have hzK := h.z_mem_K
  have hBO : B₀ ≤ O := hBW.trans ((omegaCenter_le _).trans inf_le_right)
  have hB₀2 : IsPGroup 2 B₀ := h.isPGroup_core.to_le hBO
  have hzB₀ : z ∈ normalizer (B₀ : Set G) := hXB (mem_sup_left hzK)
  have hAc : A₀ ≤ centralizer ({z} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hKA hzK)) a ha)
  have hne : ∃ u ∈ B₀, u * z ≠ z * u := by
    by_contra hcon
    push Not at hcon
    refine h.z_not_mem (hker z (mem_sup_left hzK) fun u hu => ?_)
    have e : z * u * z⁻¹ * u⁻¹ = 1 := by
      rw [← hcon u hu]
      group
    rw [e]
    exact one_mem _
  have hB4 : (centralizer ({z} : Set G)).relIndex B₀ = 4 :=
    relIndex_centralizer_eq_four_of_section hB₀2 hz3 hzB₀ (fun a ha => hAc ha) h8 hne
  have hzO : z ∈ normalizer (O : Set G) := h.H_le h.z_mem_H
  have hzKO : z ∈ normalizer ((K ⊓ O : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨h.K_normal h.z_mem_H, hzO⟩
  have hcov : ∀ o ∈ O, ∃ u ∈ B₀, u⁻¹ * o ∈ centralizer ({z} : Set G) := by
    intro o ho
    have hoH : o ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H ho
    have hc1 : z * o * z⁻¹ * o⁻¹ ∈ K ⊓ O := by
      refine ⟨?_, O.mul_mem ((mem_normalizer_iff.1 hzO o).1 ho) (O.inv_mem ho)⟩
      have h1 : o * z⁻¹ * o⁻¹ ∈ K := (mem_normalizer_iff.1 (h.K_normal hoH) _).1 (K.inv_mem hzK)
      have e : z * o * z⁻¹ * o⁻¹ = z * (o * z⁻¹ * o⁻¹) := by group
      rw [e]
      exact K.mul_mem hzK h1
    obtain ⟨q₁, hq₁, hq₁o⟩ := exists_mul_mem_centralizer_of_coprime hz3 hzKO
      (coprime_three_of_isPGroup_two (h.isPGroup_core.to_le inf_le_right)) hc1
    have hw : q₁⁻¹ ∈ K ⊓ O := (K ⊓ O).inv_mem hq₁
    have hc2 : z * q₁⁻¹ * z⁻¹ * q₁⁻¹⁻¹ ∈ B₀ := by
      have := B₀.inv_mem (hKW q₁⁻¹ hw z hzK)
      have e : (q₁⁻¹ * z * q₁⁻¹⁻¹ * z⁻¹)⁻¹ = z * q₁⁻¹ * z⁻¹ * q₁⁻¹⁻¹ := by group
      rwa [e] at this
    obtain ⟨q₂, hq₂, hq₂w⟩ := exists_mul_mem_centralizer_of_coprime hz3 hzB₀
      (coprime_three_of_isPGroup_two hB₀2) hc2
    refine ⟨q₂⁻¹, B₀.inv_mem hq₂, ?_⟩
    have e : q₂⁻¹⁻¹ * o = (q₂ * q₁⁻¹) * (q₁ * o) := by group
    rw [e]
    exact mul_mem hq₂w hq₁o
  have hle : (centralizer ({z} : Set G)).relIndex O ≤ 4 :=
    hB4 ▸ relIndex_centralizer_le_of_forall_mul hBO hcov
  have hmod := relIndex_centralizer_modEq_one hz3 hzO
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (coprime_three_of_isPGroup_two h.isPGroup_core))
  have h1 : (centralizer ({z} : Set G)).relIndex O ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    obtain ⟨o, ho, hoz⟩ := h.exists_core_not_comm
    exact fun hle => hoz (mem_centralizer_singleton_iff.1 (hle ho))
  have hcore : (centralizer ({z} : Set G)).relIndex O = 4 := by
    unfold Nat.ModEq at hmod
    omega
  refine ⟨by rw [centralizer_zpowers_eq]; exact hcore, ?_⟩
  rw [centralizer_zpowers_eq]
  calc (centralizer ({z} : Set G)).relIndex S
      ≤ (centralizer ({z} : Set G)).relIndex O * O.relIndex S :=
        relIndex_centralizer_le_mul z h.core_le
    _ = 4 * 4 := by rw [hcore, h.S_index]
    _ ≤ 16 := by norm_num

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
