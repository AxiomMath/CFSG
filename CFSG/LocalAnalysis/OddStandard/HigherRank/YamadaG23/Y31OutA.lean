module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31SylConj
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31FrSq

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {Q : Type} [Group Q] [Finite Q] (fr : Frame (MulAut Q))

private lemma innerAut_normal (Q : Type) [Group Q] : (innerAut Q).Normal := by
  change ((MulAut.conj : Q →* MulAut Q).range).Normal
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hn
  exact ⟨g q, by ext x; simp [mul_assoc]⟩

theorem frame_outer_invol_conj (h : fr.Facts (innerAut Q)) (hOut : (innerAut Q).index = 2)
    {α : MulAut Q} (hα2 : α ^ 2 = 1) (hα : α ∉ innerAut Q) :
    ∃ i ∈ innerAut Q, i * α * i⁻¹ = fr.σ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hInnNorm : (innerAut Q).Normal := innerAut_normal Q
  have hQ2 : IsPGroup 2 (zpowers α) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers α, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr hα2
  obtain ⟨g, -, hgconj⟩ :=
    exists_conj_le_isSylowIn (G := MulAut Q) (V := ⊤) (P := fr.Sσ) (Q := zpowers α)
      h.1.2.2 hQ2 le_top
  have hgα : g * α * g⁻¹ ∈ fr.Sσ := by
    have hmem : MulAut.conj g α ∈ conjSub g (zpowers α) := by
      rw [conjSub]
      exact Subgroup.mem_map.mpr ⟨α, Subgroup.mem_zpowers α, rfl⟩
    simpa only [MulAut.conj_apply] using hgconj hmem
  have hg_mem : g ∈ innerAut Q ⊔ closure ({fr.σ} : Set (MulAut Q)) := by
    rw [frame_inner_sup_sigma fr h.1 hOut]
    exact Subgroup.mem_top g
  have hg_mem' : g ∈ closure ({fr.σ} : Set (MulAut Q)) ⊔ innerAut Q := by
    rw [sup_comm]
    exact hg_mem
  obtain ⟨y, hy, i, hi, hyi⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := closure ({fr.σ} : Set (MulAut Q)))
      (t := innerAut Q)).mp hg_mem'
  have hySσ : y ∈ fr.Sσ :=
    (Subgroup.closure_le fr.Sσ).mpr (Set.singleton_subset_iff.mpr (frame_sigma_mem_Sσ fr)) hy
  have hβSσ : i * α * i⁻¹ ∈ fr.Sσ := by
    have heq : i * α * i⁻¹ = y⁻¹ * (g * α * g⁻¹) * y := by
      rw [show g = y * i from hyi.symm]
      group
    rw [heq]
    exact mul_mem (mul_mem (inv_mem hySσ) hgα) hySσ
  have hβ2 : (i * α * i⁻¹) ^ 2 = 1 := by
    have heq : (i * α * i⁻¹) ^ 2 = i * α ^ 2 * i⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [heq, hα2]
    simp
  have hβne : i * α * i⁻¹ ≠ 1 := by
    intro hb
    apply hα
    have heq : α = i⁻¹ * (i * α * i⁻¹) * i := by group
    rw [heq, hb]
    simp
  have hβnotInn : i * α * i⁻¹ ∉ innerAut Q := by
    intro hb
    apply hα
    have heq : α = i⁻¹ * (i * α * i⁻¹) * i := by group
    rw [heq]
    simpa using hInnNorm.conj_mem (i * α * i⁻¹) hb i⁻¹
  have hβnotS : i * α * i⁻¹ ∉ fr.S :=
    fun hS => hβnotInn (frame_S_le_inner fr h.1 hS)
  have hβorder : orderOf (i * α * i⁻¹) = 2 := orderOf_eq_prime hβ2 hβne
  obtain hβS | ⟨s, hs, hβs⟩ := frame_mem_Sσ_cases fr h.1 hβSσ
  · exact absurd hβS hβnotS
  have h13 := h.2.2.1
  have hmem13 : i * α * i⁻¹ ∈ conjClass fr.S fr.σ := by
    rw [← h13.2.2.1, ← h13.2.1]
    exact ⟨⟨s, hs, hβs⟩, hβorder⟩
  have hmem13' : ∃ t ∈ fr.S, i * α * i⁻¹ = t * fr.σ * t⁻¹ := by
    simpa only [conjClass, Set.mem_setOf_eq] using hmem13
  obtain ⟨s₁, hs₁, hβs₁⟩ := hmem13'
  refine ⟨s₁⁻¹ * i, ?_, ?_⟩
  · exact mul_mem (inv_mem (frame_S_le_inner fr h.1 hs₁)) hi
  · have heq : (s₁⁻¹ * i) * α * (s₁⁻¹ * i)⁻¹ = s₁⁻¹ * (i * α * i⁻¹) * s₁ := by
      group
    rw [heq, hβs₁]
    group

end CFSG.OddStandard.HigherRank.YamadaG23
