module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB2n
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Part

open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y}

theorem nf5_z_mem_comp (h : NF5 F Γ B R₀ x)
    (hZ : ∀ L : Subgroup Y, IsComponentOf L ⊤ → Subgroup.center ↥L = ⊥) {z : Y} (hz : NF5Z F z)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) : z ∈ K := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hFN : F ≤ Subgroup.normalizer (K : Set Y) := fun f hf => nf5_comp_normalized h hZ hK hf
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 5 F (Subgroup.normalizer (K : Set Y)) :=
    h.sylow.of_le hFN le_top
  have hsK : CFSG.ABGLocalTools.IsSylowOf 5 (F ⊓ K) K :=
    hsyl.inf_of_le_normalizer Subgroup.le_normalizer le_rfl
  have h5 : 5 ∣ Nat.card K := nf5_five_dvd h hK
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hne : F ⊓ K ≠ ⊥ := by
    intro hbot
    have hcard := hsK.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card K).factorization 5 :=
      Nat.Prime.factorization_pos_of_dvd (by norm_num) hKpos.ne' h5
    have h5dvd : 5 ∣ 5 ^ (Nat.card K).factorization 5 := dvd_pow_self 5 hpos.ne'
    rw [← hcard] at h5dvd
    norm_num at h5dvd
  have hnorm : ∀ f ∈ F, ∀ n ∈ F ⊓ K, f * n * f⁻¹ ∈ F ⊓ K := by
    intro f hf n hn
    obtain ⟨hnF, hnK⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨F.mul_mem (F.mul_mem hf hnF) (F.inv_mem hf), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hFN hf) n).mp hnK
  exact (Subgroup.mem_inf.mp (nf5_normal_contains h hz (inf_le_left : F ⊓ K ≤ F) hnorm hne)).2

theorem nf5_comp_unique (h : NF5 F Γ B R₀ x)
    (hZ : ∀ L : Subgroup Y, IsComponentOf L ⊤ → Subgroup.center ↥L = ⊥) {z : Y} (hz : NF5Z F z)
    {K K' : Subgroup Y} (hK : IsComponentOf K ⊤) (hK' : IsComponentOf K' ⊤) : K = K' := by
  by_contra hne
  have hzK : z ∈ K := nf5_z_mem_comp h hZ hz hK
  have hzK' : z ∈ K' := nf5_z_mem_comp h hZ hz hK'
  have hcomm : ⁅K, K'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne K K' hK hK' hne
  have hzc : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Y) * z = z * (g : Y)
    have hmem : ⁅(g : Y), z⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator g.2 hzK'
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  rw [hZ K hK, Subgroup.mem_bot] at hzc
  have hz1 : z = 1 := congrArg Subtype.val hzc
  have hord := hz.order
  rw [hz1, orderOf_one] at hord
  norm_num at hord

end Part

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
