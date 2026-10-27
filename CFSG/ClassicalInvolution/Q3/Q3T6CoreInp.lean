module

public import CFSG.ClassicalInvolution.Q3.Q3T6CoreCStar
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreFamDE
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreFamTop
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreEnd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore fusionStronglyClosed)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

section Inputs

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

abbrev secL (K C : Subgroup G) : Subgroup ↥C := (K ⊓ C).subgroupOf C

omit [Finite G] in
theorem card_centralizer_lt_of_ne_bot [Finite G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {B : Subgroup G} (hB : B ≠ ⊥) : Nat.card ↥(Subgroup.centralizer (B : Set G)) < Nat.card G := by
  have hne : Subgroup.centralizer (B : Set G) ≠ ⊤ := by
    intro htop
    have hBZ : (B : Set G) ⊆ Subgroup.center G := Subgroup.centralizer_eq_top_iff_subset.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · apply hB
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ Subgroup.center G := hBZ hx
      rw [h, Subgroup.mem_bot] at hx'
      exact (Subgroup.mem_bot).mpr hx'
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have h := Subgroup.card_mul_index (Subgroup.centralizer (B : Set G))
  have hidx : (Subgroup.centralizer (B : Set G)).index ≠ 1 := fun h1 =>
    hne (Subgroup.index_eq_one.mp h1)
  have hpos : 0 < Nat.card (Subgroup.centralizer (B : Set G)) := Nat.card_pos
  have hidx0 : (Subgroup.centralizer (B : Set G)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : 2 ≤ (Subgroup.centralizer (B : Set G)).index := by omega
  nlinarith

variable {K : Subgroup G} {z : G}

theorem sectionInputs3 (hK : Q3.IsClassicalMember3 K z)
    (hΩ : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K))
    (hDE : DEdgeless (CoreAssembly.conjClass K))
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hnab : ∃ a b : G, a * b ≠ b * a) {B : Subgroup G} (hB2 : IsPGroup 2 B) (hB : B ≠ ⊥)
    (hBK : B ≤ centralizerModOdd ⊤ K) (hzB : z ∈ Subgroup.centralizer (B : Set G))
    (c : ↥(Subgroup.centralizer (B : Set G)))
    (hne : (c : G) * z * (c : G)⁻¹ ≠ z)
    (hcomm : (c : G) * z * (c : G)⁻¹ * z = z * ((c : G) * z * (c : G)⁻¹)) :
    Q3.IsClassicalMember3 (secL K (Subgroup.centralizer (B : Set G)))
      (⟨z, hzB⟩ : Subgroup.centralizer (B : Set G)) ∧
    HypOmegaModU (.sl2 3 1) (conjFamily (secL K (Subgroup.centralizer (B : Set G)))) ∧
    DEdgeless (conjFamily (secL K (Subgroup.centralizer (B : Set G)))) ∧
    Nat.card ↥(Subgroup.centralizer (B : Set G)) < Nat.card G ∧
    ((⊤ : Subgroup (↥(conjGen (secL K (Subgroup.centralizer (B : Set G)))) ⧸
      classicalInvolutionOddCore ↥(conjGen (secL K (Subgroup.centralizer (B : Set G)))))) ∉
      oddQuotientFamily (restrictFamily (conjFamily (secL K (Subgroup.centralizer (B : Set G))))
        (conjGen (secL K (Subgroup.centralizer (B : Set G)))))) := by
  have hL := isClassicalMember3_inf_centralizer_of_cStar hK hB2 hBK rfl hzB
  exact ⟨hL, hypOmegaModU_conjFamily_sec hK hΩ hzB hL,
    dEdgeless_conjFamily_sec hK hΩ hDE hN hzB hL, card_centralizer_lt_of_ne_bot hnab hB,
    top_not_mem_sectionFamily_sec hzB hL c hne hcomm⟩

end Inputs

section EndGame


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem false_of_stronglyClosed_cStar (hB1 : S19B.GoldschmidtB1Tmp) (S : Sylow 2 G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {B : Subgroup G} (hBS : B ≤ (S : Subgroup G))
    (hB : B ≠ ⊥) (hsc : fusionStronglyClosed (B : Set G) S) (hK : Q3.IsClassicalMember3 K z)
    (hΩ : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K))
    (hDE : DEdgeless (CoreAssembly.conjClass K))
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hBK : B ≤ centralizerModOdd ⊤ K) (hzB : z ∈ Subgroup.centralizer (B : Set G))
    (c : ↥(Subgroup.centralizer (B : Set G))) (hne : (c : G) * z * (c : G)⁻¹ ≠ z)
    (hcomm : (c : G) * z * (c : G)⁻¹ * z = z * ((c : G) * z * (c : G)⁻¹)) {n : ℕ}
    (hM : Q3.M11Facts) (hIH : CITBelowT (.sl2 3 1) n) (hn : Nat.card G ≤ n) : False := by
  obtain ⟨-, hΩΛ, hDEΛ, hcard, hTop⟩ := sectionInputs3 hK hΩ hDE hN hnab
    (S.isPGroup'.to_le hBS) hB hBK hzB c hne hcomm
  exact false_of_stronglyClosed_three hB1 hnab S hBS hB hsc hM hIH (hcard.trans_le hn) hΩΛ
    ⟨_, ⟨1, conjSub_one _⟩⟩ hDEΛ hTop

end EndGame

end CFSG.ClassicalInvolution.Q3.Q3T6
