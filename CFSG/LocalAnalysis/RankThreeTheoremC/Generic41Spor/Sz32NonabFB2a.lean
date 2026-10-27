module

import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1K6
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB0

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Part

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y}

private theorem nf5_pRank_le (h : NF5 F Γ B R₀ x) : CFSG.Open.pRank 5 (⊤ : Subgroup Y) ≤ 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hidx : ¬ 5 ∣ F.index := by
    have hs := (CFSG.ABGLocalTools.isSylowOf_iff.mp h.sylow).2.2
    rwa [Subgroup.relIndex_top_right] at hs
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro k ⟨E, -, -, hE⟩
  have hdvd : Nat.card E ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card E
  rw [← Subgroup.card_mul_index (H := F), h.card, hE] at hdvd
  have hcop : Nat.Coprime (5 ^ k) F.index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hidx)
  have h125 : 5 ^ k ∣ 125 := hcop.dvd_of_dvd_mul_right hdvd
  by_contra hk
  have h4 : 5 ^ 4 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact absurd (h4.trans (Nat.le_of_dvd (by norm_num) h125)) (by norm_num)

private theorem nf5_sylow (h : NF5 F Γ B R₀ x) : ∃ S : Sylow 5 Y, (S : Subgroup Y) = F := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hidx : ¬ 5 ∣ F.index := by
    have hs := (CFSG.ABGLocalTools.isSylowOf_iff.mp h.sylow).2.2
    rwa [Subgroup.relIndex_top_right] at hs
  exact ⟨h.sylow.isPGroup.toSylow hidx, rfl⟩

theorem nf5_center_bot (h6 : KFactI6103Five) (h : NF5 F Γ B R₀ x) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) : Subgroup.center ↥L = ⊥ := by
  obtain ⟨S, hS⟩ := nf5_sylow h
  have hOm : ∀ g ∈ (S : Subgroup Y), ∀ g' ∈ (S : Subgroup Y), g ^ 5 = 1 → g' ^ 5 = 1 →
      g * g' = g' * g := by
    intro g hg g' hg' hg5 hg'5
    rw [hS] at hg hg'
    haveI : IsMulCommutative B := h.Belem.1
    exact setLike_mul_comm ((h.hB g).2 ⟨hg, hg5⟩) ((h.hB g').2 ⟨hg', hg'5⟩)
  exact szh1_center_bot h6 h.catalog h.core (nf5_pRank_le h) S hOm hL

theorem nf5_five_dvd (h : NF5 F Γ B R₀ x) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    5 ∣ Nat.card L := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_contra hnd
  have hcop : Nat.Coprime 5 (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hnd
  have hcoreL : primeComplementCore (G := ↥L) 5 = ⊥ :=
    cfsg_subnormal_primeComplementCore_eq_bot 5 L hL.2.1 h.core
  have htop : (⊤ : Subgroup ↥L) ≤ primeComplementCore (G := ↥L) 5 :=
    normal_coprime_le_primeComplementCore 5 ⊤ inferInstance (by simpa using hcop)
  rw [hcoreL] at htop
  haveI := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥L)
  exact hz (Subgroup.mem_bot.mp (htop (Subgroup.mem_top z)))

end Part

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
