module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB0
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section FFacts

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y}

theorem nf5_isPGroup (h : NF5 F Γ B R₀ x) : IsPGroup 5 ↥F := h.sylow.isPGroup

private theorem mem_zpowers_of_orderOf_prime_of_ne_one {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {g w : G} (hg : orderOf g = p) (hw : w ∈ Subgroup.zpowers g) (hw1 : w ≠ 1) :
    g ∈ Subgroup.zpowers w := by
  have hcard : Nat.card (Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hg]
  have hne : (⟨w, hw⟩ : Subgroup.zpowers g) ≠ 1 := fun e => hw1 (congrArg Subtype.val e)
  have hmem : (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) ∈
      Subgroup.zpowers (⟨w, hw⟩ : Subgroup.zpowers g) :=
    mem_zpowers_of_prime_card hcard hne
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem nf5_exists_z (h : NF5 F Γ B R₀ x) : ∃ z : Y, NF5Z F z := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hF : Nat.card F = 5 ^ 3 := h.card.trans (by norm_num)
  have hC : Nat.card (Subgroup.center ↥F) = 5 := by
    obtain ⟨k, hk0, hkc⟩ := IsPGroup.card_center_eq_prime_pow hF (by norm_num : 0 < 3)
    have hdvd : Nat.card (Subgroup.center ↥F) ∣ Nat.card ↥F := Subgroup.card_subgroup_dvd_card _
    rw [hkc, hF] at hdvd
    have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 5)).mp hdvd
    interval_cases k
    · rw [hkc, pow_one]
    · exfalso
      apply h.nonab
      have h1 := Subgroup.card_mul_index (Subgroup.center ↥F)
      rw [hkc, hF] at h1
      have hidx : (Subgroup.center ↥F).index = 5 :=
        Nat.eq_of_mul_eq_mul_left (by norm_num) (h1.trans (by norm_num))
      rw [Subgroup.index_eq_card] at hidx
      haveI : IsCyclic (↥F ⧸ Subgroup.center ↥F) := isCyclic_of_prime_card hidx
      exact isMulCommutative_of_isCyclic_quotient_center_self ↥F
    · exfalso
      apply h.nonab
      have htop : Subgroup.center ↥F = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hkc, hF]
      exact Subgroup.center_eq_top_iff.mp htop
  haveI : Nontrivial (Subgroup.center ↥F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hC]; norm_num)
  obtain ⟨g, hg⟩ : ∃ g : Subgroup.center ↥F, g ≠ 1 := exists_ne 1
  have hord : orderOf g = 5 := by
    have hd := orderOf_dvd_natCard g
    rw [hC] at hd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hg
    · exact h1
  refine ⟨((g : ↥F) : Y), (g : ↥F).2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hord]
  · intro f hf
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp g.2 ⟨f, hf⟩)
  · intro w hw hwc
    have hwcen : (⟨w, hw⟩ : ↥F) ∈ Subgroup.center ↥F :=
      Subgroup.mem_center_iff.mpr fun f => Subtype.ext (hwc f f.2)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card (g' := (⟨⟨w, hw⟩, hwcen⟩ : Subgroup.center ↥F)) hC hg)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simpa using congrArg (fun t : Subgroup.center ↥F => ((t : ↥F) : Y)) hk

theorem nf5_normal_contains (h : NF5 F Γ B R₀ x) {z : Y} (hz : NF5Z F z) {N : Subgroup Y} (hN : N ≤ F)
    (hnorm : ∀ f ∈ F, ∀ n ∈ N, f * n * f⁻¹ ∈ N) (hne : N ≠ ⊥) : z ∈ N := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Group.IsNilpotent ↥F := (nf5_isPGroup h).isNilpotent
  haveI : (N.subgroupOf F).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hnorm g g.2 n hn⟩
  have hne' : N.subgroupOf F ≠ ⊥ := by
    intro h0
    apply hne
    have hd : N ⊓ F = ⊥ := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h0)
    rwa [inf_eq_left.mpr hN] at hd
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  obtain ⟨hwN, hwc⟩ := Subgroup.mem_inf.mp w.2
  have hw1 : ((w : ↥F) : Y) ≠ 1 := by
    intro e
    apply hw
    apply Subtype.ext
    apply Subtype.ext
    exact e
  have hwgen : ((w : ↥F) : Y) ∈ Subgroup.zpowers z :=
    hz.gen ((w : ↥F) : Y) (w : ↥F).2 fun f hf =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨f, hf⟩)
  exact Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mp hwN)
    (mem_zpowers_of_orderOf_prime_of_ne_one hz.order hwgen hw1)

theorem nf5_z_mem_B (h : NF5 F Γ B R₀ x) {z : Y} (hz : NF5Z F z) : z ∈ B := by
  refine (h.hB z).2 ⟨hz.mem, ?_⟩
  rw [← hz.order]
  exact pow_orderOf_eq_one z

theorem nf5_mem_zpowers_of_mem_x (h : NF5 F Γ B R₀ x) {z : Y} (hz : NF5Z F z) {b : Y} (hb : b ∈ F)
    (hbx : b ∈ Subgroup.zpowers x) : b ∈ Subgroup.zpowers z :=
  hz.gen b hb ((h.cen b hb).2 hbx)

theorem nf5_pCoreOf_le (h : NF5 F Γ B R₀ x) : pCoreOf 5 (⊤ : Subgroup Y) ≤ Γ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := h.sylow
  have hN : CFSG.pCore 5 (⊤ : Subgroup Y) ≤ (Q : Subgroup ↥(⊤ : Subgroup Y)) :=
    IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup Q
  calc pCoreOf 5 (⊤ : Subgroup Y)
      = (CFSG.pCore 5 (⊤ : Subgroup Y)).map (⊤ : Subgroup Y).subtype := rfl
    _ ≤ (Q : Subgroup ↥(⊤ : Subgroup Y)).map (⊤ : Subgroup Y).subtype := Subgroup.map_mono hN
    _ = F := hQ
    _ ≤ Γ := h.FΓ

end FFacts

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
