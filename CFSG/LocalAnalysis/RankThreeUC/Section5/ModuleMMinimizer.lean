module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CommRankQuotient
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CommRankConjugacy
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

open scoped Pointwise

theorem exists_involution_in_sylow_attaining_moduleM {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (T : Subgroup G) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hev : Even (Nat.card G)) :
    ∃ t ∈ T, orderOf t = 2 ∧ commRank ρ t = moduleM ρ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card G := even_iff_two_dvd.mp hev
  obtain ⟨t0, ht0⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 h2
  have hne : (involutionDisplacements ρ).Nonempty :=
    ⟨_, t0, ht0, rfl⟩
  obtain ⟨t1, ht1, hval⟩ := Nat.sInf_mem hne
  have hM : moduleM ρ = sInf (involutionDisplacements ρ) := by
    unfold moduleM; rw [if_pos hev]
  have hS : Nat.card T = 2 ^ (Nat.card G).factorization 2 := by
    have := hT.card_eq
    simpa [Subgroup.card_top] using this
  let S : Sylow 2 G := Sylow.ofCard T hS
  have hP : IsPGroup 2 (Subgroup.zpowers t1) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ht1]; simp
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨g * t1 * g⁻¹, ?_, ?_, ?_⟩
  · have hmem : t1 ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers t1)
    have : g * t1 * g⁻¹ ∈ MulAut.conj g • (Q : Subgroup G) := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.conj_apply, mul_assoc] using hmem
    have h'' : ((g • Q : Sylow 2 G) : Subgroup G) = MulAut.conj g • (Q : Subgroup G) :=
      Sylow.coe_subgroup_smul
    rw [← h'', hg] at this
    exact this
  · have := (MulAut.conj g).orderOf_eq t1
    simpa [MulAut.conj_apply] using this.trans ht1
  · rw [commRank_conj, commRank_eq_fixedQuot_finrank, hM, ← hval]
