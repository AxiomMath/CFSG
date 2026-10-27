module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Group
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Local
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.RankThree.PartOne.K159.AutSzIso
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open Subgroup

theorem sz32_data :
    ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → ∀ T : Sylow 5 K,
      CFSG.AGLEmbedding.KFactProofs.Sz32Local.Sz32Data K (T : Subgroup K) := by
  intro K _ _ hK
  obtain ⟨-, hiso⟩ := hK
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  have hmodel := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  obtain rfl : a = 2 := by omega
  let σ : F ≃+* CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    CFSG.AGLEmbedding.KFactProofs.Sz32.F32.ringEquiv F hF'
  let ε : K ≃* CFSG.Blueprint.suzukiGroup 2 CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    eF.trans (CFSG.AGLEmbedding.KFactProofs.Sz32Local.modelEquiv σ)
  have hcard : ∀ T : Sylow 5 K, Nat.card (T : Subgroup K) = 25 := by
    intro T
    rw [Sylow.card_eq_multiplicity, hSz.card,
      CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
    norm_num
  intro T
  exact ⟨hSz.card, hcard T, hSz.cyclic T,
    CFSG.AGLEmbedding.KFactProofs.Sz32Local.centralizer_le_of_equiv ε T⟩

theorem sz32_maximal :
    ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → NormalizerMaximal 5 K := by
  intro K _ _ hK S H hH
  exact (sz32_data K hK S).maximal hH

theorem sz32_transOmega :
    ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → NormalizerTransitiveOmega 5 K := by
  intro K _ _ hK S a ha ha5 b hb hb5
  have D := sz32_data K hK S
  set P : Subgroup K := (S : Subgroup K)
  set N : Subgroup K := normalizer (P : Set K)
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hNcard : Nat.card N = 100 := D.card_normalizer
  have hPcard : Nat.card P = 25 := D.card_eq
  have ha1 : a ≠ 1 := by
    rintro rfl
    simp at ha5
  letI inst : MulAction N K := MulAction.compHom K ((MulAut.conj : K →* MulAut K).comp N.subtype)
  have hsmul : ∀ (n : N) (x : K), n • x = (n : K) * x * (n : K)⁻¹ := fun n x => rfl
  have hstab : MulAction.stabilizer N a = P.subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsmul]
    constructor
    · intro h
      refine D.centralizer_le a ha ha1 n ?_
      calc (n : K) * a = (n : K) * a * (n : K)⁻¹ * n := by group
        _ = a * n := by rw [h]
    · intro hn
      rw [D.commute _ hn _ ha]
      group
  have hidx : (P.subgroupOf N).index = 4 := by
    have h1 : Nat.card (P.subgroupOf N) = 25 := by
      rw [← hPcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
    have h2 := Subgroup.card_mul_index (P.subgroupOf N)
    rw [h1, hNcard] at h2
    omega
  have hOrbCard : (MulAction.orbit N a).ncard = 4 := by
    rw [← MulAction.index_stabilizer N a, hstab, hidx]
  let Ω : Set K := {x | x ∈ P ∧ orderOf x = 5}
  have hΩcard : Ω.ncard = 4 := by
    haveI : Fintype P := Fintype.ofFinite P
    have hcyc : IsCyclic P := D.isCyclic
    have hP25 : Fintype.card P = 25 := by rw [← Nat.card_eq_fintype_card]; exact hPcard
    have h1 := IsCyclic.card_orderOf_eq_totient (α := P) (d := 5) (by rw [hP25]; norm_num)
    have h2 : Nat.card {x : P // orderOf x = 5} = 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, h1]
      decide
    have hΩeq : Ω = Subtype.val '' {x : P | orderOf x = 5} := by
      ext x
      constructor
      · rintro ⟨hx, hox⟩
        exact ⟨⟨x, hx⟩, by simpa [Subgroup.orderOf_coe] using hox, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
    rw [hΩeq, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    exact h2
  have hOrbSub : MulAction.orbit N a ⊆ Ω := by
    rintro y ⟨n, hn⟩
    have hy : y = (n : K) * a * (n : K)⁻¹ := hn.symm.trans (hsmul n a)
    rw [hy]
    refine ⟨?_, ?_⟩
    · exact ((Subgroup.mem_normalizer_iff.1 n.2) a).1 ha
    · have := MulEquiv.orderOf_eq (MulAut.conj (n : K)) a
      simpa [MulAut.conj_apply] using this.trans ha5
  have hEq : MulAction.orbit N a = Ω :=
    Set.eq_of_subset_of_ncard_le hOrbSub (by rw [hΩcard, hOrbCard])
  have hbΩ : b ∈ MulAction.orbit N a := by
    rw [hEq]
    exact ⟨hb, hb5⟩
  obtain ⟨n, hn⟩ := hbΩ
  exact ⟨(n : K), n.2, (hsmul n a).symm.trans hn⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
