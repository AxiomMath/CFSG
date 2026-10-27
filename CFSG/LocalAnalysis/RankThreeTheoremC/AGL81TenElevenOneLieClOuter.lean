module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup
open scoped commutatorElement

namespace LieClAut

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

theorem false_of_index_of_forall_mem (hLL : ⁅L, L⁆ = L)
    (hC3 : ¬ 3 ∣ Nat.card (centralizer (L : Set Y)))
    (hmem : ∀ u : Y, (∃ k : ℕ, u ^ 3 ^ k = 1) → u ∈ L ⊔ centralizer (L : Set Y))
    (hN : ∃ N : Subgroup Y, N.Normal ∧ N.index = 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N, hNn, hNi⟩ := hN
  have hcard : Nat.card (Y ⧸ N) = 3 := hNi
  have hcomm : ∀ a b : Y ⧸ N, a * b = b * a := by
    haveI := isCyclic_of_prime_card hcard
    exact fun a b => (IsCyclic.commGroup (α := Y ⧸ N)).mul_comm a b
  have hmk : ∀ g : Y, g ∈ N ↔ (g : Y ⧸ N) = 1 := fun g => (QuotientGroup.eq_one_iff g).symm
  have hLN : L ≤ N := by
    rw [← hLL, Subgroup.commutator_le]
    intro a _ b _
    rw [hmk]
    change QuotientGroup.mk' N ⁅a, b⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have hCN : centralizer (L : Set Y) ≤ N := fun c hc => by
    rw [hmk, ← orderOf_eq_one_iff]
    have h1 : orderOf (c : Y ⧸ N) ∣ 3 := hcard ▸ orderOf_dvd_natCard _
    have h2 : orderOf (c : Y ⧸ N) ∣ Nat.card (centralizer (L : Set Y)) := by
      refine (orderOf_map_dvd (QuotientGroup.mk' N) c).trans ?_
      have := orderOf_dvd_natCard (⟨c, hc⟩ : centralizer (L : Set Y))
      rwa [Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hC3
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 Y))
  have hPN : (P : Subgroup Y) ≤ N := fun u hu => by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨u, hu⟩
    exact sup_le hLN hCN (hmem u ⟨k, by simpa using congrArg Subtype.val hk⟩)
  have h3 := Subgroup.index_dvd_of_le hPN
  rw [hNi] at h3
  exact P.not_dvd_index h3

end LieClAut

@[expose] def KFactTenElevenOneLieAutOuter : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → Open.IsQuasisimple ↥L →
    CFSG.pCore 2 Y = ⊥ → ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
    (RankTwoList d.1 ∨ RankThreeList d.1) → (∀ q : TauCeti.PrimePower, d.1 ≠ .A 2 q) →
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    (∃ u : Y, (∃ k : ℕ, u ^ 3 ^ k = 1) ∧ u ∉ L ⊔ Subgroup.centralizer (L : Set Y)) →
    (∃ T J : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set _) ≤ J ∧ J ≠ Subgroup.normalizer (T : Set _) ∧ J ≠ ⊤) →
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (L : Set Y)) →
    Open.pRank 3 (⊤ : Subgroup Y) = 3 →
    (∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      Open.pRank 3 (Subgroup.centralizer (E : Set Y)) ≤ 2) →
    (∃ N : Subgroup Y, N.Normal ∧ N.index = 3) → False

theorem kFactTenElevenOneLieAutRes_of_outer (hO : KFactTenElevenOneLieAutOuter) :
    KFactTenElevenOneLieAutRes := by
  intro Y _ _ L hLn hq hO2 d hd hlist hA2 he hJ hC3 hrk hE hN
  by_cases hmem : ∀ u : Y, (∃ k : ℕ, u ^ 3 ^ k = 1) → u ∈ L ⊔ centralizer (L : Set Y)
  · have hLL : ⁅L, L⁆ = L := by
      rw [← Subgroup.map_subtype_commutator, hq.1, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    exact LieClAut.false_of_index_of_forall_mem hLL hC3 hmem hN
  · push Not at hmem
    obtain ⟨u, hu3, huLC⟩ := hmem
    exact hO Y L hLn hq hO2 d hd hlist hA2 he ⟨u, hu3, huLC⟩ hJ hC3 hrk hE hN

end CFSG.LocalAnalysis.RankThreeTheoremC
