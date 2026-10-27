module

public import CFSG.GH74.Uniqueness.Gamma

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem isBenderGroup_of_isSimpleBenderGroup {Q : Type*} [Group Q] [Finite Q]
    (hB : CFSG.BenderSuzuki.IsSimpleBenderGroup Q) : CFSG.BenderSuzuki.IsBenderGroup Q := by
  rcases hB with
    ⟨⟨n, hn, ⟨e⟩⟩⟩ |
    ⟨⟨n, hn, ⟨e⟩⟩⟩ |
    ⟨⟨n, hn, E, hEfield, hEfinite, J, hform, hEcard, hfixed, ⟨e⟩⟩⟩
  · exact CFSG.BenderSuzuki.IsBenderGroup.isPSL2 n hn e
  · exact CFSG.BenderSuzuki.IsBenderGroup.isSuzuki n hn
      (e.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n).symm))
  · let : Field E := hEfield
    let : Finite E := hEfinite
    obtain ⟨u⟩ := CFSG.BenderSuzuki.projectiveSpecialUnitary_equiv_PSU3Model
      J n hn hform hEcard hfixed
    exact CFSG.BenderSuzuki.IsBenderGroup.isPSU3 n hn (e.trans u)

theorem twoRankAtLeastTwo_of_two_le_pRank {X : Type*} [Group X] [Finite X] (L : Subgroup X)
    (h : 2 ≤ Open.pRank 2 L) :
    CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEL, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) L
  have hdvd : 2 ^ 2 ∣ Nat.card E := by
    rw [hcard]
    exact pow_dvd_pow 2 h
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 hdvd
  let K' : Subgroup X := K.map E.subtype
  have hK'E : K' ≤ E := Subgroup.map_subtype_le K
  have hK'card : Nat.card K' = 4 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
    norm_num
  refine ⟨K'.subgroupOf L, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hK'E.trans hEL)).toEquiv]
    exact hK'card
  · rintro ⟨⟨x, hxL⟩, hx⟩
    have hxK' : x ∈ K' := hx
    have hx2 : x ^ 2 = 1 := hE.2 x (hK'E hxK')
    apply Subtype.ext
    apply Subtype.ext
    simpa using hx2

theorem S_SE_aux
    {X : Type*} [Group X] [Finite X] (M : Subgroup X) (hM : IsStronglyEmbedded M)
    (L : Subgroup X) (hL : L = CFSG.BenderSuzuki.involutionCore X) :
    Open.pRank 2 L ≤ 1 ∨
      (CFSG.BenderSuzuki.IsBenderGroup (↥L ⧸ pPrimeCore 2 ↥L) ∧
        (∀ o ∈ pPrimeCore 2 ↥L, (o : X) ∈ M) ∧
        IsBorel ((M.comap L.subtype).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)))) := by
  have hnat : CFSG.BenderSuzuki.IsStronglyEmbedded M :=
    CFSG.BenderSuzuki.isStronglyEmbedded_of_parity M
      (isStronglyEmbeddedOrder_of_isStronglyEmbedded hM)
  have hconc := CFSG.BenderSuzuki.theorem_SE M hnat
  subst hL
  rcases hconc with hlow | ⟨hB, hO, hBorel⟩
  · left
    by_contra hge
    exact hlow (twoRankAtLeastTwo_of_two_le_pRank _ (by omega))
  · right
    refine ⟨isBenderGroup_of_isSimpleBenderGroup hB, ?_, ?_⟩
    · intro o ho
      exact (hO ⟨o, ho, rfl⟩).1
    · obtain ⟨-, S, hS⟩ := hBorel
      refine ⟨S, ?_⟩
      have key : M.comap (CFSG.BenderSuzuki.involutionCore X).subtype =
          (M ⊓ CFSG.BenderSuzuki.involutionCore X).subgroupOf
            (CFSG.BenderSuzuki.involutionCore X) := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      exact (congrArg (Subgroup.map (QuotientGroup.mk'
        (CFSG.BenderSuzuki.twoPrimeCore ↥(CFSG.BenderSuzuki.involutionCore X)))) key).trans hS

theorem S_SE_proof :
    ∀ (X : Type) [Group X] [Finite X] (M : Subgroup X), IsStronglyEmbedded M →
      Open.pRank 2 (involutionClosure X) ≤ 1 ∨
        (CFSG.BenderSuzuki.IsBenderGroup
            (↥(involutionClosure X) ⧸ pPrimeCore 2 ↥(involutionClosure X)) ∧
          (∀ o ∈ pPrimeCore 2 ↥(involutionClosure X), (o : X) ∈ M) ∧
          IsBorel ((M.comap (involutionClosure X).subtype).map
            (QuotientGroup.mk' (pPrimeCore 2 ↥(involutionClosure X))))) := by
  intro X _ _ M hM
  refine S_SE_aux M hM _ ?_
  unfold involutionClosure CFSG.BenderSuzuki.involutionCore
  congr 1
  ext x
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change orderOf x = 2 ↔ CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x
  unfold CFSG.BenderSuzuki.PFAppendixIII.IsInvolution
  rw [orderOf_eq_prime_iff]
  exact and_comm

end CFSG.GH74.Uniqueness
