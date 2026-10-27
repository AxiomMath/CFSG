module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.KFact76RankThree
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProofTools

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.RankThree.PartTwo.Sec17.Proof176Steps

@[expose] def KFact76RankThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → CFSG.pPrimeCore 3 Y = ⊥ →
    ∀ A : Subgroup Y, Nat.card A = 3 →
      (∀ g : Y, A.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (A : Set Y) →
        A.map (MulAut.conj g).toMonoidHom = A) →
      CFSG.Open.pRank 3 (Subgroup.normalClosure (A : Set Y)) ≤ 3 →
      IsSimpleGroup ↥(Subgroup.normalClosure (A : Set Y)) ∧
        (CFSG.Open.pRank 3 (Subgroup.normalClosure (A : Set Y)) = 1 ∨
          (∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.G2 q).Valid, q.p ≠ 3 ∧
            Nonempty (↥(Subgroup.normalClosure (A : Set Y)) ≃*
              (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)) ∨
          (∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid,
            q.card = 3 ∧ Nonempty (↥(Subgroup.normalClosure (A : Set Y)) ≃*
              (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)) ∨
          Nonempty (↥(Subgroup.normalClosure (A : Set Y)) ≃*
            (TauCeti.CFSGIndex.sporadic .J2).Group))

theorem kFact76MaxRankThree_of_kFact76RankThree (h76 : KFact76RankThree)
    (hG2 : KFactG2NormalizerMax) (hUJ : KFactU33J2NormalizerMax) :
    Section8.KFact76MaxRankThree := by
  intro Y _ _ hKY hcore A hA hwc hbd
  obtain ⟨hsimple, hcases⟩ := h76 Y hKY hcore A hA hwc hbd
  refine ⟨hsimple, ?_⟩
  rcases hcases with h1 | hrest
  · exact Or.inl h1
  right
  set K := Subgroup.normalClosure (A : Set Y)
  have hAK : A ≤ K := Subgroup.le_normalClosure
  have hA' : Nat.card (A.subgroupOf K) = 3 := by rw [card_subgroupOf_eq hAK, hA]
  have hwc' := weaklyClosed_subgroupOf hAK hwc
  have hco : IsCoatom (Subgroup.normalizer ((A.subgroupOf K : Subgroup ↥K) : Set ↥K)) := by
    rcases hrest with hG | hU | hJ
    · exact hG2 ↥K hG _ hA' hwc'
    · exact hUJ ↥K (Or.inl hU) _ hA' hwc'
    · exact hUJ ↥K (Or.inr hJ) _ hA' hwc'
  rw [← Subgroup.subgroupOf_normalizer_eq hAK] at hco
  intro W hNW hWK
  have hle : (Subgroup.normalizer (A : Set Y)).subgroupOf K ≤ W.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hNW (Subgroup.mem_inf.mpr ⟨hx, x.2⟩)
  rcases hco.le_iff.mp hle with htop | heq
  · exact Or.inr (le_antisymm hWK (Subgroup.subgroupOf_eq_top.mp htop))
  · have h := Subgroup.subgroupOf_inj.mp heq
    rw [inf_of_le_left hWK] at h
    exact Or.inl h

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
