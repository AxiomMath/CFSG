module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Witness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.J3Target

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open CFSG.Blueprint

theorem mem_normalizer_of_map_eq {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom ↔ x ∈ A :=
    Subgroup.mem_map_iff_mem (MulAut.conj g).injective
  rw [h] at key
  exact key.symm

theorem centralFusionAt_of_J3
    {K : Type} [Group K] [Finite K] (e : K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :
    CentralFusionAt K := by
  obtain ⟨hOut, -⟩ := CFSG.AGLEmbedding.kFactJ3OuterRank_closed
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv K ⟨e⟩
  refine ⟨fun h => ?_, ?_⟩
  · have := Nat.le_of_dvd Nat.card_pos h
    omega
  intro T A hAT hAc hA
  have hF := CFSG.AGLEmbedding.kFactJ3Sylow K ⟨e⟩ T
  by_contra hcon
  push Not at hcon
  have hle : Subgroup.normalizer ((T : Subgroup K) : Set K) ≤
      Subgroup.normalizer ((A : Subgroup K) : Set K) := fun g hg =>
    mem_normalizer_of_map_eq (hcon g hg)
  have hAZ : A ≤ CFSG.Quasithin.centerOf (T : Subgroup K) := by
    intro a ha
    refine Subgroup.mem_inf.2 ⟨hAT ha, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (hAc a ha t ht).symm
  rcases hF.center_irreducible A hAZ hle with h0 | h9
  · rw [h0, Subgroup.card_bot] at hA
    omega
  · rw [h9, hF.center_elem.2] at hA
    omega

theorem dichThreeAt_of_J3
    {K : Type} [Group K] [Finite K] (e : K ≃* NativeSporadic.Carrier .J3) : DichThreeAt K := by
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :=
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  exact dichThreeAt_of_centralFusion (centralFusionAt_of_J3 (e.trans b))

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
