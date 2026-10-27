module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7E0
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SStd
public import CFSG.ClassicalInvolution.Asc77.AscT7AEStand
import CFSG.ClassicalInvolution.Q3.Q3T7EApp

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Apply

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem centralizersSylowPairs_of_stdCent_a7 (hΩ : HypOmegaGen Ω) {K H : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (h : StdCent Ω K H z) : CentralizersSylowPairs Ω K H :=
  CFSG.ClassicalInvolution.Q3.Q3T7E.centralizersSylowPairs_of_stdCent3 hΩ hz h

end Apply

section Datum


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_estandA7 {K K' : Subgroup G} (hst : Std2A7 Ω K) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) : ∃ (S : Sylow 2 G) (R W : Subgroup G), EStandA7 Ω K S R W := by
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hne.symm hz hzK'
  obtain ⟨R', hR', hR'fix⟩ := Asc77.exists_sylow_normalized hR₀.2.1 (hR₀.1.trans hKN)
  have hRn : R₀ ≤ Subgroup.normalizer (R' : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix r hr)
  have h2 : IsPGroup 2 ↥(R₀ ⊔ R') := hR₀.2.1.to_sup_of_normal_right' hR'.2.1 hRn
  obtain ⟨S, hS⟩ := h2.exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  refine ⟨S, R₀, ⨆ U ∈ η, U, ?_⟩
  refine
    { hyp := hΩ
      classical := hst.classical
      below := hst.below
      mem := hK
      aEmpty := hst.aEmpty K hK
      twin := ⟨K', hK', hne, R', mem_RSet_of_isSylow2In hK'Ω hR', hR'.1,
        le_sup_right.trans hS⟩
      hR := ⟨mem_RSet_of_isSylow2In hK hR₀, hR₀.1, le_sup_left.trans hS⟩
      hW := ⟨⟨η, ⟨S, hη, hηinv⟩, rfl⟩, ?_, fun s hs => T7A.conjSub_eta_eq hηinv hs⟩ }
  exact iSup₂_le fun U hU => (hη.1 hU).2

theorem a7ThmE_apply (hE : A7ThmE) {K K' : Subgroup G} {z : G} (hst : Std2A7 Ω K)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) {H : Subgroup G}
    (hstd : StdCent Ω K H z)
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) : H = ⊤ := by
  obtain ⟨S, R, W, hS⟩ := exists_estandA7 hst hK' hne
  exact hE G Ω K S R W H hS ⟨htrans, centralizersSylowPairs_of_stdCent_a7 hst.hyp hz hstd⟩

end Datum

end CFSG.ClassicalInvolution.Hat2A7S
