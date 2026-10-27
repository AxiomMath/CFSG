module

public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Assembly

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Uniqueness CFSG.ABGLocalTools Subgroup

theorem stage2PQExists_proved : Stage2PQExists := by
  intro G _ _ x K A hJ hS
  have hKC : K ≤ centralizer ({x} : Set G) := hJ.1.1.1.2.2.1
  have hNC : CxK x K ≤ centralizer ({x} : Set G) := inf_le_left
  have hKN : K ≤ NxK x K := le_inf hKC Subgroup.le_normalizer
  have hHN : K ⊔ CxK x K ≤ normalizer ((CxK x K : Subgroup G) : Set G) :=
    sup_le (hKN.trans (NxK_le_normalizer_CxK x K)) Subgroup.le_normalizer
  have hHC : K ⊔ CxK x K ≤ centralizer ({x} : Set G) := sup_le hKC hNC
  have hxN : x ∈ CxK x K := mem_CxK_self hKC
  have hAH : A ≤ K ⊔ CxK x K := by
    rcases hS.2.2.2 with ⟨hAK, -⟩ | ⟨E, hEK, hAE, -⟩
    · exact hAK.trans le_sup_left
    · rw [hAE]
      exact sup_le (hEK.trans le_sup_left) (zpowers_le.2 (le_sup_right (a := K) hxN))
  have hAp : IsPGroup 2 ↥A := by
    have := hS.2.1
    exact IsElementaryAbelian.isPGroup 2 ↥A
  obtain ⟨S, hSH, hAS⟩ := exists_isSylowOf_ge_of_le hAH hAp
  obtain ⟨P, hPC, hSP⟩ := exists_isSylowOf_ge_of_le (hSH.le.trans hHC) hSH.isPGroup
  have hSN : IsSylowOf 2 (S ⊓ CxK x K) (CxK x K) :=
    hSH.inf_of_le_normalizer le_sup_right hHN
  have hPN : P ⊓ CxK x K = S ⊓ CxK x K :=
    hSN.eq_of_le (inf_le_inf_right _ hSP) inf_le_right hPC.isPGroup.to_inf_left
  refine ⟨P, P ⊓ CxK x K, hPC, hAS.trans hSP, rfl, ?_⟩
  rw [hPN]
  exact hSN

end CFSG.GH74.Generic.BProg
