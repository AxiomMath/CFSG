module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1c
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1b

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G]

namespace Overlap

theorem inf_centralizer_eq_or_isSylowOf (h22 : Asc76Lemma22) {A R T V : Subgroup G} {g x : G}
    (hT : Overlap A R g T) (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (hnot : ¬ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTe : ¬ IsElemAbelian 2 T)
    (hCu : ∀ C' : Subgroup G, C' ≤ R → Nonempty (C' ≃* ↥(R ⊓ centralizer (T : Set G))) →
      C' = R ⊓ centralizer (T : Set G))
    (hV : Overlap A R x V)
    (hcard : ¬ IsSylowOf 2 V (rightConjugate (centralizer (A : Set G)) x) →
      Nat.card T ≤ Nat.card V) :
    IsSylowOf 2 V (rightConjugate (centralizer (A : Set G)) x) ∨
      R ⊓ centralizer (V : Set G) = R ⊓ centralizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hVs : IsSylowOf 2 V (rightConjugate (centralizer (A : Set G)) x)
  · exact Or.inl hVs
  right
  set C := R ⊓ centralizer (T : Set G) with hCdef
  have hCR : C ≤ R := inf_le_left
  have hRC : R ≤ normalizer (C : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hCR).mp (hT.normal_inf_centralizer h22 hm)
  have hVC : V ≤ normalizer (C : Set G) := by
    intro v hv
    have hvR : v ∈ normalizer (R : Set G) := hV.normalizesR hv
    have h1 : rightConjugate C v ≤ R := by
      rw [← (rightConjugate_eq_self_iff R v).mpr hvR]
      exact rightConjugate_le_rightConjugate hCR v
    have h2 := hCu _ h1 ⟨(C.equivMapOfInjective _ (MulAut.conj v⁻¹).injective).symm⟩
    exact (rightConjugate_eq_self_iff C v).mp h2
  have hS : IsPGroup 2 (R ⊔ V : Subgroup G) :=
    hT.sylowR.isPGroup.to_sup_of_normal_left' hV.sylow.isPGroup hV.normalizesR
  have hVC' : V ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    refine (inf_le_inf_left V hCR).trans ?_
    rw [inf_comm, hV.inf_eq_bot]
  have hcardC : Nat.card C ≤ Nat.card V := by rw [hT.card_inf_centralizer]; exact hcard hVs
  have hcomm := Asc76X.asc76Lemma23 G (R ⊔ V) V C hS le_sup_right hV.tightlyEmbedded_sup
    (hCR.trans le_sup_left) hVC hcardC hVC'
  have hCV : C ≤ R ⊓ centralizer (V : Set G) := by
    refine le_inf hCR ?_
    rw [commutator_comm] at hcomm
    exact (commutator_eq_bot_iff_le_centralizer).mp hcomm
  by_contra hne
  have hlt : C < R ⊓ centralizer (V : Set G) := lt_of_le_of_ne hCV (Ne.symm hne)
  have hVc : IsMulCommutative V := hV.isMulCommutative h22 hm hVs
  obtain ⟨eV⟩ := hV.mulEquiv
  have hU₀c : IsMulCommutative (R ⊓ centralizer (V : Set G) : Subgroup G) :=
    isMulCommutative_of_mulEquiv' eV hVc
  obtain ⟨r, hrU, hrC, hr2⟩ := exists_not_mem_sq_mem hlt
    (hT.sylowR.isPGroup.to_le inf_le_left) (inf_le_left.trans hRC)
  have hinv := hT.inv_of_sq_mem h22 hm hnot hTe r hrU.1 hrC hr2
  apply hTe
  have hCe : IsElemAbelian 2 C := by
    obtain ⟨eT⟩ := hT.mulEquiv
    refine ⟨isMulCommutative_of_mulEquiv' eT (hT.isMulCommutative h22 hm hnot), fun c hc => ?_⟩
    have h1 := hinv c hc
    have h2 : r * c = c * r :=
      congrArg Subtype.val (hU₀c.is_comm.comm ⟨r, hrU⟩ ⟨c, hCV hc⟩)
    have h3 : r * c * r⁻¹ = c := by rw [h2]; group
    rw [h3] at h1
    rw [sq]
    nth_rw 2 [h1]
    exact mul_inv_cancel c
  obtain ⟨eT⟩ := hT.mulEquiv
  exact Asc76X.isElemAbelian_of_mulEquiv eT hCe

end Overlap

end CFSG.ComponentClassification.Asc76.Sec5
