module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTransport

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn normIn centIn)
open CFSG.OddStandard.HigherRank.YamadaG23 (IsQuotIso LitStrothType StrothSigma6
  lit_isQuotIso_subgroupOf)

section Transport

variable {Γ : Type} [Group Γ] {S A : Subgroup Γ}

theorem sigma6_isE_subgroupOf {n : ℕ} (hAS : A ≤ S) (hA : IsE n ↥A) : IsE n ↥(A.subgroupOf S) := by
  obtain ⟨⟨hcomm, hsq⟩, hcard⟩ := hA
  let e : ↥(A.subgroupOf S) ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAS
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x _ => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply e.injective
    have h := congrArg Subtype.val
      (hcomm.is_comm.comm ⟨e x, Subgroup.mem_top _⟩ ⟨e y, Subgroup.mem_top _⟩)
    simpa [map_mul] using h
  · apply e.injective
    rw [map_pow, map_one]
    exact hsq _ (Subgroup.mem_top _)
  · rw [Nat.card_congr e.toEquiv, hcard]

theorem sigma6_centIn_subgroupOf_eq (hAS : A ≤ S) :
    (centIn S A).subgroupOf S = Subgroup.centralizer ((A.subgroupOf S : Subgroup ↥S) : Set ↥S) := by
  ext x
  simp only [centIn, Subgroup.inf_subgroupOf_left, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h a ha
    exact Subtype.ext (h a ha)
  · intro h a ha
    exact congrArg Subtype.val (h ⟨a, hAS ha⟩ ha)

theorem sigma6_normIn_subgroupOf_eq (hAS : A ≤ S) :
    (normIn S A).subgroupOf S = Subgroup.normalizer ((A.subgroupOf S : Subgroup ↥S) : Set ↥S) := by
  rw [normIn, Subgroup.inf_subgroupOf_left]
  exact Subgroup.subgroupOf_normalizer_eq hAS

end Transport

theorem strothSigma6_of_abstract
    (h : ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G), IsSimpleGroup G → IsE 4 ↥E →
      IsQuotIso (Subgroup.normalizer (E : Set G)) (Subgroup.centralizer (E : Set G))
        (Equiv.Perm (Fin 6)) →
      IsSylowIn 2 (Subgroup.centralizer (E : Set G)) E → LitStrothType G) :
    StrothSigma6 := by
  intro Γ _ _ S A hS hAS hA hQ hSyl
  refine h ↥S (A.subgroupOf S) hS (sigma6_isE_subgroupOf hAS hA) ?_ ?_
  · have hN : normIn S A ≤ S := inf_le_left
    have hQ' := lit_isQuotIso_subgroupOf (K := S) hN hQ
    rwa [sigma6_normIn_subgroupOf_eq hAS, sigma6_centIn_subgroupOf_eq hAS] at hQ'
  · obtain ⟨hle, hp, hidx⟩ := hSyl
    refine ⟨?_, ?_, ?_⟩
    · rw [← sigma6_centIn_subgroupOf_eq hAS]
      exact Subgroup.subgroupOf_mono S hle
    · exact hp.of_equiv (Subgroup.subgroupOfEquivOfLe hAS).symm
    · have hC : centIn S A ≤ S := inf_le_left
      rw [← sigma6_centIn_subgroupOf_eq hAS, Subgroup.relIndex_subgroupOf hC]
      exact hidx

end CFSG.CGT.Stroth77
