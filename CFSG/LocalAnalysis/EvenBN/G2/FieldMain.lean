module

public import CFSG.LocalAnalysis.EvenBN.G2.FieldRank
public import CFSG.LocalAnalysis.EvenBN.G2.FieldCyclic
public import CFSG.LocalAnalysis.EvenBN.G2.EndgameBase

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise MatrixGroups

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_fieldCase (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hsyl : IsSylowOf 2 (yamadaP d t) (yamadaN₂ d t)) {α : ↥(yamadaBarK₂ d t) ≃* SL(2, K)}
    (hex : ExactClosure (yamadaBarK₂ d t) α (yamadaT₂ d t) (yamadaBarP₂ d t) f)
    (hF : FieldAlternative (yamadaBarK₂ d t) (yamadaT₂ d t) f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hR₈, htN, htP⟩, -, -⟩ := h.yamada_5_51 hW d hK hQ
  have hQp : IsPGroup 2 (yamadaP d t ⊔ zpowers t : Subgroup G) := by
    rw [hR₈]
    exact LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQN : (yamadaP d t ⊔ zpowers t : Subgroup G) ≤ normalizer (yamadaP d t : Set G) :=
    sup_le le_normalizer ((zpowers_le).2 htN)
  obtain ⟨B₀, hB₀⟩ := (hQp.comap_subtype (K := normalizer (yamadaP d t : Set G))).exists_le_sylow
  set B : Subgroup G := (B₀ : Subgroup (normalizer (yamadaP d t : Set G))).map
    (normalizer (yamadaP d t : Set G)).subtype with hBdef
  have hB : IsSylowOf 2 B (normalizer (yamadaP d t : Set G)) := ⟨B₀, rfl⟩
  have hQB : (yamadaP d t ⊔ zpowers t : Subgroup G) ≤ B := fun x hx =>
    ⟨⟨x, hQN hx⟩, hB₀ (mem_subgroupOf.2 hx), rfl⟩
  have hPB : yamadaP d t ≤ B := le_sup_left.trans hQB
  have htB : t ∈ B := hQB (mem_sup_right (mem_zpowers t))
  haveI : ((yamadaP d t).subgroupOf B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hB.le
  have hcyc := h.isCyclic_quotient_yamadaP_of_field hW d hK hQ hsyl hex hF hB hPB
  have hfus := h.field_conj_t_not_mem_yamadaP hW d hK hQ hsyl hex hF
  have hcoset := h.yamadaP_conj_coset hW d hK hQ
  have hgen := h.yamadaP_le_closure_involutions hW d hK hQ
  obtain ⟨-, hFT⟩ := Common.sylow_and_firstTransferData_of_isCyclic hB hPB hcyc htB htP h.ht hfus
    hcoset hgen
  have := h.isPerfect
  exact CFSG.LocalAnalysis.perfect_first_transfer_exclusion ⟨_, _, _, hFT⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
