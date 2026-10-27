module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorSocle
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

@[expose] def KFactThreeCoverInvolve : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → Subgroup.center K ≠ ⊥ →
    IsPGroup 3 (Subgroup.center K) → Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
    ∀ (B : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup 3 L → ∀ f : B →* L,
      Function.Surjective f →
      (∀ d : TauCeti.ValidLieTypeIndex, ((∃ n, IsLinTwoIndex 3 n d) ∨ IsSpFourIndex 3 d) →
        IsEmpty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)) ∧
      IsEmpty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 9)) ∧
      ∀ s : TauCeti.SporadicName, P1ThreeSporList 3 s →
        IsEmpty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group)

variable {X : Type} [Group X] [Finite X]

theorem false_of_rankOne_of_surjective {p : ℕ} {Rb : Sylow p X} {X₀ : Subgroup X}
    (h : ReducedNongeneration p X Rb X₀) (hX : CatalogSimpleSections X) (hInv : KFactCaseTwoInv)
    (h3 : Open.pRank p (Rb : Subgroup X) ≤ 3) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hnc : ¬ IsCyclic ((Rb : Subgroup X) ⊓ K : Subgroup X))
    (hz : ∃ z ∈ (Rb : Subgroup X), z ∉ K ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (K : Set X))
    {B : Subgroup K} {L : Type} [Group L] (hiso : IsCaseTwoGroup p L) (f : B →* L)
    (hf : Function.Surjective f) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
  have hZ := h.center_eq_bot_of_rankOne hK hnc hzR hzK hzp hzc
  obtain ⟨hNU, hKY₀⟩ := h.rankOne_principle hK hnc hzR hzK hzp hzc
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have hKs : IsSimpleGroup K := e.isSimpleGroup
  have hKnab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  have hKcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hX.isCatalogGroup_center_quotient hK)
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hp35 : p = 3 ∨ p = 5 := by
    obtain ⟨d, hd | hd, -⟩ := hiso
    · exact Or.inl hd.1
    · exact Or.inr hd.1
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hc => hnc (by
    rw [← hT]
    exact isCyclic_of_surjective _ ((T : Subgroup K).equivMapOfInjective K.subtype
      K.subtype_injective).surjective)
  exact hInv K hKs hKnab hKcat p hp35 T hTnc (h.glbCore_ne_top_of_rankOne hNU hKY₀ hT)
    (h.pRank_top_le_two_of_mem_centralizer h3 hT hzR hzK hzp hzc) B L hiso f hf

theorem false_of_center_shape {Rb : Sylow 3 X} {X₀ : Subgroup X}
    (h : ReducedNongeneration 3 X Rb X₀) (hX : CatalogSimpleSections X)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    (hCin : KFactChevTwoInnerGen) (hCout : KFactChevTwoOuterGen)
    (hSchur : KFactChevTwoSurvivorSchur) (hKU1 : KFactUnitarySchur) (hKR1 : KFactReeSchur)
    (hKT : KFactThreeCoverInvolve) (h3 : Open.pRank 3 (Rb : Subgroup X) = 3) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = 3) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K)
    (hnc : ¬ IsCyclic ((Rb : Subgroup X) ⊓ K : Subgroup X))
    (hcent : ∀ c ∈ (Rb : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype)
    {B : Subgroup K} {L : Type} [Group L] (hiso : IsCaseTwoGroup 3 L) (f : B →* L)
    (hf : Function.Surjective f) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  have hZ3 : IsPGroup 3 (Subgroup.center K) := isPGroup_center_of_isComponentOf hp h.core_eq_bot hK
  have hZne : Subgroup.center K ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hw, hwz⟩ := hcent z ⟨mem_sylow_of_mem_center hz hzp Rb,
      Subgroup.center_le_centralizer _ hz⟩ hzp
    have hw1 : w = 1 := by simpa [hbot] using hw
    have : z = 1 := by rw [← hwz, hw1]; rfl
    rw [this, orderOf_one] at hzp
    omega
  obtain ⟨T₀, hT₀⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hm3 : Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    have e1 := (CFSG.SectionRank.pRank_sylow T₀).1
    have e2 := pRank_map_of_injective 3 hp K.subtype K.subtype_injective (T₀ : Subgroup K)
    rw [hT₀] at e2
    have e3 := pRank_mono 3 hp (inf_le_left : (Rb : Subgroup X) ⊓ K ≤ Rb)
    omega
  have hKT' := hKT K hK.2.2 hZne hZ3 hm3 B L hiso f hf
  have hmem : ∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = 3 → c ∈ K :=
    fun c hc hcp => mem_of_mem_centralizer_of_orderOf_eq Rb hKn
      (fun c hc hcp => Subgroup.map_subtype_le _ (hcent c hc hcp)) hc hcp
  have hCp := isPGroup_centralizer_of_forall_mem hp h.ne_two h.core_eq_bot hKn hmem
  have hCZ : ∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ (Subgroup.center K).map K.subtype := fun c hc hcp =>
    mem_map_center_of_mem_of_mem_centralizer (hmem c hc hcp) hc
  obtain ⟨-, hnonab, i, ⟨e⟩⟩ : IsSimpleGroup (K ⧸ Subgroup.center K) ∧
      (∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a) ∧ IsCatalogGroup (K ⧸ Subgroup.center K) :=
    ⟨hK.2.2.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
      hK.2.2, hX.isCatalogGroup_center_quotient hK⟩
  cases i with
  | cyclic q hq => exact not_nonempty_mulEquiv_zmod hnonab ⟨e⟩
  | alternating n hn =>
    have h9 := hP1A 3 X Rb X₀ h hX K hK huniq hnc hcent n hn ⟨e⟩
    subst h9
    exact hKT'.2.1.false e
  | sporadic s => exact (hKT'.2.2 s (hP1S 3 X Rb X₀ h hX K hK huniq hnc hcent s ⟨e⟩)).false e
  | lie d =>
    have hinner : IsChevTwoInnerIndex d → False := fun hdi => by
      have htop := hCin d hdi K hK.2.2 ⟨e⟩ hZ3 (h.isCyclic_center hK hKn)
      have hle := le_of_weakCore_eq_top h T₀ hT₀ (htop T₀)
      have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
      have : Nontrivial K := (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
      have h3' := three_le_pRank_of_weakCore_eq_top hp (htop T₀)
      rw [← pRank_map_of_injective 3 hp K.subtype K.subtype_injective, hT₀] at h3'
      exact false_of_le_of_three_le_pRank h hle (h3'.trans (pRank_mono 3 hp inf_le_right))
    have houter : IsChevTwoOuterIndex d → False := fun hdo => by
      have hW := hCout.2 d hdo X K hKn hK.2.2 ⟨e⟩ hCp hCZ Rb h.three_le_pRank
      have hCR := IsPGroup.le_sylow_of_normal hCp Rb
      have : Group.IsPerfect K := ⟨hK.2.2.1⟩
      exact false_of_le_of_normal_sup h (hW.trans h.weakCore_le)
        (normal_sup_of_outer K e Rb hCR (hCout.1 d hdo))
    have hsurv : IsChevTwoSurvivorIndex 3 d → False := fun hds =>
      hZne (hSchur K 3 d hds hK.2.2 hZ3 ⟨e⟩)
    rcases hP1L 3 X Rb X₀ h hX K hK huniq hnc hcent d ⟨e⟩ with hl | hu | hr | hsp | hc2
    · exact (hKT'.1 d (Or.inl hl)).false e
    · exact hZne (hKU1 K 3 d hu hK.2.2 hZ3 ⟨e⟩)
    · exact hZne (hKR1 K d hr hK.2.2 hZ3 ⟨e⟩)
    · exact (hKT'.1 d (Or.inr hsp)).false e
    · rcases hc2 with ⟨-, q, hq, hq1, hd | hd | hd | hd | hd | hd | hd | hd⟩ |
        ⟨-, q, hq, hq3, hd | hd | hd | hd⟩ | ⟨h35, -⟩
      · exact hsurv (Or.inl ⟨rfl, q, hq, hq1, hd⟩)
      · exact hinner ⟨q, hq, hq1, Or.inl hd⟩
      · exact hinner ⟨q, hq, hq1, Or.inr (Or.inl hd)⟩
      · exact hinner ⟨q, hq, hq1, Or.inr (Or.inr (Or.inl hd))⟩
      · exact hinner ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inl hd)))⟩
      · exact hinner ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hd))))⟩
      · exact hinner ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hd))))⟩
      · exact houter (Or.inl ⟨q, hq, hq1, hd⟩)
      · exact hsurv (Or.inr (Or.inl ⟨rfl, q, hq, hq3, hd⟩))
      · exact hsurv (Or.inr (Or.inr (Or.inl ⟨rfl, q, hq, hq3, hd⟩)))
      · exact houter (Or.inr ⟨q, hq, hq3, Or.inl hd⟩)
      · exact houter (Or.inr ⟨q, hq, hq3, Or.inr hd⟩)
      · omega

end CFSG.AGLEmbedding
