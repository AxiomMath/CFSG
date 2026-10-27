module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma551
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isPComponent_centralizer_t
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    {K : Subgroup G} (hKt : K ≤ centralizer ({t} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({t} : Set G))))
    (htype : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f) ∨
      IsL34Type (K ⧸ Open.fusionZStar K)) : K = L := by
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, -, htS, -, -⟩ := hset'
  have htQ : t ∈ S ⊓ coreActionKernel L := mem_inf.mpr ⟨htS,
    mem_coreActionKernel_of_commute fun l hl => (mem_centralizer_singleton_iff.mp (hLt hl)).symm⟩
  obtain ⟨-, -, -, hK, -⟩ := isPComponent_eq_of_setting hS hU hheld hSol hGW hMax hL34 hset htQ
    hto hKt hKp htype
  rw [hK, gsFixedLayer_eq_of_le hLt hLpt hLt]
  apply le_antisymm
  · exact iSup₂_le fun g hg => (conjugate_eq_self (hCN hg)).le
  · exact le_iSup₂_of_le 1 (one_mem _) (conjugate_one L).ge

theorem oddIn_inf_centralizer_le_of_conj
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUC : L34UnitaryCentralizerFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {n : G}
    (hnS : n ∈ normalizer (S : Set G)) :
    oddIn L ⊓ centralizer ({n⁻¹ * t * n} : Set G) ≤
      oddIn (centralizer ({n⁻¹ * t * n} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨hbase, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, -, hSyl, htS, -, -⟩ := hset'
  set s := n⁻¹ * t * n with hs
  have hsS : s ∈ S := by
    have h := (mem_normalizer_iff.mp (inv_mem hnS) t).mp htS
    rwa [inv_inv] at h
  have hs2 : orderOf s = 2 := by
    rw [hs, show n⁻¹ * t * n = MulAut.conj n⁻¹ t by simp, MulEquiv.orderOf_eq, hto]
  have hts : t * s = s * t := (hZS s hsS).symm
  have hXt : oddIn L ≤ oddIn (centralizer ({t} : Set G)) :=
    GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt
  have hYD : oddIn L ⊓ centralizer ({s} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({s} : Set G) := inf_le_inf_right _ hXt
  by_contra hY
  obtain ⟨K₁, hK₁s, hK₁p, hK₁n⟩ := exists_isPComponent_not_le hSol hto hs2 hts hYD hY
  have hT := gsUnbalancingTriple_of_not_le hSol hto hs2 hts hK₁s hK₁p hYD hK₁n
  have htypes := hbase.2.2.2.2.2.2.2 s t K₁ hT
  obtain ⟨h1, h2⟩ := GSThmB.Six.isPComponent_conjugate hK₁s hK₁p n⁻¹
  rw [conjugate_centralizer_singleton, show n⁻¹⁻¹ * s * n⁻¹ = t by rw [hs]; group] at h1 h2
  have hK₁L := eq_of_isPComponent_centralizer_t hS hU hheld hSol hGW hMax hL34 hset h1 h2
    (types_conjugate n⁻¹ htypes)
  have hK₁eq : K₁ = conjugate L n := by
    rw [← hK₁L, conjugate_conjugate, inv_mul_cancel, conjugate_one]
  have htype₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁) := by
    rw [hK₁eq]
    let e : ↥L ≃* ↥(conjugate L n) :=
      L.equivMapOfInjective (MulAut.conj n⁻¹).toMonoidHom (MulAut.conj n⁻¹).injective
    exact LieType.CurtisTits.lieModel_of_mulEquiv
      (FooteLit.nonempty_quotient_fusionZStar_equiv e).some htypeL
  have hRt : S ⊓ K₁ ≤ centralizer ({t} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (hZS y (mem_inf.mp hy).1)
  have hR2 : IsPGroup 2 ↥(S ⊓ K₁) := (IsSylowTwoIn.isPGroup hSyl).to_le inf_le_left
  have h8 := card_le_eight_of_unitary hUnit hUC hT htype₁ inf_le_right hRt hR2
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := by
    exact isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
      (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have h64 : 64 ∣ Nat.card L := by
    have h1 := GSThmB.card_of_lieModel_L34 htypeL
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.fusionZStar ↥L)
    rw [h1] at h2
    rw [h2]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hge := sixtyFour_le_card_of_isSylowTwoIn hS₀ h64
  have hcard : Nat.card ↥(S ⊓ K₁) = Nat.card ↥(S ⊓ L) := by
    have hconjS : conjugate S n = S := conjugate_eq_self hnS
    have heqR : S ⊓ conjugate L n = conjugate (S ⊓ L) n := by
      calc S ⊓ conjugate L n = conjugate S n ⊓ conjugate L n := by rw [hconjS]
        _ = conjugate (S ⊓ L) n :=
          (Subgroup.map_inf_eq _ _ _ (MulAut.conj n⁻¹).injective).symm
    rw [hK₁eq, heqR]
    exact card_map_of_injective (MulAut.conj n⁻¹).injective
  omega

end CFSG.ComponentClassification.GrSLit.GrS5
