module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoreMirror
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Pump
public import CFSG.LocalAnalysis.ComponentClassification.CTUMaxTwoAt
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdSol

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

@[expose] def L34FieldNormalSetting (G : Type) [Group G] [Finite G] (t : G) (P : Subgroup G) :
    Prop :=
  L34BaseSetting G ∧ orderOf t = 2 ∧ P ≤ centralizer ({t} : Set G) ∧
    IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G))) ∧
    (P.subgroupOf (centralizer ({t} : Set G))).Normal ∧
    ∃ m : ℕ, 4 ≤ m ∧ Even m ∧ Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 m

@[expose] def L34FieldSignalizerVanishing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (P : Subgroup G), L34FieldNormalSetting G t P →
    ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = ⊥

@[expose] def L34FieldCoreOfSignalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (P : Subgroup G), L34FieldNormalSetting G t P →
    (∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = ⊥) →
    ⁅oddIn P, P⁆ = ⊥

section Certified


theorem l34FieldCoreStepMirror_of_signalizer
    (hS : SchreierFor Blueprint.Catalog) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h13 : Sol76T13.SolomonThm13Simple)
    (hS0 : L34FieldSignalizerVanishing) (hS1 : L34FieldCoreOfSignalizer) :
    L34FieldCoreStepMirror := by
  intro G _ _ hG J hJmm hJτ b t hb hJb hJp ht hbt hJt
  obtain ⟨hsimple, hna, hK, -, -, -, -, -⟩ := id hG
  have := hsimple
  obtain ⟨hsF, hnF, hoF⟩ := GrS5.fstar_facts hG
  obtain ⟨n, hn, hnev, hJL⟩ := hJτ
  have hJw : GSWeakMaximalComponent J := hJmm.gsWeakMaximalComponent ⟨b, hb, hJb, hJp⟩
  have hJsol : FooteLit.IsSolomonMaximal J :=
    Foote5.SolMax.isSolomonMaximal_of_gsMirrorMaximal hsF hnF hb ⟨hJb, hJp⟩ hJmm
  have hJtype : SuzONanFieldType (J ⧸ Open.fusionZStar J) :=
    Or.inr (Or.inr ⟨n, hn, hnev, hJL⟩)
  have hJrank : 3 ≤ pRank 2 ↥J := three_le_pRank_of_lieModel_fusionZStar (by omega) hJL
  have hT9J := Sol76.maximalTwoComponentSimple_at_of_solomonMaximal hCI hGA hsF hnF hoF h13 hK
    hJw (by omega) (not_psp4_of_suzONanFieldType hJtype) hJsol ht hJt
  have htZ : t ∉ center G := GSLit.not_mem_center_of_orderOf_eq_two hna ht
  have hPt : pumpUp J t ≤ centralizer ({t} : Set G) := GrS5.pumpUp_le_centralizer J t
  have hPp : IsPComponent 2 ((pumpUp J t).subgroupOf (centralizer ({t} : Set G))) :=
    GrS5.isPComponent_pumpUp hS hK hb ht hbt htZ hJb hJp hJt hT9J.1
  have hreach : FooteLit.GSMirrorReach J (pumpUp J t) :=
    FooteLit.GSMirrorReach.tail_corr Relation.ReflTransGen.refl
      (GSWeakCorr.of_gsCorr (GrS5.gsCorr_pumpUp hS hK hb ht hbt htZ hJb hJp hJt hT9J.1))
  have hPmm : FooteLit.GSMirrorMaximal (pumpUp J t) := fun M hM => by
    obtain ⟨e₁⟩ := hJmm _ hreach
    obtain ⟨e₂⟩ := hJmm M (hreach.trans hM)
    exact ⟨e₁.symm.trans e₂⟩
  obtain ⟨eJP⟩ := hJmm _ hreach
  have hPL : Blueprint.LieModel (pumpUp J t ⧸ Open.fusionZStar (pumpUp J t)) .PSL 3 2 n :=
    LieType.CurtisTits.lieModel_of_mulEquiv eJP hJL
  have hPw : GSWeakMaximalComponent (pumpUp J t) :=
    hPmm.gsWeakMaximalComponent ⟨t, ht, hPt, hPp⟩
  have hPsol : FooteLit.IsSolomonMaximal (pumpUp J t) :=
    Foote5.SolMax.isSolomonMaximal_of_gsMirrorMaximal hsF hnF ht ⟨hPt, hPp⟩ hPmm
  have hPtype : SuzONanFieldType (pumpUp J t ⧸ Open.fusionZStar (pumpUp J t)) :=
    Or.inr (Or.inr ⟨n, hn, hnev, hPL⟩)
  have hPrank : 3 ≤ pRank 2 ↥(pumpUp J t) :=
    three_le_pRank_of_lieModel_fusionZStar (by omega) hPL
  have hT9P := Sol76.maximalTwoComponentSimple_at_of_solomonMaximal hCI hGA hsF hnF hoF h13 hK
    hPw (by omega) (not_psp4_of_suzONanFieldType hPtype) hPsol ht hPt
  have hPnorm : centralizer ({t} : Set G) ≤ normalizer (pumpUp J t : Set G) :=
    GrS5.centralizer_le_normalizer_of_isPComponent (hT9P.2 hPrank) hPt hPp
  have hPN : ((pumpUp J t).subgroupOf (centralizer ({t} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPt).mpr hPnorm
  have hset : L34FieldNormalSetting G t (pumpUp J t) := ⟨hG, ht, hPt, hPp, hPN, n, hn, hnev, hPL⟩
  have hcomm : ⁅oddIn (pumpUp J t), pumpUp J t⁆ = ⊥ := hS1 G t _ hset (hS0 G t _ hset)
  have hgs := GrS5.gsFixedLayer_eq_of_le hJb hJp hJt
  have hsup := GrS5.sup_oddIn_pumpUp hJt hgs hT9J.1
  have hperf : ⁅pumpUp J t, pumpUp J t⁆ = pumpUp J t := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hPp
    have h2 : Group.IsPerfect ↥(pumpUp J t) :=
      Group.IsPerfect.ofSurjective
        (f := (subgroupOfEquivOfLe (GrS5.pumpUp_le_centralizer J t)).toMonoidHom)
        (subgroupOfEquivOfLe (GrS5.pumpUp_le_centralizer J t)).surjective
    exact (Subgroup.isPerfect_iff (H := pumpUp J t)).mp h2
  have hOP : oddIn (pumpUp J t) ≤ (center ↥(pumpUp J t)).map (pumpUp J t).subtype := by
    intro o ho
    refine ⟨⟨o, map_subtype_le _ ho⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    have h1 : ⁅o, (y : G)⁆ ∈ (⊥ : Subgroup G) := hcomm ▸ commutator_mem_commutator ho y.2
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  by_contra hbad
  exact GrS5.not_oddIn_le_center_pumpUp hsup hperf hbad hOP

end Certified

end CFSG.ComponentClassification.GrSLit.L34Sec5S
