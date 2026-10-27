module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefL3QuotResidual
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenConstrained
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenDvdP1
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeConclusion
import CFSG.LocalAnalysis.RankThreeEvenClassification.HallTransport
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Background.InternalSecData
import CFSG.Quasithin.Background.InternalSecIso
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Exists
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11SecAFacts04
import CFSG.Quasithin.Vol2.Ch11SecBFacts22
import CFSG.Quasithin.Vol2.Ch11SecD552
import CFSG.Quasithin.Vol2.Ch11SecD556C
import CFSG.Quasithin.Vol2.Ch11SecD556O
import CFSG.Quasithin.Vol2.Ch11SecDFacts5
import CFSG.Quasithin.Vol2.Ch11SecE42S2a
import CFSG.Quasithin.Vol2.Ch11SecE42Setup
import CFSG.Quasithin.Vol2.Ch11SecE43
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.RankThreeEvenClassification.Helpers

variable {G : Type} [Group G] [Finite G]

theorem nonempty_modPrimeComplement_mulEquiv_of_map {G' : Type} [Group G'] [Finite G']
    {d : ℕ} (hd : d.Prime) (φ : G →* G') {A : Subgroup G} {A' : Subgroup G'}
    (hA : A.map φ = A') (hker : ¬ d ∣ Nat.card (φ.ker ⊓ A : Subgroup G)) :
    Nonempty (modPrimeComplement d A ≃* modPrimeComplement d A') := by
  classical
  let ψ : ↥A →* ↥A' :=
    (MulEquiv.subgroupCongr hA).toMonoidHom.comp (φ.subgroupMap A)
  have hψ : Function.Surjective ψ :=
    (MulEquiv.subgroupCongr hA).surjective.comp (MonoidHom.subgroupMap_surjective φ A)
  have hψker : ψ.ker = (φ.ker ⊓ A).subgroupOf A := by
    dsimp only [ψ]
    rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hA).injective,
      Subgroup.ker_subgroupMap, Subgroup.inf_subgroupOf_right]
  have hcard : Nat.card ψ.ker = Nat.card (φ.ker ⊓ A : Subgroup G) := by
    rw [hψker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := φ.ker ⊓ A) (K := A) inf_le_right).toEquiv
  refine CFSG.GroupTheory.nonempty_quot_primeComplementCore_mulEquiv hd ψ hψ ?_
  rw [hcard]
  exact hker

private theorem not_dvd_card_subgroupOf_primeComplementCore {d : ℕ} (hd : d.Prime)
    (X : Subgroup G) (N : Subgroup ↥X) :
    ¬ d ∣ Nat.card ((primeComplementCore (G := ↥X) d).subgroupOf N) := by
  have hcard : Nat.card ((primeComplementCore (G := ↥X) d).subgroupOf N) ∣
      Nat.card (primeComplementCore (G := ↥X) d) := by
    have h1 : Nat.card ((primeComplementCore (G := ↥X) d).subgroupOf N) =
        Nat.card ↥((primeComplementCore (G := ↥X) d) ⊓ N) := by
      rw [← Subgroup.inf_subgroupOf_right (primeComplementCore (G := ↥X) d) N]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (H := (primeComplementCore (G := ↥X) d) ⊓ N) (K := N) inf_le_right).toEquiv
    rw [h1]
    exact Subgroup.card_dvd_of_le
      (H := (primeComplementCore (G := ↥X) d) ⊓ N) (K := primeComplementCore (G := ↥X) d)
      inf_le_left
  exact fun hdvd => (primeComplementCore_properties ↥X d hd).2 (hdvd.trans hcard)

private theorem primeComplementCore_eq_bot_of_normal_quotient {d : ℕ} (hd : d.Prime)
    (X : Subgroup G) (O : Subgroup (modPrimeComplement d X)) (hO : O.Normal) :
    primeComplementCore (G := ↥O) d = ⊥ := by
  haveI : Finite (modPrimeComplement d X) :=
    Finite.of_surjective (QuotientGroup.mk' (primeComplementCore (G := ↥X) d))
      (QuotientGroup.mk'_surjective _)
  haveI : O.Normal := hO
  apply Subgroup.map_injective O.subtype_injective
  rw [Subgroup.map_bot]
  haveI hchar : (primeComplementCore (G := ↥O) d).Characteristic :=
    primeComplementCore_characteristic ↥O d hd
  haveI : ((primeComplementCore (G := ↥O) d).map O.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hcard : ¬ d ∣ Nat.card ((primeComplementCore (G := ↥O) d).map O.subtype) := by
    rw [Subgroup.card_subtype O (primeComplementCore (G := ↥O) d)]
    exact (primeComplementCore_properties ↥O d hd).2
  have hle : (primeComplementCore (G := ↥O) d).map O.subtype ≤
      primeComplementCore (G := modPrimeComplement d X) d :=
    le_primeComplementCore d _ inferInstance hcard
  rw [show primeComplementCore (G := modPrimeComplement d X) d = ⊥ from
    primeComplementCore_quotient_eq_bot (G := ↥X) d hd] at hle
  exact le_bot_iff.mp hle

private theorem nonempty_quot_oPPrimeHull_of_quotient {d : ℕ} (hd : d.Prime) (X : Subgroup G) :
    Nonempty ((↥(oPPrimeHull d (⊤ : Subgroup ↥X)) ⧸
        primeComplementCore (G := ↥(oPPrimeHull d (⊤ : Subgroup ↥X))) d) ≃*
      ↥(oPPrimeHull d (⊤ : Subgroup (modPrimeComplement d X)))) := by
  classical
  let C : Subgroup ↥X := primeComplementCore (G := ↥X) d
  let Q := modPrimeComplement d X
  let N : Subgroup ↥X := oPPrimeHull d (⊤ : Subgroup ↥X)
  let O : Subgroup Q := oPPrimeHull d (⊤ : Subgroup Q)
  haveI hCnorm : C.Normal := primeComplementCore_normal d ↥X
  haveI hQfin : Finite Q :=
    Finite.of_surjective (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
  let π : ↥X →* Q := QuotientGroup.mk' C
  haveI : Fact d.Prime := ⟨hd⟩
  have hNO : N.map π = O := by
    dsimp only [N, O, π]
    rw [S631.map_oPPrimeHull (G' := Q),
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
  haveI hNnorm : N.Normal := oPPrimeHull_top_normal d
  have hOnorm : O.Normal := by
    rw [← hNO]
    exact hNnorm.map π (QuotientGroup.mk'_surjective C)
  haveI : O.Normal := hOnorm
  let f : ↥N →* ↥O :=
    (MulEquiv.subgroupCongr hNO).toMonoidHom.comp (π.subgroupMap N)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hNO).surjective.comp (MonoidHom.subgroupMap_surjective π N)
  have hfker : f.ker = C.subgroupOf N := by
    dsimp only [f, π]
    rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hNO).injective,
      Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  have hfcard : ¬ d ∣ Nat.card f.ker := by
    rw [hfker]
    exact not_dvd_card_subgroupOf_primeComplementCore hd X N
  obtain ⟨eN⟩ := CFSG.GroupTheory.nonempty_quot_primeComplementCore_mulEquiv hd f hf hfcard
  have hcore_bot : primeComplementCore (G := ↥O) d = ⊥ :=
    primeComplementCore_eq_bot_of_normal_quotient hd X O hOnorm
  exact ⟨(eN.trans (QuotientGroup.quotientMulEquivOfEq hcore_bot)).trans
    QuotientGroup.quotientBot⟩

theorem nonempty_oPrimeModPrimeComplement_mulEquiv {d : ℕ} (hd : d.Prime) (X : Subgroup G) :
    Nonempty (oPrimeModPrimeComplement d X ≃* modPrimeComplement d (oPPrimeHull d X)) := by
  obtain ⟨eN⟩ := nonempty_quot_oPPrimeHull_of_quotient hd X
  let N : Subgroup ↥X := oPPrimeHull d (⊤ : Subgroup ↥X)
  have hmapN : N.map X.subtype = oPPrimeHull d X := map_subtype_oPPrimeHull_top X d
  let eNJ : ↥N ≃* ↥(oPPrimeHull d X) :=
    (Subgroup.equivMapOfInjective N X.subtype X.subtype_injective).trans
      (MulEquiv.subgroupCongr hmapN)
  have hcoreNJ : (primeComplementCore (G := ↥N) d).map eNJ.toMonoidHom =
      primeComplementCore (G := ↥(oPPrimeHull d X)) d :=
    primeComplementCore_map_equiv d hd eNJ
  let eQ : (↥N ⧸ primeComplementCore (G := ↥N) d) ≃*
      (↥(oPPrimeHull d X) ⧸ primeComplementCore (G := ↥(oPPrimeHull d X)) d) :=
    QuotientGroup.congr _ _ eNJ hcoreNJ
  exact ⟨eN.symm.trans eQ⟩

theorem nonempty_modPrimeComplement_congr {G' : Type} [Group G'] [Finite G'] {d : ℕ}
    {A : Subgroup G} {B : Subgroup G'} (e : ↥A ≃* ↥B) :
    Nonempty (modPrimeComplement d A ≃* modPrimeComplement d B) := by
  classical
  have hset : (Subgroup.map e.toMonoidHom) ''
      {H : Subgroup ↥A | H.Normal ∧ ¬ d ∣ Nat.card H} =
      {K : Subgroup ↥B | K.Normal ∧ ¬ d ∣ Nat.card K} := by
    ext K
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨H, ⟨hHn, hHc⟩, rfl⟩
      exact ⟨hHn.map e.toMonoidHom e.surjective, by
        rwa [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]⟩
    · rintro ⟨hKn, hKc⟩
      refine ⟨K.comap e.toMonoidHom, ⟨hKn.comap e.toMonoidHom, ?_⟩,
        Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective K⟩
      rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom)
        (K := K.comap e.toMonoidHom) e.injective,
        Subgroup.map_comap_eq_self_of_surjective e.surjective]
      exact hKc
  have hcore : (primeComplementCore (G := ↥A) d).map e.toMonoidHom =
      primeComplementCore (G := ↥B) d := by
    unfold primeComplementCore
    rw [(Subgroup.gc_map_comap e.toMonoidHom).l_sSup, ← sSup_image, hset]
  exact ⟨QuotientGroup.congr _ _ e hcore⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
