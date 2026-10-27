module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
import CFSG.LocalAnalysis.ComponentInitial.OddCoreQuotient
import CFSG.Quasithin.H13.VolIC129BorelMain
import CFSG.Quasithin.MS93.Sec2Basic
import CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.L34Exclusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBasic
import CFSG.Models.PGLOrders
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellStruct2

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X]

private theorem pCoreOf_two_inf_eq_pCoreOf_two {K : Subgroup X} (hKn : K.Normal) :
    K ⊓ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) = CFSG.Open.pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore 2]
  rw [CFSG.Open.pCoreOf]
  exact (CFSG.LocalAnalysis.ComponentInitial.pCore_normal_intersection 2 hKn).symm


theorem le_pCoreOf_two_of_commutator_le {K S Y : Subgroup X} (hS : IsPGroup 2 S) (hKn : K.Normal)
    (hKS : K ⊔ S = ⊤)
    (hKz : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥)
    (hYn : Y.Normal) (hcomm : ⁅Y, K⁆ ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) :
    Y ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) := by
  classical
  let O : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
  have hOnormal : O.Normal := by
    dsimp [O]
    haveI : (CFSG.pCore 2 (⊤ : Subgroup X)).Characteristic := CFSG.pCore_characteristic
    exact ConjAct.normal_of_characteristic_of_normal
  letI : O.Normal := hOnormal
  let π : X →* X ⧸ O := QuotientGroup.mk' O
  let Kbar : Subgroup (X ⧸ O) := K.map π
  let Ybar : Subgroup (X ⧸ O) := Y.map π
  have hF1 : K ⊓ O = CFSG.Open.pCoreOf 2 K := pCoreOf_two_inf_eq_pCoreOf_two (X := X) hKn
  have hKbar_normal : Kbar.Normal := by
    dsimp [Kbar]
    exact Subgroup.Normal.map hKn π (QuotientGroup.mk'_surjective O)
  have hYbar_normal : Ybar.Normal := by
    dsimp [Ybar]
    exact Subgroup.Normal.map hYn π (QuotientGroup.mk'_surjective O)
  have hcommbar : ⁅Ybar, Kbar⁆ = ⊥ := by
    have hmap := Subgroup.map_commutator Y K π
    rw [← hmap]
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    have hxO : x ∈ O := hcomm hx
    simpa [π, O, QuotientGroup.ker_mk'] using hxO
  have hcent : Ybar ≤ Subgroup.centralizer (Kbar : Set (X ⧸ O)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommbar
  have hYbar_inf_center : Ybar ⊓ Kbar ≤ CFSG.Quasithin.centerOf Kbar := by
    intro z hz
    rw [Subgroup.mem_inf] at hz
    refine Subgroup.mem_inf.mpr ⟨hz.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (hcent hz.1) w hw
  have hKbar_center : Subgroup.center Kbar = ⊥ := by
    let φ : K →* X ⧸ O := π.comp K.subtype
    have hφrange : φ.range = Kbar := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩
        exact Subgroup.mem_map_of_mem π k.2
      · intro hx
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
        exact ⟨⟨k, hk⟩, rfl⟩
    have hφker : φ.ker = CFSG.pCore 2 K := by
      ext k
      constructor
      · intro hk
        have hkO : (k : X) ∈ O := by
          have : φ k = 1 := hk
          simpa [φ, π, MonoidHom.mem_ker] using this
        have hmem : (k : X) ∈ K ⊓ O := Subgroup.mem_inf.mpr ⟨k.2, hkO⟩
        rw [hF1] at hmem
        exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp hmem
      · intro hk
        have hkO : (k : X) ∈ O := by
          have hmem : (k : X) ∈ CFSG.Open.pCoreOf 2 K :=
            Subgroup.mem_map_of_mem K.subtype hk
          rw [← hF1] at hmem
          exact hmem.2
        show φ k = 1
        simp [φ, π, MonoidHom.mem_ker, hkO, QuotientGroup.eq_one_iff]
    have eK : K ⧸ CFSG.pCore 2 K ≃* Kbar :=
      (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
        ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange))
    rw [← Subgroup.map_center_eq eK, hKz, Subgroup.map_bot]
  have hinfK : Y ⊓ K ≤ CFSG.Open.pCoreOf 2 K := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxYbar : π x ∈ Ybar := Subgroup.mem_map_of_mem π hx.1
    have hxKbar : π x ∈ Kbar := Subgroup.mem_map_of_mem π hx.2
    have hxbar_center : (⟨π x, hxKbar⟩ : Kbar) ∈ Subgroup.center Kbar := by
      have hxcenter := hYbar_inf_center (Subgroup.mem_inf.mpr ⟨hxYbar, hxKbar⟩)
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcenter.2 (w : X ⧸ O) w.2)
    have hxbar1 : π x = 1 := by
      rw [hKbar_center] at hxbar_center
      simpa using congrArg Subtype.val hxbar_center
    have hxO : x ∈ O := by
      have : x ∈ (QuotientGroup.mk' O).ker := by
        rw [MonoidHom.mem_ker]
        exact hxbar1
      simpa [QuotientGroup.ker_mk'] using this
    have hmem : x ∈ K ⊓ O := Subgroup.mem_inf.mpr ⟨hx.2, hxO⟩
    rw [hF1] at hmem
    exact hmem
  have hInfP : IsPGroup 2 ↥(Y ⊓ K) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K).to_le hinfK
  have hquotP : IsPGroup 2 (X ⧸ K) := by
    let f : S →* X ⧸ K := (QuotientGroup.mk' K).comp S.subtype
    have hf : Function.Surjective f := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K z
      have hx : x ∈ K ⊔ S := by rw [hKS]; exact Subgroup.mem_top x
      obtain ⟨k, hk, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      refine ⟨⟨s, hs⟩, ?_⟩
      show (QuotientGroup.mk' K) s = (QuotientGroup.mk' K) (k * s)
      have hk1 : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
      rw [map_mul, hk1, one_mul]
    exact IsPGroup.of_surjective hS f hf
  have hYp : IsPGroup 2 Y := by
    intro y
    obtain ⟨n, hn⟩ := hquotP (QuotientGroup.mk' K (y : X))
    have hzK : (y : X) ^ 2 ^ n ∈ K := by
      have h1 : QuotientGroup.mk' K ((y : X) ^ 2 ^ n) = 1 := by
        simpa only [map_pow] using hn
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hzY : (y : X) ^ 2 ^ n ∈ Y := Y.pow_mem y.2 _
    obtain ⟨m, hm⟩ := hInfP
      (⟨(y : X) ^ 2 ^ n, Subgroup.mem_inf.mpr ⟨hzY, hzK⟩⟩ : ↥(Y ⊓ K))
    refine ⟨n + m, Subtype.ext ?_⟩
    have hm' : ((y : X) ^ 2 ^ n) ^ 2 ^ m = 1 := by
      simpa using congrArg Subtype.val hm
    rw [pow_add, pow_mul]
    exact hm'
  exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 Y ⊤ le_top
    (by infer_instance) hYp


theorem gnC_eq_pCoreOf_or_le_gnC {K S : Subgroup X}
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X))
    (hS : IsPGroup 2 S)
    (hOS : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ S) (hKn : K.Normal)
    (hKS : K ⊔ S = ⊤)
    (hKz : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥)
    (hKsimple : IsSimpleGroup (K ⧸ CFSG.pCore 2 K)) :
    K ≤ CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC S ∨
      CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC S =
        CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) := by
  classical
  set C : Subgroup X := CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC S with hCdef
  set O : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) with hOdef
  set O2K : Subgroup X := CFSG.Open.pCoreOf 2 K with hO2Kdef
  have hCnormal : C.Normal := by
    rw [hCdef]
    infer_instance
  have hF1 : K ⊓ O = O2K := pCoreOf_two_inf_eq_pCoreOf_two (X := X) (K := K) hKn
  have hOleC : O ≤ C := by
    rw [hCdef, CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC]
    have hZleCO : CFSG.Quasithin.omegaOneCenterOf S ≤
        Subgroup.centralizer (O : Set X) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      have hzcentS : z ∈ CFSG.Quasithin.centerOf S :=
        CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf S hz
      exact Subgroup.mem_centralizer_iff.mp hzcentS.2 o (hOS ho)
    haveI : (Subgroup.centralizer (O : Set X)).Normal := Subgroup.normal_centralizer
    have hVleCO : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnV S ≤
        Subgroup.centralizer (O : Set X) := by
      rw [CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnV]
      exact Subgroup.normalClosure_le_normal hZleCO
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hVleCO hv) o ho).symm
  by_cases hle : C ⊓ K ≤ O2K
  · right
    have hcomm : ⁅C, K⁆ ≤ O := by
      have h1 : ⁅C, K⁆ ≤ C ⊓ K := Subgroup.commutator_le_inf C K
      exact h1.trans (hle.trans (by rw [← hF1]; exact inf_le_right))
    have hCle : C ≤ O :=
      le_pCoreOf_two_of_commutator_le (X := X) (K := K) (S := S) (Y := C)
        hS hKn hKS hKz hCnormal hcomm
    exact le_antisymm hCle hOleC
  · left
    set D : Subgroup X := C ⊓ K with hDdef
    have hDnormal : D.Normal := by
      rw [hDdef]
      infer_instance
    let q : K →* K ⧸ CFSG.pCore 2 K := QuotientGroup.mk' (CFSG.pCore 2 K)
    have hDsub_normal : (D.subgroupOf K).Normal := hDnormal.subgroupOf K
    haveI : (D.subgroupOf K).Normal := hDsub_normal
    have hmapne : (D.subgroupOf K).map q ≠ ⊥ := by
      intro hbot
      apply hle
      intro x hx
      rw [Subgroup.mem_inf] at hx
      have hxsub : (⟨x, hx.2⟩ : K) ∈ D.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
      have hxmap : q ⟨x, hx.2⟩ ∈ (D.subgroupOf K).map q :=
        Subgroup.mem_map_of_mem q hxsub
      rw [hbot, Subgroup.mem_bot] at hxmap
      have hxker : (⟨x, hx.2⟩ : K) ∈ q.ker := by
        rw [MonoidHom.mem_ker]
        exact hxmap
      rw [QuotientGroup.ker_mk'] at hxker
      exact Subgroup.mem_map_of_mem K.subtype hxker
    have hmaptop : (D.subgroupOf K).map q = ⊤ := by
      rcases hKsimple.eq_bot_or_eq_top_of_normal ((D.subgroupOf K).map q) with h | h
      · exact absurd h hmapne
      · exact h
    have hsupK : D.subgroupOf K ⊔ CFSG.pCore 2 K = ⊤ := by
      have hcomap := Subgroup.comap_map_eq q (D.subgroupOf K)
      rw [hmaptop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hO2KleC : CFSG.Open.pCoreOf 2 K ≤ C := by
      rw [← hO2Kdef, ← hF1]
      exact inf_le_right.trans hOleC
    intro k hk
    have hk_top : (⟨k, hk⟩ : K) ∈ (⊤ : Subgroup K) := Subgroup.mem_top _
    rw [← hsupK] at hk_top
    obtain ⟨d, hd, o, ho, hmul⟩ := Subgroup.mem_sup_of_normal_left.mp hk_top
    have hval : (d : X) * (o : X) = k := by
      simpa using congrArg Subtype.val hmul
    rw [← hval]
    have hdC : (d : X) ∈ C := (Subgroup.mem_subgroupOf.mp hd).1
    have hoC : (o : X) ∈ C := hO2KleC (Subgroup.mem_map_of_mem K.subtype ho)
    exact C.mul_mem hdC hoC


theorem normal_omegaOneCenterOf_of_le_gnC {K S : Subgroup X} (hKn : K.Normal) (hKS : K ⊔ S = ⊤)
    (hKleC : K ≤ CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC S) :
    (CFSG.Quasithin.omegaOneCenterOf S).Normal := by
  classical
  haveI : K.Normal := hKn
  set Z : Subgroup X := CFSG.Quasithin.omegaOneCenterOf S with hZ
  refine ⟨fun z hz g => ?_⟩
  have hg : g ∈ K ⊔ S := by rw [hKS]; exact Subgroup.mem_top g
  obtain ⟨k, hk, s, hs, hmul⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  have hkC : k ∈ CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC S := hKleC hk
  have hkcomm : k * z = z * k := by
    rw [CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC,
      Subgroup.mem_centralizer_iff] at hkC
    exact (hkC z (Subgroup.le_normalClosure hz)).symm
  have hconjS : s * z * s⁻¹ ∈ Z := by
    have hSfix : S.map (MulAut.conj s).toMonoidHom = S := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) y).mp hy
      · intro hx
        refine ⟨s⁻¹ * x * s, ?_, ?_⟩
        · simpa using
            (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (S.inv_mem hs)) x).mp hx
        · change s * (s⁻¹ * x * s) * s⁻¹ = x
          group
    have hZmap : Z.map (MulAut.conj s).toMonoidHom = Z := by
      rw [hZ, CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv, hSfix]
    have hmem : s * z * s⁻¹ ∈ Z.map (MulAut.conj s).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    rwa [hZmap] at hmem
  have hkcommW : k * (s * z * s⁻¹) = (s * z * s⁻¹) * k := by
    rw [CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC,
      Subgroup.mem_centralizer_iff] at hkC
    exact (hkC (s * z * s⁻¹) (Subgroup.le_normalClosure hconjS)).symm
  have hkconj : k * (s * z * s⁻¹) * k⁻¹ = s * z * s⁻¹ := by
    calc k * (s * z * s⁻¹) * k⁻¹ = (k * (s * z * s⁻¹)) * k⁻¹ := rfl
      _ = ((s * z * s⁻¹) * k) * k⁻¹ := by rw [hkcommW]
      _ = s * z * s⁻¹ := by group
  have hgoal : g * z * g⁻¹ = s * z * s⁻¹ := by
    rw [← hmul]
    calc (k * s) * z * (k * s)⁻¹ = k * (s * z * s⁻¹) * k⁻¹ := by group
      _ = s * z * s⁻¹ := hkconj
  rw [hgoal]
  exact hconjS


theorem normal_thompsonJ_of_le_pCoreOf {S : Subgroup X}
    (hOS : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ S)
    (hJS : CFSG.Quasithin.thompsonJ S ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) :
    (CFSG.Quasithin.thompsonJ S).Normal := by
  have hJeq : CFSG.Quasithin.thompsonJ (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) =
      CFSG.Quasithin.thompsonJ S :=
    (CFSG.Quasithin.thompsonJ_eq_of_le (S := S)
      (R := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) hJS hOS).symm
  rw [← hJeq]
  rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore 2]
  infer_instance


private theorem isLinThreeFour_projSL_three_four :
    CFSG.AGLEmbedding.IsLinThreeFour
      (CFSG.PGLModel.projSL 3 (GaloisField 2 2)) := by
  let q : TauCeti.PrimePower := ⟨2, 2, Nat.prime_two, by norm_num⟩
  have hq4 : q.card = 4 := by
    simp [q, TauCeti.PrimePower.card_def]
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [hq4]
    omega
  let d : TauCeti.ValidLieTypeIndex := ⟨.A 2 q, hv⟩
  have hcat : CFSG.AGLEmbedding.IsLinThreeFour (TauCeti.CFSGIndex.lie d).Group :=
    ⟨d, ⟨q, rfl, rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩
  have eCat : (TauCeti.CFSGIndex.lie d).Group ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 2) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 (GaloisField 2 2)).trans
        (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL
          3 (GaloisField 2 2)).symm)
  exact CFSG.AGLEmbedding.L34FF.isLinThreeFour_of_equiv eCat.symm hcat


theorem thompsonJ_le_pCoreOf_of_l34
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) {S K : Subgroup X}
    (hS : IsPGroup 2 S) (hOS : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ S)
    (hKn : K.Normal) (hKS : K ⊔ S = ⊤)
    (hKz : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥)
    (hKL : Nonempty ((K ⧸ CFSG.pCore 2 K) ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 2)))
    (hCeq : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC S =
      CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) :
    CFSG.Quasithin.thompsonJ S ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) := by
  classical
  set C : Subgroup X :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnC S with hCdef
  set O : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) with hO
  have hCnormal : C.Normal := by
    rw [hCdef]
    infer_instance
  letI : C.Normal := hCnormal
  let π : X →* X ⧸ C := QuotientGroup.mk' C
  let Kstar : Subgroup (X ⧸ C) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnImg S K
  have hKstar_map : Kstar = K.map π := rfl
  have hKstar_normal : Kstar.Normal := by
    rw [hKstar_map]
    exact Subgroup.Normal.map hKn π (QuotientGroup.mk'_surjective C)
  have hF1 : K ⊓ O = CFSG.Open.pCoreOf 2 K := pCoreOf_two_inf_eq_pCoreOf_two (X := X) (K := K) hKn
  let φ : K →* X ⧸ C := π.comp K.subtype
  have hφrange : φ.range = Kstar := by
    rw [hKstar_map]
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact Subgroup.mem_map_of_mem π k.2
    · intro hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨⟨k, hk⟩, rfl⟩
  have hφker : φ.ker = CFSG.pCore 2 K := by
    ext k
    constructor
    · intro hk
      have hkC : (k : X) ∈ C := by
        have : φ k = 1 := hk
        simpa [φ, π, MonoidHom.mem_ker] using this
      have hkO : (k : X) ∈ O := by
        rw [hCeq] at hkC
        exact hkC
      have hmem : (k : X) ∈ K ⊓ O := Subgroup.mem_inf.mpr ⟨k.2, hkO⟩
      rw [hF1] at hmem
      exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp hmem
    · intro hk
      have hkO : (k : X) ∈ O := by
        have hmem : (k : X) ∈ CFSG.Open.pCoreOf 2 K :=
          Subgroup.mem_map_of_mem K.subtype hk
        rw [← hF1] at hmem
        exact hmem.2
      have hkC : (k : X) ∈ C := by
        rw [hCeq]
        exact hkO
      show φ k = 1
      simp [φ, π, MonoidHom.mem_ker, hkC, QuotientGroup.eq_one_iff]
  have eK : K ⧸ CFSG.pCore 2 K ≃* Kstar :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange))
  obtain ⟨eCat⟩ := hKL
  have hKstar_lin : CFSG.AGLEmbedding.IsLinThreeFour Kstar :=
    CFSG.AGLEmbedding.L34FF.isLinThreeFour_of_equiv
      (eK.symm.trans eCat) isLinThreeFour_projSL_three_four
  have hKstar_simple : IsSimpleGroup Kstar :=
    CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.isSimpleGroup_of_isLinThreeFour hKstar_lin
  have hKstar_center : Subgroup.center Kstar = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.center_eq_bot_of_isLinThreeFour hKstar_lin
  have hKstar_perf : Group.IsPerfect Kstar :=
    CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.isPerfect_of_isLinThreeFour hKstar_lin
  have hKstar_qs : CFSG.Open.IsQuasisimple Kstar := by
    refine ⟨hKstar_perf.commutator_eq_top, ?_⟩
    haveI : IsSimpleGroup Kstar := hKstar_simple
    let e : Kstar ⧸ Subgroup.center Kstar ≃* Kstar :=
      (QuotientGroup.quotientMulEquivOfEq hKstar_center).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup
  have hKstar_native_qs : CFSG.IsQuasisimple Kstar :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff Kstar).2.2.1.mpr hKstar_qs
  have hKstar_comp_native : CFSG.IsComponent Kstar :=
    ⟨hKstar_native_qs, hKstar_normal.isSubnormal⟩
  have hKstar_comp : CFSG.Open.IsComponentOf Kstar ⊤ :=
    (CFSG.isComponent_iff_open Kstar).mp hKstar_comp_native
  have hKstar_card : Nat.card Kstar = 20160 := by
    calc Nat.card Kstar = Nat.card (K ⧸ CFSG.pCore 2 K) :=
          (Nat.card_congr eK.toEquiv).symm
      _ = Nat.card (CFSG.PGLModel.projSL 3 (GaloisField 2 2)) := Nat.card_congr eCat.toEquiv
      _ = 20160 := CFSG.PGLModel.card_projSL_three_four
  have hKstar_ne_bot : Kstar ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hKstar_card
    omega
  have hKstar_centralizer : Subgroup.centralizer (Kstar : Set (X ⧸ C)) = ⊥ := by
    set Y : Subgroup X := (Subgroup.centralizer (Kstar : Set (X ⧸ C))).comap π with hY
    have hYnormal : Y.Normal := by
      rw [hY]
      infer_instance
    have hcomm : ⁅Y, K⁆ ≤ O := by
      have hmap : ⁅Y, K⁆.map π = ⁅Y.map π, K.map π⁆ := Subgroup.map_commutator Y K π
      have hYbar : Y.map π ≤ Subgroup.centralizer (Kstar : Set (X ⧸ C)) := by
        rw [hY]
        exact Subgroup.map_comap_le _ _
      have hKbar : K.map π = Kstar := by rw [hKstar_map]
      have hbot : ⁅Y, K⁆.map π = ⊥ := by
        rw [hmap, hKbar]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYbar
      have hle : ⁅Y, K⁆ ≤ π.ker := by
        rw [← Subgroup.map_eq_bot_iff]
        exact hbot
      rw [QuotientGroup.ker_mk'] at hle
      rw [hCeq] at hle
      exact hle
    have hYleO : Y ≤ O :=
      le_pCoreOf_two_of_commutator_le (X := X) (K := K) (S := S) (Y := Y)
        hS hKn hKS hKz hYnormal hcomm
    have hYleC : Y ≤ C := by
      rw [hCeq]
      exact hYleO
    have hmapbot : Y.map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hYleC
    rw [hY] at hmapbot
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C)] at hmapbot
    exact hmapbot
  have hJst_bot : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnImg S
      (CFSG.Quasithin.thompsonJ S) = ⊥ := by
    by_contra hJst
    set Jst : Subgroup (X ⧸ C) :=
      CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnImg S
        (CFSG.Quasithin.thompsonJ S) with hJstdef
    have hcomm_ne : ⁅Kstar, Jst⁆ ≠ ⊥ := by
      intro hcomm
      apply hJst
      rw [hJstdef] at hcomm ⊢
      have hcomm' : ⁅Jst, Kstar⁆ = ⊥ := by
        rwa [Subgroup.commutator_comm]
      have hle : Jst ≤ Subgroup.centralizer (Kstar : Set (X ⧸ C)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm' 
      rw [hKstar_centralizer] at hle
      exact le_bot_iff.mp hle
    have hJst_norm : Jst ≤ Subgroup.normalizer (Kstar : Set (X ⧸ C)) := by
      intro x hx
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top x
    have hJeq : ⁅Kstar, Jst⁆ = Kstar :=
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.commutator_eq_of_ne_bot
        hKstar_native_qs hJst_norm hcomm_ne
    obtain ⟨W, _, _, _, ρ, hρ, A, hAel, hAbest, hAn, hKA⟩ :=
      CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.exists_rep_offender_of_le
        X S hC hOS Kstar hKstar_comp hJeq
    have hfaith : ∀ a : X ⧸ C, (∀ w, ρ a w = w) → a = 1 := fun a ha =>
      hρ (by ext w; simp [ha w])
    have hb : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsBestOffenderOn ρ A ⊤ :=
      (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.isBestOffender_iff_on ρ A
        (fun a _ ha => hfaith a ha)).mp ⟨hAel, hAbest⟩
    have hKnt : ¬ Kstar ≤
        CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.cenOn ρ Kstar ⊤ := by
      intro hle
      apply hKstar_ne_bot
      rw [eq_bot_iff]
      intro k hk
      have hkcen := hle hk
      have hkfix : ∀ w, ρ k w = w := fun w =>
        (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.mem_cenOn.mp hkcen).2 w
          Submodule.mem_top
      have hk1 : k = 1 := hρ (by ext w; simpa using hkfix w)
      simpa using hk1
    obtain ⟨W', _, _, Lb, Eb, hsq, hirr, hLbq, hEbne, hEbel, hEbquad, hEbN, hbound,
      ψ, hψsurj⟩ :=
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.exists_irrSection
        ρ Kstar A hKstar_native_qs hAel hAn hKA hKnt hb
    have hLbne : Lb ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot Lb).mp
        (CFSG.LocalCores.isQuasisimple_nontrivial hLbq)
    have hψinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases hKstar_simple.eq_bot_or_eq_top_of_normal ψ.ker with h | h
      · exact h
      · exfalso
        apply hLbne
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨k, hk⟩ := hψsurj ⟨y, hy⟩
        have hker : ψ k = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top k)
        rw [hk] at hker
        simpa using congrArg Subtype.val hker
    have hψrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hψsurj
    let eψ : Kstar ≃* ↥Lb :=
      (MonoidHom.ofInjective hψinj).trans
        ((MulEquiv.subgroupCongr hψrange).trans (Subgroup.topEquiv))
    have hLb_lin : CFSG.AGLEmbedding.IsLinThreeFour ↥Lb :=
      CFSG.AGLEmbedding.L34FF.isLinThreeFour_of_equiv eψ.symm hKstar_lin
    have hlt := CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.l34Exclusion
      W' hsq Lb Eb hirr hLb_lin hEbN hEbne hEbel hEbquad
    omega
  have hJleC : CFSG.Quasithin.thompsonJ S ≤ C := by
    have hmapbot : (CFSG.Quasithin.thompsonJ S).map π = ⊥ := by
      simpa only [CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.gnImg] using hJst_bot
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmapbot
  rw [hCeq] at hJleC
  exact hJleC


private theorem pCoreOf_two_ne_bot_of_l34
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) {K : Subgroup X}
    (hKn : K.Normal)
    (hKL : Nonempty ((K ⧸ CFSG.pCore 2 K) ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 2))) :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hO
  set O : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) with hOdef
  have hFstar : CFSG.Open.quasithinGenFitting (⊤ : Subgroup X) = O :=
    (CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff (⊤ : Subgroup X) 2).mpr hC
  have hKLlin : CFSG.AGLEmbedding.IsLinThreeFour (K ⧸ CFSG.pCore 2 K) := by
    obtain ⟨e⟩ := hKL
    exact CFSG.AGLEmbedding.L34FF.isLinThreeFour_of_equiv e
      isLinThreeFour_projSL_three_four
  have hKcard : Nat.card (K ⧸ CFSG.pCore 2 K) = 20160 := by
    obtain ⟨e⟩ := hKL
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.PGLModel.card_projSL_three_four
  have hKne : K ≠ ⊥ := by
    intro hbot
    subst hbot
    have hcard1 : Nat.card ((⊥ : Subgroup X) ⧸ CFSG.pCore 2 (⊥ : Subgroup X)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [hcard1] at hKcard
    omega
  have hF1 : K ⊓ O = CFSG.Open.pCoreOf 2 K := pCoreOf_two_inf_eq_pCoreOf_two (X := X) (K := K) hKn
  have hO2Kbot : CFSG.Open.pCoreOf 2 K = ⊥ := by
    rw [← hF1, hO]
    simp
  have hO2Knormal : (CFSG.Open.pCoreOf 2 K).Normal := by
    letI : K.Normal := hKn
    haveI : (CFSG.pCore 2 K).Characteristic := CFSG.pCore_characteristic
    exact ConjAct.normal_of_characteristic_of_normal
  letI : (CFSG.Open.pCoreOf 2 K).Normal := hO2Knormal
  have hO2Kbot_int : CFSG.pCore 2 K = ⊥ :=
    Subgroup.map_injective K.subtype_injective (by
      rw [Subgroup.map_bot]
      exact hO2Kbot)
  have hKlin : CFSG.AGLEmbedding.IsLinThreeFour K := by
    have e : K ⧸ CFSG.pCore 2 K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hO2Kbot_int).trans QuotientGroup.quotientBot
    exact CFSG.AGLEmbedding.L34FF.isLinThreeFour_of_equiv e.symm hKLlin
  have hKsimple : IsSimpleGroup K :=
    CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.isSimpleGroup_of_isLinThreeFour hKlin
  have hKcenter : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.center_eq_bot_of_isLinThreeFour hKlin
  have hKperf : Group.IsPerfect K :=
    CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.isPerfect_of_isLinThreeFour hKlin
  have hKqs : CFSG.Open.IsQuasisimple K := by
    refine ⟨hKperf.commutator_eq_top, ?_⟩
    haveI : IsSimpleGroup K := hKsimple
    let e : K ⧸ Subgroup.center K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hKcenter).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup
  have hKqs_native : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.mpr hKqs
  have hKcomp_native : CFSG.IsComponent K := ⟨hKqs_native, hKn.isSubnormal⟩
  have hKcomp_open : CFSG.Open.IsComponentOf K ⊤ :=
    (CFSG.isComponent_iff_open K).mp hKcomp_native
  have hKleF : K ≤ CFSG.Open.quasithinGenFitting (⊤ : Subgroup X) := by
    have hle : K ≤ sSup {L : Subgroup X | CFSG.Open.IsComponentOf L ⊤} := le_sSup hKcomp_open
    exact hle.trans le_sup_right
  rw [hFstar, hO] at hKleF
  exact hKne (le_bot_iff.mp hKleF)


theorem exists_char_normal_of_l34
    {X : Type} [Group X] [Finite X]
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) {S K : Subgroup X}
    (hS : IsPGroup 2 S) (hOS : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ S) (hKn : K.Normal)
    (hKS : K ⊔ S = ⊤)
    (hKodd : K = Subgroup.closure {x : X | x ∈ K ∧ Odd (orderOf x)})
    (hKL : Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 2))) :
    ∃ D : Subgroup X, D ≠ ⊥ ∧ D ≤ S ∧ (D.subgroupOf S).Characteristic ∧ D.Normal := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKLlin : CFSG.AGLEmbedding.IsLinThreeFour (K ⧸ CFSG.pCore 2 K) := by
    obtain ⟨e⟩ := hKL
    exact CFSG.AGLEmbedding.L34FF.isLinThreeFour_of_equiv e
      isLinThreeFour_projSL_three_four
  have hKz : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.center_eq_bot_of_isLinThreeFour hKLlin
  have hKsimple : IsSimpleGroup (K ⧸ CFSG.pCore 2 K) :=
    CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.isSimpleGroup_of_isLinThreeFour hKLlin
  have hO2ne : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≠ ⊥ :=
    pCoreOf_two_ne_bot_of_l34 hC hKn hKL
  have hSne : S ≠ ⊥ := by
    intro hSbot
    apply hO2ne
    exact le_bot_iff.mp (hSbot ▸ hOS)
  have hZne : CFSG.Quasithin.omegaOneCenterOf S ≠ ⊥ :=
    CFSG.Quasithin.MS93.omegaOneCenterOf_ne_bot hS hSne
  have hZchar : ((CFSG.Quasithin.omegaOneCenterOf S).subgroupOf S).Characteristic :=
    CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf S
  rcases gnC_eq_pCoreOf_or_le_gnC hC hS hOS hKn hKS hKz hKsimple with hKleC | hCeq
  · refine ⟨CFSG.Quasithin.omegaOneCenterOf S, hZne,
      CFSG.Quasithin.A4.omegaOneCenterOf_le S, hZchar, ?_⟩
    exact normal_omegaOneCenterOf_of_le_gnC hKn hKS hKleC
  · have hJleO : CFSG.Quasithin.thompsonJ S ≤
        CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) :=
      thompsonJ_le_pCoreOf_of_l34 hC hS hOS hKn hKS hKz hKL hCeq
    have hJnormal : (CFSG.Quasithin.thompsonJ S).Normal :=
      normal_thompsonJ_of_le_pCoreOf hOS hJleO
    have hJne : CFSG.Quasithin.thompsonJ S ≠ ⊥ :=
      CFSG.Quasithin.H13.VolI.thompsonJ_ne_bot hS hSne
    have hJchar : ((CFSG.Quasithin.thompsonJ S).subgroupOf S).Characteristic :=
      CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S
    exact ⟨CFSG.Quasithin.thompsonJ S, hJne, CFSG.Quasithin.thompsonJ_le_self S,
      hJchar, hJnormal⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
