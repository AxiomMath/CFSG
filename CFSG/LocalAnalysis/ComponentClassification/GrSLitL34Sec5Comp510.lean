module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools582

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem exists_elemTwo_sixtyFour (h59 : L34Lemma59) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) :
    ∃ E : Subgroup G, E ≤ S ⊓ L ⊔ omegaOne (S ⊓ coreActionKernel L) ∧ IsElemTwo E ∧
      Nat.card E = 64 := by
  obtain ⟨z, -, -, hΩ, h6, -⟩ := h59 G L t S T hset
  obtain ⟨E, hE, hEl, hEc⟩ := exists_isElemTwo_card_eq_pRank (S ⊓ L ⊔ zpowers t ⊔ zpowers z)
  refine ⟨E, ?_, hEl, by rw [hEc, h6]; norm_num⟩
  rw [hΩ, ← sup_assoc]
  exact hE

theorem wGroup_eq_bot_of_le_sup_omegaOne
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (h58 : L34Lemma58) (hElem : L34ElementaryCenterSylowFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    {A : Subgroup G} (hA : IsEightGroup A)
    (hAP : A ≤ S ⊓ L ⊔ omegaOne (S ⊓ coreActionKernel L)) : wGroup A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨hbase, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -, -, hW8⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have htKL : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have hGWb : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced hSol hbase.2.2.2.2.2.1
  have hZ2 : ∀ y ∈ S ⊓ L ⊓ zStarIn L, y * y = 1 := by
    intro y hy
    obtain ⟨hy1, hyZ⟩ := mem_inf.mp hy
    have hyQL : y ∈ S ⊓ coreActionKernel L ⊓ L := mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hy1).1,
      zStarIn_le_coreActionKernel L hyZ⟩, (mem_inf.mp hy1).2⟩
    by_cases hZ : S ⊓ coreActionKernel L ⊓ L = ⊥
    · rw [hZ, mem_bot] at hyQL
      rw [hyQL, mul_one]
    · exact ((h58 G L t S T hset).2 hZ).2 y hyQL
  obtain ⟨hZel, hZc, -⟩ := hElem G L (S ⊓ L) hperf htypeL hS₀ hZ2
  set Z₀ := S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) with hZ₀
  set P := S ⊓ L ⊔ omegaOne (S ⊓ coreActionKernel L) with hP
  have hPS : P ≤ S := sup_le inf_le_left ((omegaOne_le _).trans inf_le_left)
  have htZ : ∀ y ∈ Z₀, t * y = y * t := fun y hy =>
    (hZS y (mem_inf.mp (mem_inf.mp hy).1).1).symm
  have hFC : zpowers t ⊔ Z₀ ≤ centralizer (P : Set G) := by
    refine sup_le (zpowers_le.mpr (mem_centralizer_iff.mpr fun h hh => hZS h (hPS hh))) ?_
    intro c hc
    have hcS₀ : c ∈ S ⊓ L := (mem_inf.mp hc).1
    have hPc : P ≤ centralizer ({c} : Set G) := by
      refine sup_le (fun h hh => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (mem_inf.mp hc).2 h hh)) fun q hq => ?_
      have hqQ := omegaOne_le _ hq
      exact mem_centralizer_singleton_iff.mpr (commute_of_mem_coreActionKernel hS2
        (mem_inf.mp hqQ).1 (mem_inf.mp hqQ).2 (mem_inf.mp hcS₀).1 (mem_inf.mp hcS₀).2)
    exact mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hPc hh)
  have hF8 : 8 ≤ Nat.card ↥(zpowers t ⊔ Z₀) := by
    by_cases htZ₀ : t ∈ Z₀
    · have htZ1 : t ∈ S ⊓ L ⊓ zStarIn L := mem_inf.mpr ⟨(mem_inf.mp htZ₀).1,
        inf_coreActionKernel_le_zStarIn L (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp htZ₀).1).2,
          htKL⟩)⟩
      have h2 : 2 ≤ Nat.card ↥(S ⊓ L ⊓ zStarIn L) := by
        by_contra h
        push Not at h
        have h1 : Nat.card ↥(S ⊓ L ⊓ zStarIn L) = 1 := by
          have := Nat.card_pos (α := ↥(S ⊓ L ⊓ zStarIn L))
          omega
        rw [Subgroup.card_eq_one] at h1
        rw [h1, mem_bot] at htZ1
        rw [htZ1] at hto
        simp at hto
      calc 8 ≤ Nat.card Z₀ := by rw [hZc]; omega
        _ ≤ Nat.card ↥(zpowers t ⊔ Z₀) := card_le_of_le le_sup_right
    · obtain ⟨-, hc⟩ := elemTwo_zpowers_sup ht2 hZel htZ htZ₀
      rw [hc, hZc]
      have := Nat.card_pos (α := ↥(S ⊓ L ⊓ zStarIn L))
      omega
  have hF2 : IsPGroup 2 ↥(zpowers t ⊔ Z₀) :=
    hS2.to_le (sup_le (zpowers_le.mpr htS) ((inf_le_left.trans inf_le_left)))
  obtain ⟨F, hFle, hFc⟩ := exists_le_card_eight hF2 hF8
  have hFel : IsElemTwo F := by
    refine (IsElemTwo.sup (isElemTwo_zpowers ht2) hZel fun x hx y hy => ?_).mono hFle
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute t y from htZ y hy) i).eq
  have hFL : F ≤ L ⊔ zpowers t := hFle.trans
    (sup_le le_sup_right ((inf_le_left.trans inf_le_right).trans le_sup_left))
  have hWF : wGroup F = ⊥ := hW8 F ⟨hFel, hFc⟩ (Or.inl hFL)
  rw [wGroup_eq_of_commute hGWb (A := A) (A' := F)
    ⟨hA.1.isPGroup, hA.1.1, hA.1.three_le_pRank hA.2.symm.le⟩
    ⟨hFel.isPGroup, hFel.1, hFel.three_le_pRank hFc.symm.le⟩
    fun x hx y hy => mem_centralizer_iff.mp (hFC (hFle hy)) x (hAP hx)]
  exact hWF

theorem oddIn_le_center_of_component
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hElem : L34ElementaryCenterSylowFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu2 : orderOf u = 2) (huc : ∀ s ∈ S, s * u = u * s) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hSN : S ≤ normalizer (K₁ : Set G))
    (hrk : ∀ E : Subgroup G, E ≤ S → IsElemTwo E →
      Nat.card E ≤ 8 * Nat.card ↥(E ⊓ coreActionKernel K₁)) :
    ∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨hbase, -, -, hSyl, -, -, -⟩ := hset'
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  obtain ⟨E, hEP, hEl, hEc⟩ := exists_elemTwo_sixtyFour h59 hset
  have hES : E ≤ S := hEP.trans (sup_le inf_le_left ((omegaOne_le _).trans inf_le_left))
  have h8 : 8 ≤ Nat.card ↥(E ⊓ coreActionKernel K₁) := by
    have := hrk E hES hEl
    omega
  obtain ⟨F, hFle, hFc⟩ := exists_le_card_eight ((hS2.to_le hES).to_le inf_le_left) h8
  have hFel : IsElemTwo F := hEl.mono (hFle.trans inf_le_left)
  have hFS : F ≤ S := (hFle.trans inf_le_left).trans hES
  have hWF := wGroup_eq_bot_of_le_sup_omegaOne hS hU hheld hSol hGW h58 hElem hset ⟨hFel, hFc⟩
    ((hFle.trans inf_le_left).trans hEP)
  have hbal : ∀ e ∈ F, e ≠ 1 →
      ⁅(pPrimeCore 2 K₁).map K₁.subtype ⊓ centralizer ({e} : Set G),
        (pLayer ↥(K₁ ⊓ centralizer ({e} : Set G)) 2).map
          (K₁ ⊓ centralizer ({e} : Set G)).subtype⁆ ≤
      (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype :=
    fun e he he1 => commutator_oddCore_pLayer_le hS hU hheld hK hu2 hK₁u hK₁p
      (huc e (hFS he)).symm
      (centralizer_ne_top_of_not_mem_center (not_mem_center_of_ne_one hnonab he1))
  have hcom := oddCore_le_center_of_wGroup_eq_bot hK₁u hK₁p
    (fun e he => mem_centralizer_singleton_iff.mpr (huc e (hFS he))) hFel.1 hFel.2
    (by rw [hFc]; norm_num) (hFS.trans hSN)
    (fun e he => conj_mem_oddIn_of_mem_coreActionKernel (mem_inf.mp (hFle he)).2)
    hWF hbal (Or.inr (by rw [hFc]))
  exact hcom

end CFSG.ComponentClassification.GrSLit.GrS5
