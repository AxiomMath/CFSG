module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWConfig
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzSylowFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTarget
public import CFSG.GroupTheory.SylowNormalizedByPGroup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Tools46

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

theorem le_normalizer_of_suz_pump
    (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts)
    {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G}
    (hc : L34WConfigAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P W)
    {v : G} (hv : orderOf v = 2) (htv : t * v = v * t)
    (hvP : ∀ p ∈ P, p⁻¹ * v⁻¹ * p * v ∈ oddIn P) {Q : Subgroup G}
    (hQv : Q ≤ centralizer ({v} : Set G))
    (hQ : IsPComponent 2 (Q.subgroupOf (centralizer ({v} : Set G))))
    (hQn : (Q.subgroupOf (centralizer ({v} : Set G))).Normal)
    (hQty : IsSporadic (↥Q ⧸ Open.fusionZStar ↥Q) .Suz) : Q ≤ normalizer (W : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCQ : centralizer ({v} : Set G) ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hQv).mp hQn
  obtain ⟨W', -, hW'N, hW'eq, -⟩ :=
    exists_wGroup_glue_of_sylowData hc.gwTwoBalanced hv hQv hCQ
      (GrS4.le_normalizer_oddIn_self Q) (odd_card_oddIn Q)
      (suzSylowData_of_isPComponent hF1 hF2 hv hQv hQ hQty)
  have hv2 : v * v = 1 := by
    rw [← pow_two, ← hv]
    exact pow_orderOf_eq_one v
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  have hvC : v ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.mpr htv.symm
  have hvN : v ∈ normalizer (P : Set G) := hc.centralizer_le_normalizer hvC
  obtain ⟨R, ⟨hRP, hR2, hRodd⟩, hzvR, -⟩ :=
    CFSG.GroupTheory.exists_isSylowIn_normalized_of_isPGroup (p := 2) (K := P) (Q := zpowers v)
      (isElemTwo_zpowers hv2).isPGroup (zpowers_le.mpr hvN)
  have hvR : v ∈ normalizer (R : Set G) := hzvR (mem_zpowers v)
  have hRsub : IsPGroup 2 (R.subgroupOf P) :=
    hR2.of_equiv (subgroupOfEquivOfLe hRP).symm
  have hRodd' : ¬ 2 ∣ (R.subgroupOf P).index := by
    rwa [show (R.subgroupOf P).index = R.relIndex P from rfl]
  have hRsyl : IsSylowTwoIn R P :=
    ⟨hRP, hRsub.toSylow hRodd', IsPGroup.toSylow_coe hRsub hRodd'⟩
  have hoddP : Odd (Nat.card (oddIn P)) := odd_card_oddIn P
  have hbot : R ⊓ oddIn P = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
    rw [hn]
    exact (hoddP.coprime_two_left).pow_left n
  have hRcent : R ≤ centralizer ({v} : Set G) := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    have hvrv : v⁻¹ * r * v ∈ R := by
      have h1 : v * r * v⁻¹ ∈ R := (mem_normalizer_iff.mp hvR r).mp hr
      simpa [hvinv] using h1
    have hc_mem : r⁻¹ * v⁻¹ * r * v ∈ R := by
      have h2 : r⁻¹ * (v⁻¹ * r * v) ∈ R := R.mul_mem (R.inv_mem hr) hvrv
      simpa [mul_assoc] using h2
    have hc_odd : r⁻¹ * v⁻¹ * r * v ∈ oddIn P := hvP r (hRP hr)
    have hc1 : r⁻¹ * v⁻¹ * r * v = 1 := by
      have h3 : r⁻¹ * v⁻¹ * r * v ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact ⟨hc_mem, hc_odd⟩
      exact mem_bot.mp h3
    have hcomm : r * v = v * r := by
      have h : r * (r⁻¹ * v⁻¹ * r * v) * v = v * r := by
        calc r * (r⁻¹ * v⁻¹ * r * v) * v = v⁻¹ * r * (v * v) := by group
          _ = v⁻¹ * r := by rw [hv2, mul_one]
          _ = v * r := by rw [hvinv]
      rwa [hc1, mul_one] at h
    exact hcomm
  have hdata : SuzSylowData P t :=
    suzSylowData_of_facts hF1 hF2
      ⟨hc.base, hc.order_two, hc.le_centralizer, hc.isPComponent, hc.normal, hc.mirror,
        hc.type⟩
  obtain ⟨hEe, hE16⟩ := hdata.elem R hRsyl
  have hER : zGammaThree R ≤ R := zGammaThree_le R
  have hEP : zGammaThree R ≤ P := hER.trans hRP
  have hEt : zGammaThree R ≤ centralizer ({t} : Set G) := hEP.trans hc.le_centralizer
  have hEv : zGammaThree R ≤ centralizer ({v} : Set G) := hER.trans hRcent
  have hW₁ : wGroup (zGammaThree R) = W :=
    hc.wGroup_eq _ hEt hEe (by omega)
  have hW₂ : wGroup (zGammaThree R) = W' :=
    hW'eq _ hEv hEe.isElemAbelian (by omega)
  have hW'W : W' = W := by rw [← hW₂, hW₁]
  calc Q ≤ normalizer (Q : Set G) := Subgroup.le_normalizer
    _ ≤ normalizer (W' : Set G) := hW'N
    _ = normalizer (W : Set G) := by rw [hW'W]

theorem exists_suz_pump (hS : SchreierFor Blueprint.Catalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple)
    {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G}
    (hc : L34WConfigAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P W)
    {v : G} (hv : orderOf v = 2) (htv : t * v = v * t)
    (hvP : ∀ p ∈ P, p⁻¹ * v⁻¹ * p * v ∈ oddIn P) :
    ∃ Q : Subgroup G, Q ≤ centralizer ({v} : Set G) ∧
      IsPComponent 2 (Q.subgroupOf (centralizer ({v} : Set G))) ∧
      (Q.subgroupOf (centralizer ({v} : Set G))).Normal ∧
      UnbalancedGS.gsFixedLayer P v ≤ Q ∧
      IsSporadic (↥Q ⧸ Open.fusionZStar ↥Q) .Suz := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbase := hc.base
  have hsimple : IsSimpleGroup G := hbase.1
  have : IsSimpleGroup G := hsimple
  have hv1 : v ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hv
    omega
  have hvZ : v ∉ center G := by
    rw [CatLeaf.center_eq_bot_of_simple hbase.2.1]
    simp only [mem_bot]
    exact hv1
  have hvC : v ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.mpr htv.symm
  have hvN : v ∈ normalizer (P : Set G) := hc.centralizer_le_normalizer hvC
  obtain ⟨Q, hQv, hQpc, hTQ, hTpc, hidx, hcorr, hiso⟩ :=
    FooteLit.kProper_orbit_target_production_of_schreier hS hbase.2.2.1
      (a := t) hc.order_two (J := P) hc.le_centralizer hc.isPComponent
      (b := v) hv hvZ htv hvN (by simpa [oddIn] using hvP)
  have hcorrW : GrSLit.GSWeakCorr t P v Q :=
    ⟨hc.order_two, hv, htv, hc.le_centralizer, hc.isPComponent, hQv, hQpc, hvN,
      (by simpa [oddIn] using hvP), hTQ⟩
  have hreach : FooteLit.GSMirrorReach P Q :=
    FooteLit.GSMirrorReach.tail_corr (FooteLit.GSMirrorReach.refl P) hcorrW
  have hPQ : Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* ↥Q ⧸ Open.fusionZStar ↥Q) :=
    hc.mirror Q hreach
  have hQty : IsSporadic (↥Q ⧸ Open.fusionZStar ↥Q) .Suz := by
    obtain ⟨e⟩ := hc.type
    obtain ⟨f⟩ := hPQ
    exact ⟨f.symm.trans e⟩
  have hQmirror : FooteLit.GSMirrorMaximal Q := by
    intro M hM
    obtain ⟨e⟩ := hc.mirror M (Relation.ReflTransGen.trans hreach hM)
    obtain ⟨f⟩ := hPQ
    exact ⟨f.symm.trans e⟩
  have hQgs : GrSLit.GSWeakMaximalComponent Q :=
    FooteLit.GSMirrorMaximal.gsWeakMaximalComponent hQmirror ⟨v, hv, hQv, hQpc⟩
  have h3 : 3 ≤ pRank 2 ↥Q := three_le_pRank_of_sporadic_suz_fusionZStar hQty
  have hpsp : ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
      Nonempty (↥Q ⧸ Open.fusionZStar ↥Q ≃* Assembly.LowTwoRank.StatedProj
        (Assembly.LowTwoRank.StatedSp 2 K)) :=
    not_psp4_of_suz hQty
  obtain ⟨hsF, hnF, hoF⟩ := GrS5.fstar_facts hc.base
  have hT92 : ∀ g : G, ¬ ⁅Q, conjugate Q g⁆ ≤ oddIn Q ⊓ oddIn (conjugate Q g) :=
    (Sol76.maximalTwoComponentSimple_at_of_gsMirrorMaximal hCI hGA hsF hnF hoF h13
      hbase.2.2.1 hQgs (by omega) hpsp hQmirror hv hQv).2 h3
  have hQnorm : centralizer ({v} : Set G) ≤ normalizer (Q : Set G) :=
    GrS5.centralizer_le_normalizer_of_isPComponent hT92 hQv hQpc
  have hQn : (Q.subgroupOf (centralizer ({v} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQv).mpr hQnorm
  have htC : t ∈ centralizer ({v} : Set G) :=
    mem_centralizer_singleton_iff.mpr htv
  have htN : t ∈ normalizer (Q : Set G) := hQnorm htC
  have hconjQt : conjugate Q t = Q :=
    mem_normalizer_iff_map_conj_eq.mp (inv_mem htN)
  have hDQ : UnbalancedGS.gsFixedLayer P v ≤ Q := by
    have h := hTQ
    rw [hconjQt, sup_idem] at h
    exact h
  exact ⟨Q, hQv, hQpc, hQn, hDQ, hQty⟩

theorem exists_suz_pump_le_normalizer (hS : SchreierFor Blueprint.Catalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple) (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts)
    {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G}
    (hc : L34WConfigAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P W)
    {v : G} (hv : orderOf v = 2) (htv : t * v = v * t)
    (hvP : ∀ p ∈ P, p⁻¹ * v⁻¹ * p * v ∈ oddIn P) :
    ∃ Q : Subgroup G, Q ≤ centralizer ({v} : Set G) ∧
      IsPComponent 2 (Q.subgroupOf (centralizer ({v} : Set G))) ∧
      (Q.subgroupOf (centralizer ({v} : Set G))).Normal ∧
      UnbalancedGS.gsFixedLayer P v ≤ Q ∧ Q ≤ normalizer (W : Set G) ∧
      IsSporadic (↥Q ⧸ Open.fusionZStar ↥Q) .Suz := by
  obtain ⟨Q, hQv, hQ, hQn, hDQ, hQty⟩ := exists_suz_pump hS hCI hGA h13 hc hv htv hvP
  exact ⟨Q, hQv, hQ, hQn, hDQ,
    le_normalizer_of_suz_pump hF1 hF2 hc hv htv hvP hQv hQ hQn hQty, hQty⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
