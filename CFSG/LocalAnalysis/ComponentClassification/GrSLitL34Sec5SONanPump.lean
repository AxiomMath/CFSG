module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanConfig
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SONanGluing
public import CFSG.LocalAnalysis.ComponentClassification.CTUMaxTwoAt
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdOrder
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTarget
public import CFSG.GroupTheory.SylowNormalizedByPGroup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open scoped commutatorElement

theorem le_normalizer_of_onan_pump
    {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G} (hc : ONanWConfig G t P W)
    {v : G} (hv : orderOf v = 2) (htv : t * v = v * t)
    (hvP : ∀ p ∈ P, p⁻¹ * v⁻¹ * p * v ∈ oddIn P) {Q : Subgroup G}
    (hQv : Q ≤ centralizer ({v} : Set G))
    (hQ : IsPComponent 2 (Q.subgroupOf (centralizer ({v} : Set G))))
    (hQn : (Q.subgroupOf (centralizer ({v} : Set G))).Normal)
    (hQON : IsSporadic (↥Q ⧸ Open.fusionZStar ↥Q) .ONan) : Q ≤ normalizer (W : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQperf : Group.IsPerfect ↥Q := by
    have := CatalogueBAlternating.pComponent_perfect hQ
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hQv).toMonoidHom)
      (subgroupOfEquivOfLe hQv).surjective
  have hQON' : IsSporadic (↥Q ⧸ pPrimeCore 2 ↥Q) .ONan :=
    isSporadic_pPrimeCore_of_fusionZStar_on hQperf hQON
  have hCQ : centralizer ({v} : Set G) ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hQv).mp hQn
  obtain ⟨W', hW'odd, hW'N, hW'eq⟩ :=
    exists_wGroup_of_on (G := G) hc.gwTwoBalanced (t := v) (P := Q) hv hQv hCQ hQON'
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
  have hoddP : Odd (Nat.card (oddIn P)) := by
    have hcard : Nat.card (oddIn P) = Nat.card (pPrimeCore 2 ↥P) :=
      Subgroup.card_map_of_injective (K := pPrimeCore 2 ↥P) (f := P.subtype)
        P.subtype_injective
    rw [hcard]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := ↥P) (p := 2))
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
  have hE8 := omSub_sqSub_of_on hc.isSporadic_pPrimeCore hRsyl
  have hEe : IsElemTwo (omSub (sqSub R)) := hE8.1
  have hEcard : Nat.card (omSub (sqSub R)) = 8 := hE8.2
  have hER : omSub (sqSub R) ≤ R := omSub_sqSub_le R
  have hEP : omSub (sqSub R) ≤ P := hER.trans hRP
  have hEt : omSub (sqSub R) ≤ centralizer ({t} : Set G) := hEP.trans hc.le_centralizer
  have hEv : omSub (sqSub R) ≤ centralizer ({v} : Set G) := hER.trans hRcent
  have hW₁ : wGroup (omSub (sqSub R)) = W :=
    hc.wGroup_eq _ hEt hEe (by omega)
  have hW₂ : wGroup (omSub (sqSub R)) = W' :=
    hW'eq _ hEv hEe (by omega)
  have hW'W : W' = W := by rw [← hW₂, hW₁]
  calc Q ≤ normalizer (Q : Set G) := Subgroup.le_normalizer
    _ ≤ normalizer (W' : Set G) := hW'N
    _ = normalizer (W : Set G) := by rw [hW'W]

theorem exists_onan_pump (hS : SchreierFor Blueprint.Catalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple)
    {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G} (hc : ONanWConfig G t P W)
    {v : G} (hv : orderOf v = 2) (htv : t * v = v * t)
    (hvP : ∀ p ∈ P, p⁻¹ * v⁻¹ * p * v ∈ oddIn P) :
    ∃ Q : Subgroup G, Q ≤ centralizer ({v} : Set G) ∧
      IsPComponent 2 (Q.subgroupOf (centralizer ({v} : Set G))) ∧
      (Q.subgroupOf (centralizer ({v} : Set G))).Normal ∧
      UnbalancedGS.gsFixedLayer P v ≤ Q ∧ IsSporadic (↥Q ⧸ Open.fusionZStar ↥Q) .ONan := by
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
  have hQON : IsSporadic (↥Q ⧸ Open.fusionZStar ↥Q) .ONan := by
    obtain ⟨e⟩ := hc.isSporadic
    obtain ⟨f⟩ := hPQ
    exact ⟨f.symm.trans e⟩
  have hQmirror : FooteLit.GSMirrorMaximal Q := by
    intro M hM
    obtain ⟨e⟩ := hc.mirror M (Relation.ReflTransGen.trans hreach hM)
    obtain ⟨f⟩ := hPQ
    exact ⟨f.symm.trans e⟩
  have hQgs : GrSLit.GSWeakMaximalComponent Q :=
    FooteLit.GSMirrorMaximal.gsWeakMaximalComponent hQmirror ⟨v, hv, hQv, hQpc⟩
  have h3 : 3 ≤ pRank 2 ↥Q := three_le_pRank_of_sporadic_onan_fusionZStar hQON
  have hpsp : ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
      Nonempty (↥Q ⧸ Open.fusionZStar ↥Q ≃* Assembly.LowTwoRank.StatedProj
        (Assembly.LowTwoRank.StatedSp 2 K)) :=
    not_psp4_of_onan hQON
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
  exact ⟨Q, hQv, hQpc, hQn, hDQ, hQON⟩

theorem exists_onan_pump_le_normalizer (hS : SchreierFor Blueprint.Catalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple)
    {G : Type} [Group G] [Finite G] {t : G} {P W : Subgroup G} (hc : ONanWConfig G t P W)
    {v : G} (hv : orderOf v = 2) (htv : t * v = v * t)
    (hvP : ∀ p ∈ P, p⁻¹ * v⁻¹ * p * v ∈ oddIn P) :
    ∃ Q : Subgroup G, Q ≤ centralizer ({v} : Set G) ∧
      IsPComponent 2 (Q.subgroupOf (centralizer ({v} : Set G))) ∧
      (Q.subgroupOf (centralizer ({v} : Set G))).Normal ∧
      UnbalancedGS.gsFixedLayer P v ≤ Q ∧ Q ≤ normalizer (W : Set G) ∧
      IsSporadic (↥Q ⧸ Open.fusionZStar ↥Q) .ONan := by
  obtain ⟨Q, hQv, hQ, hQn, hDQ, hQON⟩ := exists_onan_pump hS hCI hGA h13 hc hv htv hvP
  exact ⟨Q, hQv, hQ, hQn, hDQ, le_normalizer_of_onan_pump hc hv htv hvP hQv hQ hQn hQON, hQON⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
