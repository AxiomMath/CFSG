module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Rank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Notation54
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitWeakMaximal

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem inf_oddIn_le_oddIn {M C : Subgroup G} (hMC : M ≤ C) : oddIn C ⊓ M ≤ oddIn M := by
  set N : Subgroup ↥M := (oddIn C ⊓ M).subgroupOf M with hN
  have hNn : N.Normal := by
    constructor
    intro x hx m
    rw [hN, mem_subgroupOf] at hx ⊢
    obtain ⟨hxC, hxM⟩ := mem_inf.mp hx
    have hmC : ((m : M) : G) ∈ normalizer (oddIn C : Set G) :=
      normalizer_le_normalizer_oddIn C (le_normalizer (hMC m.2))
    refine mem_inf.mpr ⟨?_, ?_⟩
    · simpa using (mem_normalizer_iff.mp hmC _).mp hxC
    · simpa using mul_mem (mul_mem m.2 hxM) (inv_mem m.2)
  have hcop : Nat.Coprime 2 (Nat.card N) := by
    have hodd : Odd (Nat.card (oddIn C)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have h1 : Nat.card N ∣ Nat.card (oddIn C) := by
      rw [hN, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : oddIn C ⊓ M ≤ M)).toEquiv]
      exact card_dvd_of_le inf_le_left
    exact Nat.coprime_two_left.mpr (hodd.of_dvd_nat h1)
  have hle : N ≤ pPrimeCore 2 ↥M := le_sSup ⟨hNn, hcop⟩
  intro x hx
  exact ⟨⟨x, (mem_inf.mp hx).2⟩, hle (show (⟨x, (mem_inf.mp hx).2⟩ : M) ∈ N from hx), rfl⟩

theorem inf_oddIn_centralizer_le_oddIn {L T : Subgroup G} {z : G} (hTL : T ≤ L)
    (hTz : T ≤ centralizer ({z} : Set G))
    (hTset : (T : Set G) * (oddIn L : Set G) = L) :
    L ⊓ oddIn (centralizer ({z} : Set G)) ≤ oddIn L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hC
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set N : Subgroup ↥L := (L ⊓ oddIn C).subgroupOf L with hN
  have hdec : ∀ l : ↥L, ∃ y ∈ T, ∃ hyL : y ∈ L, π l = π ⟨y, hyL⟩ := by
    intro l
    have hl : (l : G) ∈ (T : Set G) * (oddIn L : Set G) := by rw [hTset]; exact l.2
    obtain ⟨y, hy, o, ho, hyo⟩ := hl
    refine ⟨y, hy, hTL hy, ?_⟩
    obtain ⟨o', ho', rfl⟩ := ho
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hyo' : y * (o' : G) = l := hyo
    have e : l⁻¹ * (⟨y, hTL hy⟩ : ↥L) = o'⁻¹ := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv]
      rw [← hyo']
      group
    rw [e]
    exact inv_mem ho'
  have hNn : (N.map π).Normal := by
    constructor
    rintro _ ⟨n, hn, rfl⟩ g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) g
    obtain ⟨y, hy, hyL, hly⟩ := hdec l
    rw [show (QuotientGroup.mk' (pPrimeCore 2 ↥L)) l = π l from rfl, hly, ← map_mul, ← map_inv,
      ← map_mul]
    refine ⟨⟨y, hyL⟩ * n * ⟨y, hyL⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe] at hn
    rw [SetLike.mem_coe, hN, mem_subgroupOf] at *
    obtain ⟨-, hnC⟩ := mem_inf.mp hn
    have hyC : y ∈ normalizer (oddIn C : Set G) :=
      normalizer_le_normalizer_oddIn C (le_normalizer (hTz hy))
    refine mem_inf.mpr ⟨(⟨y, hyL⟩ * n * ⟨y, hyL⟩⁻¹ : ↥L).2, ?_⟩
    simpa using (mem_normalizer_iff.mp hyC _).mp hnC
  have hodd : Nat.Coprime 2 (Nat.card (N.map π)) := by
    have hoddC : Odd (Nat.card (oddIn C)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have h1 : Nat.card N ∣ Nat.card (oddIn C) := by
      rw [hN, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : L ⊓ oddIn C ≤ L)).toEquiv]
      exact card_dvd_of_le inf_le_right
    exact Nat.coprime_two_left.mpr ((hoddC.of_dvd_nat h1).of_dvd_nat (card_map_dvd N π))
  have hbot : N.map π = ⊥ := by
    have h1 : N.map π ≤ pPrimeCore 2 (↥L ⧸ pPrimeCore 2 ↥L) := le_sSup ⟨hNn, hodd⟩
    rwa [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot, le_bot_iff] at h1
  intro x hx
  have hxL : x ∈ L := (mem_inf.mp hx).1
  have h1 : π ⟨x, hxL⟩ ∈ N.map π := ⟨⟨x, hxL⟩, hx, rfl⟩
  rw [hbot, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨x, hxL⟩, h1, rfl⟩

theorem gsFixedLayer_facts (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {L : Subgroup G} {t z : G}
    (ht : orderOf t = 2) (hz : orderOf z = 2) (htz : t * z = z * t) (hzZ : z ∉ center G)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (hzK : z ∈ coreActionKernel L) :
    gsFixedLayer L z ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ∧
      IsPComponent 2 ((gsFixedLayer L z).subgroupOf
        (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G))) ∧
      gsFixedLayer L z ≤ layerIn (centralizer ({z} : Set G)) ∧
      (gsFixedLayer L z : Set G) * (oddIn L : Set G) = L ∧
      oddIn (gsFixedLayer L z) = gsFixedLayer L z ⊓ oddIn L ∧
      Nonempty (gsFixedLayer L z ⧸ pPrimeCore 2 (gsFixedLayer L z) ≃* L ⧸ pPrimeCore 2 L) := by
  have hLtt : conjugate L t = L := UnbalancedCorr.conjugate_eq_self_of_le_centralizer hLt
  have hKe : ∀ k ∈ L ⊔ conjugate L t, k⁻¹ * z⁻¹ * k * z ∈
      (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype := by
    rw [hLtt, sup_idem]
    intro k hk
    exact GSLit.map_pPrimeCore_le_of_isPComponent hLt hL ((mem_coreActionKernel.mp hzK).2 k hk)
  obtain ⟨-, -, -, -, hTbe, hTpc, hTV, hVE, hTset, hO, φ, -⟩ :=
    UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK (a := t)
      (b := t) (e := z) ht hz rfl htz hzZ hLt hL hKe
  exact ⟨hTbe, hTpc, hTV.trans hVE, hTset, hO, ⟨φ⟩⟩

omit [Finite G] in
theorem gsFixedLayer_sup_oddIn {L : Subgroup G} {z : G}
    (hTset : (gsFixedLayer L z : Set G) * (oddIn L : Set G) = L) :
    gsFixedLayer L z ≤ L ∧ gsFixedLayer L z ⊔ oddIn L = L := by
  have hTL : gsFixedLayer L z ≤ L := (gsFixedLayer_le_inf L z).trans inf_le_left
  refine ⟨hTL, le_antisymm (sup_le hTL (map_subtype_le _)) fun l hl => ?_⟩
  have hl' : l ∈ (gsFixedLayer L z : Set G) * (oddIn L : Set G) := by rw [hTset]; exact hl
  obtain ⟨y, hy, o, ho, rfl⟩ := hl'
  exact mul_mem (mem_sup_left hy) (mem_sup_right ho)

theorem mem_coreActionKernel_of_fixedLayer {L T : Subgroup G} {z c : G} (hTL : T ≤ L)
    (hTz : T ≤ centralizer ({z} : Set G)) (hTset : (T : Set G) * (oddIn L : Set G) = L)
    (hcN : c ∈ normalizer (L : Set G))
    (hc : ∀ y ∈ T, c * y * c⁻¹ * y⁻¹ ∈ oddIn (centralizer ({z} : Set G))) :
    c ∈ coreActionKernel L := by
  have hLO := inf_oddIn_centralizer_le_oddIn hTL hTz hTset
  have hON : c ∈ normalizer (oddIn L : Set G) := normalizer_le_normalizer_oddIn L hcN
  have hcy : ∀ y ∈ T, c * y * c⁻¹ * y⁻¹ ∈ oddIn L := by
    intro y hy
    refine hLO (mem_inf.mpr ⟨?_, hc y hy⟩)
    have h1 : c * y * c⁻¹ ∈ L := (mem_normalizer_iff.mp hcN y).mp (hTL hy)
    exact mul_mem h1 (inv_mem (hTL hy))
  have hcj : ∀ j ∈ L, c * j * c⁻¹ * j⁻¹ ∈ oddIn L := by
    intro j hj
    have hj' : j ∈ (T : Set G) * (oddIn L : Set G) := by rw [hTset]; exact hj
    obtain ⟨y, hy, o, ho, rfl⟩ := hj'
    have hoL : o ∈ L := map_subtype_le _ ho
    have hco : c * o * c⁻¹ ∈ oddIn L := (mem_normalizer_iff.mp hON o).mp ho
    have hyN : y ∈ normalizer (oddIn L : Set G) :=
      normalizer_le_normalizer_oddIn L (le_normalizer (hTL hy))
    have e : c * (y * o) * c⁻¹ * (y * o)⁻¹ =
        (c * y * c⁻¹ * y⁻¹) * (y * ((c * o * c⁻¹) * o⁻¹) * y⁻¹) := by group
    rw [e]
    refine mul_mem (hcy y hy) ((mem_normalizer_iff.mp hyN _).mp (mul_mem hco (inv_mem ho)))
  refine mem_coreActionKernel.mpr ⟨hcN, fun j hj => ?_⟩
  have h1 := hcj j⁻¹ (inv_mem hj)
  have h2 := (mem_normalizer_iff.mp (inv_mem hON) _).mp h1
  rwa [show c⁻¹ * (c * j⁻¹ * c⁻¹ * j⁻¹⁻¹) * c⁻¹⁻¹ = j⁻¹ * c⁻¹ * j * c by group] at h2

theorem fstar_facts (hbase : L34BaseSetting G) :
    IsSimpleGroup (GeneralizedFitting.subgroup G) ∧
      (∃ u v : GeneralizedFitting.subgroup G, u * v ≠ v * u) ∧
      ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) := by
  obtain ⟨hsimple, hnab, -, -, hUo, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have htop : GeneralizedFitting.subgroup G = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup G ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  refine ⟨eF.isSimpleGroup, ?_, fun h => hUo (Or.inl h)⟩
  obtain ⟨u, v, huv⟩ := hnab
  exact ⟨eF.symm u, eF.symm v, fun h => huv (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩

theorem commutator_le_inf_oddIn {C M M' : Subgroup G} (hMC : M ≤ C) (hM'C : M' ≤ C)
    (hM : IsPComponent 2 (M.subgroupOf C)) (hM' : IsPComponent 2 (M'.subgroupOf C))
    (hne : M ≠ M') : ⁅M, M'⁆ ≤ oddIn M ⊓ oddIn M' := by
  obtain ⟨h1, hN'⟩ := commutator_le_of_ne hMC hM'C hM hM' hne
  obtain ⟨-, hN⟩ := commutator_le_of_ne hM'C hMC hM' hM (Ne.symm hne)
  have hle1 : ⁅M, M'⁆ ≤ M := commutator_le_of_le_normalizer hN'
  have hle2 : ⁅M, M'⁆ ≤ M' := by
    rw [commutator_comm]
    exact commutator_le_of_le_normalizer hN
  exact le_inf ((le_inf h1 hle1).trans (inf_oddIn_le_oddIn hMC))
    ((le_inf h1 hle2).trans (inf_oddIn_le_oddIn hM'C))

theorem conjugate_eq_of_fixedLayer
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) {z : G} (hz : orderOf z = 2) (htz : t * z = z * t)
    (hzK : z ∈ coreActionKernel L) {M : Subgroup G} (hMz : M ≤ centralizer ({z} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({z} : Set G))))
    (hTK : gsFixedLayer L z ≤ (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set G))
    (hTpc : IsPComponent 2 ((gsFixedLayer L z).subgroupOf
      ((M ⊔ conjugate M t) ⊓ centralizer ({t} : Set G)))) :
    conjugate M t = M := by
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  obtain ⟨hbase, hfam, -, -, -, -, -⟩ := hset
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts hbase
  have : IsSimpleGroup G := hbase.1
  obtain ⟨-, -, hK, -, -, -, -, -⟩ := id hbase
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, htype, hmax, -, -⟩ := hfam
  by_contra hne
  have hne' : M ≠ conjugate M t := fun h => hne h.symm
  obtain ⟨-, hmoved, -⟩ := UGSChain.orbit_fixed_component_comparison hto htz hMz hM hTK hTpc
  have hfix := hmoved hne'
  have hC : GSCorr t L z M := ⟨hto, hz, htz, hLt, hLpt, hMz, hM,
    (mem_coreActionKernel.mp hzK).1, (mem_coreActionKernel.mp hzK).2, hfix.symm⟩
  have hR : GSReach L M := GSReach.of_gsCorr hC
  have hmaxM : GSWeakMaximalComponent M := hmax.of_weakReach (GSWeakReach.of_gsReach hR)
  obtain ⟨e⟩ := hmax.gsMaximalComponent.2 M hR
  have htypeM : IsL34Type (M ⧸ Open.fusionZStar M) :=
    LieType.CurtisTits.lieModel_of_mulEquiv e htype
  have h3 := three_le_pRank_of_l34 htypeM
  obtain ⟨-, h2⟩ := hMax G hsF hnF hoF hK M hmaxM (by omega) (Sol78.not_psp4_of_l34 htypeM)
    (Or.inl ⟨htypeM, hbase⟩) z hz hMz
  apply h2 h3 t
  obtain ⟨hMtz, hMt⟩ := UGSChain.conjugate_isPComponent_centralizer htz hMz hM
  exact commutator_le_inf_oddIn hMz hMtz hM hMt hne'

end CFSG.ComponentClassification.GrSLit.GrS5
