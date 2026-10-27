module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Five
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma551
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem eq_mul_of_card_le_four {H : Subgroup G} (hH : Nat.card H ≤ 4) {t u s : G}
    (ht : t * t = 1) (hu : u * u = 1) (htu : t * u = u * t) (htH : t ∈ H) (huH : u ∈ H)
    (hsH : s ∈ H) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (hut : u ≠ t) (hs1 : s ≠ 1) (hst : s ≠ t)
    (hsu : s ≠ u) : s = u * t := by
  have hun : u ∉ zpowers t := fun h => by
    rcases eq_one_or_eq_of_mem_zpowers' ht h with h | h
    · exact hu1 h
    · exact hut h
  obtain ⟨-, hcard⟩ := elemTwo_zpowers_sup hu (isElemTwo_zpowers ht) (fun y hy => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute u t from htu.symm) i).eq) hun
  have ht2 : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ht) ht1
  have hle : zpowers u ⊔ zpowers t ≤ H := sup_le (zpowers_le.mpr huH) (zpowers_le.mpr htH)
  have heq : zpowers u ⊔ zpowers t = H :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, ht2]; omega)
  have hsK : s ∈ zpowers u ⊔ zpowers t := heq ▸ hsH
  rcases mem_four_of_mem_sup hu ht htu.symm hsK with h | h | h | h
  · exact absurd h hs1
  · exact absurd h hsu
  · exact absurd h hst
  · exact h

theorem exists_unitary_mem
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hUnit : L34UnbalancingUnitaryStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {x : G}
    (hx : GSUnbalancingTriple t x L) : ∃ x₁ ∈ S, IsL34Unitary L x₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨-, htypeL, -⟩, -, hSyl, -, -, -⟩ := hset'
  have hSt : S ≤ centralizer ({t} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hZS s hs)
  have hSC : IsSylowTwoIn S (centralizer ({t} : Set G)) := isSylowTwoIn_of_le_of_le hSyl hSt hCN
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx.2.1, pow_orderOf_eq_one]
  have hxC : x ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hx.2.2.1.symm
  obtain ⟨c, hcC, hcS⟩ :=
    exists_conjugate_le_of_isSylowTwoIn hSC (zpowers_le.mpr hxC) (isElemTwo_zpowers hx2).isPGroup
  exact ⟨c⁻¹ * x * c, hcS (conj_mem_conjugate (mem_zpowers x) c),
    hUnit G t _ L (gsUnbalancingTriple_conj hx hcC (hCN hcC)) htypeL⟩

theorem exists_card_le_four_of_unitary
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hF1 : L34SylowCentralizerFact) (hUCen : L34UnitaryCenterFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    (hQ : S ⊓ coreActionKernel L = zpowers t) {x₁ : G} (hx₁S : x₁ ∈ S)
    (hx₁ : IsL34Unitary L x₁) :
    ∃ H : Subgroup G, H ≤ zpowers t ⊔ S ⊓ L ∧ Nat.card H ≤ 4 ∧ t ∈ H ∧
      ∀ g ∈ S, (∀ s ∈ S, g * s = s * g) → g ∈ H := by
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  set C₀ := S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ centralizer ({x₁} : Set G)
    with hC₀
  have hZt : S ⊓ L ⊓ zStarIn L ≤ zpowers t := by
    rw [← hQ]
    exact le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans (zStarIn_le_coreActionKernel L))
  have hZ2 : ∀ z ∈ S ⊓ L ⊓ zStarIn L, z * z = 1 := fun z hz =>
    mul_self_eq_one_of_mem_zpowers ht2 (hZt hz)
  have hx₁N : x₁ ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    have h1 := mem_normalizer_iff.mp (le_normalizer hx₁S) h
    have h2 := mem_normalizer_iff.mp hx₁.1 h
    simp only [mem_inf] at h1 h2 ⊢
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩
  obtain ⟨hcard, -⟩ := hUCen G L (S ⊓ L) x₁ hperf htypeL hx₁ hS₀ hx₁N hZ2
  have htcomm : ∀ q ∈ zpowers t, ∀ s ∈ S, q * s = s * q := by
    intro q hq s hs
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hq
    exact (Commute.zpow_left (show Commute t s from (hZS s hs).symm) i).eq
  have hcen : ∀ g ∈ S, (∀ s ∈ S, g * s = s * g) → g ∈ zpowers t ⊔ C₀ := by
    intro g hgS hg
    obtain ⟨k, hk, hkK, -⟩ := hF1 G L (S ⊓ L) g hperf htypeL hS₀ (hSyl.1 hgS)
      fun p hp => hg p (mem_inf.mp hp).1
    have hkS : k ∈ S := (mem_inf.mp hk).1
    have hq : k⁻¹ * g ∈ zpowers t := by
      rw [← hQ]
      exact mem_inf.mpr ⟨mul_mem (inv_mem hkS) hgS, hkK⟩
    have hkc : ∀ s ∈ S, k * s = s * k := by
      intro s hs
      have hq' := htcomm _ (inv_mem hq) s hs
      calc k * s = g * ((k⁻¹ * g)⁻¹ * s) := by group
        _ = g * (s * (k⁻¹ * g)⁻¹) := by rw [hq']
        _ = (g * s) * (k⁻¹ * g)⁻¹ := by group
        _ = (s * g) * (k⁻¹ * g)⁻¹ := by rw [hg s hs]
        _ = s * k := by group
    have hkC₀ : k ∈ C₀ := mem_inf.mpr ⟨mem_inf.mpr ⟨hk, mem_centralizer_iff.mpr fun h hh =>
      (hkc h (mem_inf.mp hh).1).symm⟩, mem_centralizer_singleton_iff.mpr (hkc x₁ hx₁S)⟩
    rw [show g = k * (k⁻¹ * g) by group]
    exact mul_mem (mem_sup_right hkC₀) (mem_sup_left hq)
  have hC₀S : C₀ ≤ S ⊓ L := inf_le_left.trans inf_le_left
  refine ⟨zpowers t ⊔ C₀, sup_le_sup_left hC₀S _, ?_, mem_sup_left (mem_zpowers t), hcen⟩
  have hZcard : Nat.card ↥(S ⊓ L ⊓ zStarIn L) ≤ 2 := by
    calc Nat.card ↥(S ⊓ L ⊓ zStarIn L) ≤ Nat.card (zpowers t) := card_le_of_le hZt
      _ = 2 := by rw [Nat.card_zpowers, hto]
  by_cases htC : t ∈ C₀
  · rw [sup_eq_right.mpr (zpowers_le.mpr htC), hcard]
    omega
  · have htL : t ∉ L := fun htL => htC (mem_inf.mpr ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨htS, htL⟩,
      mem_centralizer_iff.mpr fun h hh => hZS h (mem_inf.mp hh).1⟩,
      mem_centralizer_singleton_iff.mpr (hZS x₁ hx₁S).symm⟩)
    have hZ1 : Nat.card ↥(S ⊓ L ⊓ zStarIn L) = 1 := by
      rw [Subgroup.card_eq_one, eq_bot_iff]
      intro z hz
      rcases eq_one_or_eq_of_mem_zpowers' ht2 (hZt hz) with h | h
      · exact mem_bot.mpr h
      · exact absurd (h ▸ (mem_inf.mp (mem_inf.mp hz).1).2) htL
    have htn : t ∈ normalizer (C₀ : Set G) :=
      mem_normalizer_of_commute fun y hy => (hZS y (hC₀S hy).1).symm
    calc Nat.card ↥(zpowers t ⊔ C₀) ≤ 2 * Nat.card C₀ := card_zpowers_sup_le ht2 htn
      _ = 4 := by rw [hcard, hZ1]

theorem isL34Type_of_mem_zStarIn (hbase : L34BaseSetting G) {u t : G} {K : Subgroup G}
    (hT : GSUnbalancingTriple u t K) (hu : u ∈ zStarIn K) :
    IsL34Type (K ⧸ Open.fusionZStar K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsQuasisimple (K ⧸ pPrimeCore 2 K) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K _ hT.2.2.2.1).mp hT.2.2.2.2.1).2.2
  rcases hbase.2.2.2.2.2.2.2 u t K hT with h | h | h
  · exact absurd hu (not_mem_zStarIn_of_lieModel_psl_two h hq hT.1)
  · exact absurd hu (not_mem_zStarIn_of_lieModel_psl_two h hq hT.1)
  · exact h

end CFSG.ComponentClassification.GrSLit.GrS5
