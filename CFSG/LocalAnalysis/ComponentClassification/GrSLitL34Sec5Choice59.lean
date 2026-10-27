module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Center59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Prop41
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5StdEven

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_mem_zStarIn_component
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hStd : GSThmB.L34StandardEvenInput)
    (hUnit : L34UnbalancingUnitaryStep) (hUA : L34UnitaryAutFact) (h41 : L34Prop41)
    {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) (hQ : S ⊓ coreActionKernel L = zpowers t) {u : G}
    (huT : u ∈ T) (huc : ∀ s ∈ T, s * u = u * s) (hu2 : orderOf u = 2) {K₁ : Subgroup G}
    (hT₁ : GSUnbalancingTriple u t K₁) (huK₁ : u ∈ zStarIn K₁)
    (hmax₁ : GSWeakMaximalComponent K₁) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨hbase, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, hlexmax, hSyl, htS, hST, hTsyl⟩ := hset'
  have huS : ∀ s ∈ S, s * u = u * s := fun s hs => huc s (hST hs)
  have htype₁ := isL34Type_of_mem_zStarIn hbase hT₁ huK₁
  have hset₁ :=
    l34Sec4Setting_of_mem_center hMax hbase hT₁ htype₁ hmax₁ hTsyl huT (hST htS) huc
  have hW₁ := h41 G u t K₁ T hset₁ huc fun _ => mem_inf.mpr ⟨huT, huK₁⟩
  obtain ⟨v, -, hfam', hsup⟩ :=
    exists_isL34Family_of_component hS hSol hMax hbase hT₁ htype₁ hmax₁ hset₁.2.2.2.2.1 huc
      (not_isStandardSubgroup_of_mem_zStarIn hU hStd hbase htype₁ hu2 huK₁) hW₁
  have hlex := hlexmax _ v hfam'
  obtain ⟨⟨-, -, -, -, -, hv2, -, -⟩, -, -, -, -⟩ := hfam'
  set L' := pumpUp K₁ v with hL'
  have hK₁L' : K₁ ≤ L' := le_sup_left.trans hsup.le
  have huL' : u ∈ zStarIn L' := mem_zStarIn_of_sup_oddIn hK₁L' hsup huK₁
  have ha' : 1 ≤ twoExp (zStarIn L') := by
    apply le_twoExp_of_dvd
    have h1 := orderOf_dvd_natCard (⟨u, huL'⟩ : zStarIn L')
    rw [Subgroup.orderOf_mk, hu2] at h1
    rwa [pow_one]
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have hZn : ((zStarIn L).subgroupOf L).Normal := by
    have h1 : (zStarIn L).subgroupOf L = Open.fusionZStar L :=
      comap_map_eq_self_of_injective L.subtype_injective _
    rw [h1, Sol78.fusionZStar_eq_comap]
    exact Subgroup.Normal.comap inferInstance _
  have hZsyl : IsSylowTwoIn (S ⊓ L ⊓ zStarIn L) (zStarIn L) :=
    isSylowTwoIn_inf_of_isSubnormal hS₀ (map_subtype_le _) hZn.isSubnormal
  have hZt : S ⊓ L ⊓ zStarIn L ≤ zpowers t := by
    rw [← hQ]
    exact le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans (zStarIn_le_coreActionKernel L))
  have ha : twoExp (zStarIn L) ≤ 1 := by
    have h1 := card_eq_two_pow_twoExp hZsyl
    have h2 : Nat.card ↥(S ⊓ L ⊓ zStarIn L) ≤ 2 :=
      (card_le_of_le hZt).trans (by rw [Nat.card_zpowers, hto])
    by_contra h
    have h3 : 4 ≤ 2 ^ twoExp (zStarIn L) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ twoExp (zStarIn L) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hKN : coreActionKernel L ≤ normalizer (L : Set G) := fun g hg =>
    (mem_coreActionKernel.mp hg).1
  have hQsyl : IsSylowTwoIn (S ⊓ coreActionKernel L) (coreActionKernel L) :=
    isSylowTwoIn_inf_of_isSubnormal hSyl hKN ((normal_subgroupOf_iff_le_normalizer hKN).mpr
      (normalizer_le_normalizer_coreActionKernel L)).isSubnormal
  have hb : twoExp (coreActionKernel L) ≤ 1 := by
    have h1 := card_eq_two_pow_twoExp hQsyl
    rw [hQ, Nat.card_zpowers, hto] at h1
    by_contra h
    have h3 : 4 ≤ 2 ^ twoExp (coreActionKernel L) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ twoExp (coreActionKernel L) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [Prod.Lex.toLex_le_toLex] at hlex
  have hlex' : twoExp (zStarIn L') = twoExp (zStarIn L) ∧
      twoExp (coreActionKernel L') ≤ twoExp (coreActionKernel L) := by
    rcases hlex with h | h
    · exact absurd h (by dsimp only; omega)
    · exact h
  have hb' : twoExp (coreActionKernel L') ≤ 1 := hlex'.2.trans hb
  have haL : 1 ≤ twoExp (zStarIn L) := hlex'.1 ▸ ha'
  have hL'v : L' ≤ centralizer ({v} : Set G) := pumpUp_le_centralizer K₁ v
  have huL'' : u ∈ L' := map_subtype_le _ huL'
  have hu1 : u ≠ 1 := by rintro rfl; simp at hu2
  by_cases huv : u = v
  ·
    subst huv
    have hK₁u := hT₁.2.2.2.1
    have hK₁p := hT₁.2.2.2.2.1
    have hL'K : L' = K₁ := by
      rw [hL', pumpUp, gsFixedLayer_eq_of_le hK₁u hK₁p hK₁u]
      apply le_antisymm
      · exact iSup₂_le fun g hg => (conjugate_eq_self (layerIn_le_normalizer hK₁u hK₁p hg)).le
      · exact le_iSup₂_of_le 1 (one_mem _) (conjugate_one K₁).ge
    rw [hL'K] at hb'
    obtain ⟨hsF, hnF, hoF⟩ := fstar_facts hbase
    have : IsSimpleGroup G := hbase.1
    have h3 := three_le_pRank_of_l34 htype₁
    have hT92 := (hMax G hsF hnF hoF hbase.2.2.1 K₁ hmax₁ (by omega)
      (Sol78.not_psp4_of_l34 htype₁) (Or.inl ⟨htype₁, hbase⟩) u hu2 hK₁u).2 h3
    have hCN₁ := centralizer_le_normalizer_of_isPComponent hT92 hK₁u hK₁p
    have hSN : S ≤ normalizer (K₁ : Set G) := fun s hs =>
      hCN₁ (mem_centralizer_singleton_iff.mpr (huS s hs))
    have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
    obtain ⟨h32, -, -⟩ := hUA G K₁ S t (GSThmB.commutator_eq_self_of_isPComponent hK₁u hK₁p)
      htype₁ (hUnit G u t K₁ hT₁ htype₁) hS2
      (le_inf hSN fun s hs => mem_centralizer_singleton_iff.mpr (hZS s hs))
    have hSK : Nat.card ↥(S ⊓ coreActionKernel K₁) ≤ 2 := by
      have h1 := card_le_two_pow_twoExp (inf_le_right : S ⊓ coreActionKernel K₁ ≤ _)
        (hS2.to_le inf_le_left)
      have h2 : 2 ^ twoExp (coreActionKernel K₁) ≤ 2 := by
        calc 2 ^ twoExp (coreActionKernel K₁) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hb'
          _ = 2 := by norm_num
      omega
    have h128 : 2 ^ 7 ∣ Nat.card L := by
      have h1 := GSThmB.card_of_lieModel_L34 htypeL
      have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.fusionZStar ↥L)
      rw [h1] at h2
      have h4 : 2 ∣ Nat.card (zStarIn L) :=
        Nat.dvd_of_factorization_pos (Nat.one_le_iff_ne_zero.mp haL)
      rw [zStarIn, card_map_of_injective L.subtype_injective] at h4
      obtain ⟨c, hc⟩ := h4
      rw [h2, hc]
      exact ⟨315 * c, by ring⟩
    have h128' := two_pow_le_card_of_isSylowTwoIn hS₀ h128
    have hS₀S : Nat.card ↥(S ⊓ L) ≤ Nat.card S := card_le_of_le inf_le_left
    rw [show (2 : ℕ) ^ 7 = 128 by norm_num] at h128'
    omega
  ·
    have hv2' : v * v = 1 := by rw [← pow_two, ← hv2, pow_orderOf_eq_one]
    have hu2' : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
    have huv' : u * v = v * u := mem_centralizer_singleton_iff.mp (hL'v huL'')
    have hun : u ∉ zpowers v := fun h => by
      rcases eq_one_or_eq_of_mem_zpowers' hv2' h with h | h
      · exact hu1 h
      · exact huv h
    obtain ⟨-, hcard⟩ := elemTwo_zpowers_sup hu2' (isElemTwo_zpowers hv2') (fun y hy => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute u v from huv') i).eq) hun
    have hle : zpowers u ⊔ zpowers v ≤ coreActionKernel L' := sup_le
      (zpowers_le.mpr (zStarIn_le_coreActionKernel L' huL'))
      (zpowers_le.mpr (mem_coreActionKernel_of_commute fun l hl =>
        (mem_centralizer_singleton_iff.mp (hL'v hl)).symm))
    have h4 : 2 ^ 2 ∣ Nat.card (coreActionKernel L') := by
      have h1 := Subgroup.card_dvd_of_le hle
      rw [hcard, Nat.card_zpowers, hv2] at h1
      exact h1
    have := le_twoExp_of_dvd h4
    omega

end CFSG.ComponentClassification.GrSLit.GrS5
