module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Suzuki510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Cor211
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Central
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma55
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Pump
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools59

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_central_involution_zStarIn {K₁ S : Subgroup G}
    (hSN : S ≤ normalizer (K₁ : Set G)) (hS2 : IsPGroup 2 S)
    (hev : Even (Nat.card ↥(zStarIn K₁))) :
    ∃ S₁ : Subgroup G, IsSylowTwoIn S₁ (normalizer (K₁ : Set G)) ∧ S ≤ S₁ ∧
      ∃ b ∈ S₁ ⊓ zStarIn K₁, orderOf b = 2 ∧ ∀ s ∈ S₁, s * b = b * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₁, hS₁, hSS₁⟩ := L34Central.exists_isSylowTwoIn_le hSN hS2
  refine ⟨S₁, hS₁, hSS₁, ?_⟩
  have hS₁2 : IsPGroup 2 S₁ := IsSylowTwoIn.isPGroup hS₁
  have hZK : zStarIn K₁ ≤ K₁ := map_subtype_le _
  have hZN : zStarIn K₁ ≤ normalizer (K₁ : Set G) := fun x hx => le_normalizer (hZK hx)
  have hNZ : normalizer (K₁ : Set G) ≤ normalizer (zStarIn K₁ : Set G) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic K₁ (Open.fusionZStar K₁)
  have hsub : ((zStarIn K₁).subgroupOf (normalizer (K₁ : Set G))).IsSubnormal :=
    ((normal_subgroupOf_iff_le_normalizer hZN).mpr hNZ).isSubnormal
  have hsyl := isSylowTwoIn_inf_of_isSubnormal hS₁ hZN hsub
  have hne : S₁ ⊓ zStarIn K₁ ≠ ⊥ := by
    intro h
    have h1 := card_eq_two_pow_twoExp hsyl
    rw [h, card_bot] at h1
    have h2 : 1 ≤ twoExp (zStarIn K₁) := le_twoExp_of_dvd (by
      rw [pow_one]
      exact even_iff_two_dvd.mp hev)
    have h3 : 2 ≤ 2 ^ twoExp (zStarIn K₁) :=
      (Nat.pow_le_pow_right (by norm_num) h2).trans_eq' (by norm_num)
    omega
  have hS₁Z : S₁ ≤ normalizer ((S₁ ⊓ zStarIn K₁ : Subgroup G) : Set G) := fun s hs =>
    normalizer_inf_mem (le_normalizer hs) (hNZ (hS₁.1 hs))
  obtain ⟨b, hb, hbo, hbc⟩ := GSLit.exists_involution_mem_center hS₁2 inf_le_left hS₁Z hne
  exact ⟨b, hb, hbo, hbc⟩

theorem twoExp_zStarIn_le_of_sup_oddIn {K P : Subgroup G} (hKP : K ≤ P)
    (hsup : K ⊔ oddIn P = P) : twoExp (zStarIn K) ≤ twoExp (zStarIn P) := by
  apply le_twoExp_of_dvd
  have h1 : Nat.card ↥(zStarIn K) ∣ Nat.card ↥(zStarIn P) :=
    card_dvd_of_le fun x hx => mem_zStarIn_of_sup_oddIn hKP hsup hx
  exact (Nat.ordProj_dvd _ 2).trans h1

theorem mem_normalizer_pumpUp_of_mem_normalizer {J : Subgroup G} {v c : G}
    (hcJ : c ∈ normalizer (J : Set G)) (hcv : c ∈ centralizer ({v} : Set G)) :
    c ∈ normalizer (pumpUp J v : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pLayer ↥(J ⊓ centralizer ({v} : Set G)) 2).Characteristic :=
    CatalogueBPrimeJoin.pLayer_characteristic
  have hcF : c ∈ normalizer (gsFixedLayer J v : Set G) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic (J ⊓ centralizer ({v} : Set G))
      (pLayer ↥(J ⊓ centralizer ({v} : Set G)) 2)
      (normalizer_inf_mem hcJ (le_normalizer hcv))
  exact mem_normalizer_iSup_conjugate_of_normalizer
    (mem_normalizer_map_pLayer (H := centralizer ({v} : Set G)) hcv) hcF

theorem mem_coreActionKernel_pumpUp {K₁ : Subgroup G} {u v c : G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁v : K₁ ≤ centralizer ({v} : Set G)) (hsup : K₁ ⊔ oddIn (pumpUp K₁ v) = pumpUp K₁ v)
    (hcK : c ∈ coreActionKernel K₁) (hcv : c * v = v * c) :
    c ∈ coreActionKernel (pumpUp K₁ v) := by
  have hgs := gsFixedLayer_eq_of_le hK₁u hK₁p hK₁v
  have hJP : K₁ ≤ pumpUp K₁ v := le_pumpUp hgs
  have hcN : c ∈ normalizer (pumpUp K₁ v : Set G) :=
    mem_normalizer_pumpUp_of_mem_normalizer (mem_coreActionKernel.mp hcK).1
      (mem_centralizer_singleton_iff.mpr hcv)
  refine GSThmB.mem_coreActionKernel_of_sup hJP hsup hcN fun y hy => ?_
  exact GSLit.map_pPrimeCore_le_of_sup_eq hsup ((mem_coreActionKernel.mp hcK).2 y hy)

theorem gsUnbalancingTriple_of_pumpUp_eq (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {u t b : G} {K₁ : Subgroup G}
    (hT : GSUnbalancingTriple u t K₁) (hb : orderOf b = 2) (hbZ : b ∉ center G)
    (hub : u * b = b * u) (htb : t * b = b * t) (hK₁b : K₁ ≤ centralizer ({b} : Set G))
    (hP : pumpUp K₁ b = K₁) : GSUnbalancingTriple b t K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := hT
  obtain ⟨hu, -, -, hK₁u, hK₁p, -, -⟩ := hT'
  have hK₁bp : IsPComponent 2 (K₁.subgroupOf (centralizer ({b} : Set G))) :=
    isPComponent_of_pumpUp_eq hS hK hu hb hub hbZ hK₁u hK₁p hK₁b hP
  have hbN : b ∈ normalizer (K₁ : Set G) :=
    mem_normalizer_of_commute fun j hj => (mem_centralizer_singleton_iff.mp (hK₁b hj)).symm
  have hJb : ∀ j ∈ K₁, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 K₁).map K₁.subtype := by
    intro j hj
    rw [show j⁻¹ * b⁻¹ * j * b = j⁻¹ * b⁻¹ * (j * b) by group,
      mem_centralizer_singleton_iff.mp (hK₁b hj), show j⁻¹ * b⁻¹ * (b * j) = 1 by group]
    exact one_mem _
  obtain ⟨M, hMb, hMp, hTM, hle, -, -, -, -⟩ :=
    UGSChain.kProper_unbalancing_orbit_target_production_of_schreier hS hK hT hb hbZ hub htb hbN
      hJb
  rw [gsFixedLayer_eq_of_le hK₁u hK₁p hK₁b] at hle
  have huC : u ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.mpr hub
  obtain ⟨hMuC, hMup⟩ := GSThmB.isPComponent_conjugate_centralizer_singleton hMb hMp huC
  have hle' : (K₁.subgroupOf (centralizer ({b} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))) ≤
      ((M ⊔ conjugate M u).subgroupOf (centralizer ({b} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))) :=
    map_mono fun x hx => mem_subgroupOf.mpr (hle (mem_subgroupOf.mp hx))
  rcases GSLit.eq_or_eq_of_map_le_sup hK₁b hK₁bp hMb hMp hMuC hMup hle' with h | h
  · rw [h]
    exact hTM
  · have huN : u⁻¹ ∈ normalizer (K₁ : Set G) := inv_mem
      (mem_normalizer_of_commute fun j hj => (mem_centralizer_singleton_iff.mp (hK₁u hj)).symm)
    have hM : M = K₁ := by
      have h1 : conjugate K₁ u⁻¹ = M := by
        rw [h, conjugate_conjugate, mul_inv_cancel, conjugate_one]
      rw [← h1]
      exact conjugate_eq_of_mem_normalizer huN
    rw [← hM]
    exact hTM

theorem twoExp_le_of_setting
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (h58 : L34Lemma58) (h59 : L34Lemma59) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) :
    (S ⊓ coreActionKernel L ⊓ L = ⊥ → twoExp (zStarIn L) = 0) ∧
      (S ⊓ coreActionKernel L ⊓ L ≠ ⊥ →
        twoExp (zStarIn L) ≤ 2 ∧ twoExp (coreActionKernel L) ≤ 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have hZn : ((zStarIn L).subgroupOf L).Normal := by
    have h1 : (zStarIn L).subgroupOf L = Open.fusionZStar L :=
      comap_map_eq_self_of_injective L.subtype_injective _
    rw [h1, Sol78.fusionZStar_eq_comap]
    exact Subgroup.Normal.comap inferInstance _
  have hZsyl : IsSylowTwoIn (S ⊓ L ⊓ zStarIn L) (zStarIn L) :=
    isSylowTwoIn_inf_of_isSubnormal hS₀ (map_subtype_le _) hZn.isSubnormal
  have hZQ : S ⊓ L ⊓ zStarIn L ≤ S ⊓ coreActionKernel L ⊓ L := fun x hx =>
    mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).1).1,
      zStarIn_le_coreActionKernel L (mem_inf.mp hx).2⟩, (mem_inf.mp (mem_inf.mp hx).1).2⟩
  have hZc := card_eq_two_pow_twoExp hZsyl
  refine ⟨fun hZ => ?_, fun hZ => ?_⟩
  · rw [hZ, le_bot_iff] at hZQ
    rw [hZQ, card_bot] at hZc
    have h1 : 2 ^ twoExp (zStarIn L) = 2 ^ 0 := by rw [← hZc, pow_zero]
    exact Nat.pow_right_injective (le_refl 2) h1
  obtain ⟨hQΩ, -⟩ := (h58 G L t S T hset).2 hZ
  obtain ⟨z, hzo, hzt, hΩ, -, -⟩ := h59 G L t S T hset
  have hz2 : z * z = 1 := by rw [← pow_two, ← hzo, pow_orderOf_eq_one]
  have hzQ : z ∈ S ⊓ coreActionKernel L := by
    rw [hQΩ, hΩ]
    exact mem_sup_right (mem_zpowers z)
  have hzt' : z ∉ zpowers t := fun h => by
    rcases eq_one_or_eq_of_mem_zpowers' ht2 h with h1 | h1
    · rw [h1] at hzo
      simp at hzo
    · exact hzt h1
  obtain ⟨-, hcard⟩ := elemTwo_zpowers_sup hz2 (isElemTwo_zpowers ht2) (fun y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hZS z (mem_inf.mp hzQ).1) k).eq) hzt'
  have hQ4 : Nat.card ↥(S ⊓ coreActionKernel L) = 4 := by
    rw [hQΩ, hΩ, sup_comm, hcard, Nat.card_zpowers, hto]
  have hKN : coreActionKernel L ≤ normalizer (L : Set G) := fun g hg =>
    (mem_coreActionKernel.mp hg).1
  have hQsyl : IsSylowTwoIn (S ⊓ coreActionKernel L) (coreActionKernel L) :=
    isSylowTwoIn_inf_of_isSubnormal hSyl hKN ((normal_subgroupOf_iff_le_normalizer hKN).mpr
      (normalizer_le_normalizer_coreActionKernel L)).isSubnormal
  have hQc := card_eq_two_pow_twoExp hQsyl
  rw [hQ4] at hQc
  have hle4 : 2 ^ twoExp (zStarIn L) ≤ 2 ^ 2 := by
    rw [← hZc]
    exact (card_le_of_le (hZQ.trans inf_le_left)).trans (by rw [hQ4]; norm_num)
  refine ⟨(Nat.pow_le_pow_iff_right (by norm_num)).mp hle4, ?_⟩
  have h1 : 2 ^ twoExp (coreActionKernel L) = 2 ^ 2 := by rw [← hQc]; norm_num
  exact (Nat.pow_right_injective (le_refl 2) h1).le

theorem false_of_selfCentralizing_kernel {K₁ L₁ U E : Subgroup G} {v : G}
    (hUK : U ≤ coreActionKernel K₁) (hU : IsElemTwo U) (hU4 : Nat.card U = 4) (hvU : v ∈ U)
    (hCK : ∀ c ∈ coreActionKernel K₁, c * v = v * c → c ∈ coreActionKernel L₁)
    (hbound : twoExp (coreActionKernel L₁) ≤ 2)
    (hEK : E ≤ coreActionKernel K₁) (hE : IsElemTwo E) (hE8 : 8 ≤ Nat.card E) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hUP⟩ := L34Central.exists_isSylowTwoIn_le hUK hU.isPGroup
  have hP2 : IsPGroup 2 P := IsSylowTwoIn.isPGroup hP
  obtain ⟨g, -, hEg⟩ := exists_conjugate_le_of_isSylowTwoIn hP hEK hE.isPGroup
  have h1 : P ⊓ centralizer (U : Set G) ≤ coreActionKernel L₁ := fun c hc =>
    hCK c (hP.1 (mem_inf.mp hc).1) ((mem_centralizer_iff.mp (mem_inf.mp hc).2) v hvU).symm
  have h2 : Nat.card ↥(P ⊓ centralizer (U : Set G)) ≤ 4 :=
    (card_le_two_pow_twoExp h1 (hP2.to_le inf_le_left)).trans
      ((Nat.pow_le_pow_right (by norm_num) hbound).trans (by norm_num))
  have h3 : U ≤ P ⊓ centralizer (U : Set G) :=
    le_inf hUP fun x hx => mem_centralizer_iff.mpr fun y hy => hU.1 y hy x hx
  have hC : P ⊓ centralizer (U : Set G) ≤ U :=
    (eq_of_le_of_card_ge h3 (by rw [hU4]; exact h2)).ge
  refine false_of_selfCentralizing_four_of_elemTwo hP2 hUP hU4 hU.2 hC hEg (fun x hx => ?_)
    (by rw [GSLit.card_conjugate]; exact hE8)
  rw [mem_conjugate_iff] at hx
  have h4 := hE.2 _ hx
  have e : x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
  rw [e, h4, mul_one, inv_mul_cancel]

end CFSG.ComponentClassification.GrSLit.GrS5
