module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5OTwoTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsOTwo

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddIn_le_map_center {K : Subgroup G} (hO : ∀ x ∈ oddIn K, ∀ k ∈ K, x * k = k * x) :
    oddIn K ≤ (center ↥K).map K.subtype := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, mem_center_iff.mpr fun m => Subtype.ext (hO _ ⟨y, hy, rfl⟩ m m.2).symm, rfl⟩

theorem le_centralizer_of_mem_zStarIn {C K : Subgroup G} (hKC : K ≤ C)
    (hKp : IsPComponent 2 (K.subgroupOf C)) (hO : ∀ x ∈ oddIn K, ∀ k ∈ K, x * k = k * x)
    {b : G} (hb : b ∈ zStarIn K) : K ≤ centralizer ({b} : Set G) := by
  have hq := isQuasisimple_of_oddIn_le_center hKC hKp (oddIn_le_map_center hO)
  have hO' : pPrimeCore 2 ↥K ≤ center ↥K := fun y hy =>
    mem_center_iff.mpr fun m => Subtype.ext (hO _ ⟨y, hy, rfl⟩ m m.2).symm
  have heq := fusionZStar_eq_center_of_le hq.1.commutator_eq_top hO'
  obtain ⟨w, hw, rfl⟩ := hb
  rw [heq] at hw
  intro k hk
  exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val ((mem_center_iff.mp hw) ⟨k, hk⟩))

theorem twoExp_coreActionKernel_pumpUp_le
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hBd : L34Lemma510OTwoBoundStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) (huc : ∀ s ∈ S, s * u = u * s)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁)
    (htype₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁))
    (hO : ∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x) (hev : Even (Nat.card ↥(zStarIn K₁)))
    {S₁ : Subgroup G} (hS₁ : IsSylowTwoIn S₁ (normalizer (K₁ : Set G))) (hSS₁ : S ≤ S₁) {b : G}
    (hb : b ∈ S₁ ⊓ zStarIn K₁) (hbo : orderOf b = 2) (hbc : ∀ s ∈ S₁, s * b = b * s)
    (hPb : pumpUp K₁ b = K₁)
    (hW : ∀ A : Subgroup G, A ≤ withKernel K₁ → IsEightGroup A → wGroup A = ⊥)
    {v : G} (hK₁v : K₁ ≤ centralizer ({v} : Set G)) (hfam : IsL34Family (pumpUp K₁ v) v)
    (hsup : K₁ ⊔ oddIn (pumpUp K₁ v) = pumpUp K₁ v) (hne : b ≠ v) :
    twoExp (coreActionKernel (pumpUp K₁ v)) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨-, -, hlexmax, -, -, -, -⟩ := hset'
  have hlex := hlexmax _ v hfam
  rw [Prod.Lex.toLex_le_toLex] at hlex
  have hfam' := hfam
  obtain ⟨⟨-, -, -, -, -, hvo, -, -⟩, -⟩ := hfam'
  have hK₁L₁ : K₁ ≤ pumpUp K₁ v := le_sup_left.trans hsup.le
  have he₁ : 1 ≤ twoExp (zStarIn K₁) :=
    le_twoExp_of_dvd (by rw [pow_one]; exact even_iff_two_dvd.mp hev)
  have hzle := twoExp_zStarIn_le_of_sup_oddIn hK₁L₁ hsup
  obtain ⟨h0, h12⟩ := twoExp_le_of_setting hS hU hheld hSol hGW h58 h59 hset
  by_cases hZ : S ⊓ coreActionKernel L ⊓ L = ⊥
  · exfalso
    have hz0 := h0 hZ
    rcases hlex with h | ⟨h, -⟩
    · dsimp only at h
      omega
    · dsimp only at h
      omega
  · obtain ⟨hzL, hcL⟩ := h12 hZ
    rcases hlex with h | ⟨-, h⟩
    ·
      dsimp only at h
      exact hBd G L t S T hset u hu huc hmax K₁ hK₁u hK₁p hK₁n htype₁ hO S₁ hS₁ hSS₁ b hb hbo hbc
        hPb hW v hvo hK₁v hfam hsup hne (by omega) (by omega) (by omega)
    · dsimp only at h
      exact h.trans hcL

theorem false_of_pumpUp_family
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hBd : L34Lemma510OTwoBoundStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) (huc : ∀ s ∈ S, s * u = u * s)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁)
    (htype₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁))
    (hO : ∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x) (hev : Even (Nat.card ↥(zStarIn K₁)))
    {F : Subgroup G} (hFK : F ≤ coreActionKernel K₁) (hF : IsElemTwo F) (hF8 : 8 ≤ Nat.card F)
    {S₁ : Subgroup G} (hS₁ : IsSylowTwoIn S₁ (normalizer (K₁ : Set G))) (hSS₁ : S ≤ S₁) {w : G}
    (hb : w ∈ S₁ ⊓ zStarIn K₁) (hw : orderOf w = 2) (hbc : ∀ s ∈ S₁, s * w = w * s)
    (hPb : pumpUp K₁ w = K₁)
    (hW : ∀ A : Subgroup G, A ≤ withKernel K₁ → IsEightGroup A → wGroup A = ⊥)
    {v : G} (hwv : w * v = v * w) (hne : w ≠ v)
    (hK₁w : K₁ ≤ centralizer ({w} : Set G)) (hK₁v : K₁ ≤ centralizer ({v} : Set G))
    (hfam : IsL34Family (pumpUp K₁ v) v) (hsup : K₁ ⊔ oddIn (pumpUp K₁ v) = pumpUp K₁ v) :
    False := by
  have hbound := twoExp_coreActionKernel_pumpUp_le hS hU hheld hSol hGW h58 h59 hBd hset hu huc
    hmax hK₁u hK₁p hK₁n htype₁ hO hev hS₁ hSS₁ hb hw hbc hPb hW hK₁v hfam hsup hne
  have hfam' := hfam
  obtain ⟨⟨-, -, -, -, -, hvo, -, -⟩, -⟩ := hfam'
  have hv2 : v * v = 1 := by rw [← pow_two, ← hvo, pow_orderOf_eq_one]
  have hw2 : w * w = 1 := by rw [← pow_two, ← hw, pow_orderOf_eq_one]
  have hwn : w ∉ zpowers v := fun h => by
    rcases eq_one_or_eq_of_mem_zpowers' hv2 h with h1 | h1
    · rw [h1] at hw
      simp at hw
    · exact hne h1
  obtain ⟨hUel, hUc⟩ := elemTwo_zpowers_sup hw2 (isElemTwo_zpowers hv2) (fun y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute w v from hwv) k).eq) hwn
  have hU4 : Nat.card ↥(zpowers w ⊔ zpowers v) = 4 := by rw [hUc, Nat.card_zpowers, hvo]
  have hUK : zpowers w ⊔ zpowers v ≤ coreActionKernel K₁ := sup_le
    (zpowers_le.mpr (mem_coreActionKernel_of_commute fun l hl =>
      (mem_centralizer_singleton_iff.mp (hK₁w hl)).symm))
    (zpowers_le.mpr (mem_coreActionKernel_of_commute fun l hl =>
      (mem_centralizer_singleton_iff.mp (hK₁v hl)).symm))
  exact false_of_selfCentralizing_kernel hUK hUel hU4 (mem_sup_right (mem_zpowers v))
    (fun c hc hcv => mem_coreActionKernel_pumpUp hK₁u hK₁p hK₁v hsup hc hcv) hbound hFK hF hF8

end CFSG.ComponentClassification.GrSLit.GrS5
