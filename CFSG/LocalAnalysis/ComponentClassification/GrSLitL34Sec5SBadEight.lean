module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SBadTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFour
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34OrbitParity

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_bad_ne
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) (h58 : L34Lemma58)
    (h59 : L34Lemma59) (hSC : L34AutSylowCenterFact) (hUnit : L34UnbalancingUnitaryStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁)
    (htype₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁)) (hO : ∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x)
    {S₁ : Subgroup G} (hS₁ : IsSylowTwoIn S₁ (normalizer (K₁ : Set G))) (hSS₁ : S ≤ S₁) {b : G}
    (hb : b ∈ S₁ ⊓ zStarIn K₁) (hbo : orderOf b = 2) (hbc : ∀ s ∈ S₁, s * b = b * s)
    (h1 : twoExp (zStarIn K₁) = 1) (h3 : twoExp (zStarIn L) = 2) (hbu : b ≠ u) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have htKL : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have hperfL : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hu' := hu
  obtain ⟨huS₀, hu2, hun⟩ := hu'
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hYodd : Odd (Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) := by
    have h1 : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact Odd.of_dvd_nat h1 (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨y₀, hy₀, hy₀1⟩ : ∃ y ∈ oddIn L ⊓ centralizer ({u} : Set G), y ≠ 1 := by
    by_contra h
    push Not at h
    exact hun fun y hy => by rw [h y hy]; exact one_mem _
  obtain ⟨hZ, hQL⟩ := le_of_twoExp_eq_two hS hU hheld hSol hGW h58 h59 hset h3
  have htL : t ∈ L := hQL (mem_inf.mpr ⟨htS, htKL⟩)
  have huL : u ∈ L := (sup_le inf_le_right (zpowers_le.mpr htL) : S ⊓ L ⊔ zpowers t ≤ L) huS₀
  obtain ⟨hbS₁, hbZ⟩ := mem_inf.mp hb
  have hb2 : b * b = 1 := by rw [← pow_two, ← hbo, pow_orderOf_eq_one]
  have hb1 : b ≠ 1 := by rintro rfl; simp at hbo
  have hbN : b ∈ normalizer (L : Set G) :=
    hCN (mem_centralizer_singleton_iff.mpr (hbc t (hSS₁ htS)).symm)
  have hbS : b ∈ S :=
    HSFLit.L34Inv.mem_of_isSylowTwoIn hSyl hbN hb2 fun s hs => hbc s (hSS₁ hs)
  have hexp : ∀ x ∈ S ⊓ zStarIn L, x * x = 1 := fun x hx =>
    ((h58 G L t S T hset).2 hZ).2 x (mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hx).1,
      zStarIn_le_coreActionKernel L (mem_inf.mp hx).2⟩, map_subtype_le _ (mem_inf.mp hx).2⟩)
  have hbZQ := (hSC G L S hperfL htypeL hSyl hexp).1 b hbS S le_rfl (by omega) fun s hs => by
    rw [show s⁻¹ * b⁻¹ * s * b = 1 by
      calc s⁻¹ * b⁻¹ * s * b = s⁻¹ * b⁻¹ * (s * b) := by group
        _ = s⁻¹ * b⁻¹ * (b * s) := by rw [hbc s (hSS₁ hs)]
        _ = 1 := by group]
    exact one_mem _
  have hbL : b ∈ L := (sup_le (inf_le_left.trans inf_le_right) hQL :
    S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊔ S ⊓ coreActionKernel L ≤ L) hbZQ
  have hXb := commute_of_mem_zStarIn hSol hto hu2 htu hYD hK₁u hK₁p hO hS₁ hb hbo h1
  have hQinv : ∀ q ∈ S ⊓ coreActionKernel L, orderOf q = 2 → q ≠ t →
      (∀ y ∈ oddIn L ⊓ centralizer ({u} : Set G), y * q = q * y) → False := by
    intro q hq hqo hqt hqc
    have h1 := conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset hq hqo hqt y₀
      (mem_inf.mp hy₀).1
    have h2 : q * y₀ * q⁻¹ = y₀ := by rw [← hqc y₀ hy₀, mul_assoc, mul_inv_cancel, mul_one]
    rw [h2] at h1
    exact hy₀1 (eq_one_of_mul_self_of_odd hYodd hy₀ (by
      calc y₀ * y₀ = y₀ * y₀⁻¹ := congrArg (fun w => y₀ * w) h1
        _ = 1 := mul_inv_cancel y₀))
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have htK₁ : t ∉ coreActionKernel K₁ := fun h =>
    (hUnit G u t K₁ hT₁ htype₁).2.2.1 (mem_sup_right h)
  have hK₁b : K₁ ≤ centralizer ({b} : Set G) := le_centralizer_of_mem_zStarIn hK₁u hK₁p hO hbZ
  have hbK : b ∉ coreActionKernel L := by
    intro hbK
    by_cases hbt : b = t
    · apply htK₁
      rw [← hbt]
      exact mem_coreActionKernel_of_commute fun k hk =>
        (mem_centralizer_singleton_iff.mp (hK₁b hk)).symm
    · exact hQinv b (mem_inf.mpr ⟨hbS, hbK⟩) hbo hbt hXb
  have hub : u * b = b * u := hbc u (hSS₁ huS)
  have hubK : u * b ∉ coreActionKernel L := by
    intro hK
    have hub2 : u * b * (u * b) = 1 := by
      calc u * b * (u * b) = u * (b * u) * b := by group
        _ = u * (u * b) * b := by rw [hub]
        _ = (u * u) * (b * b) := by group
        _ = 1 := by rw [hu2', hb2, one_mul]
    have hub1 : u * b ≠ 1 := fun h => hbu (by
      rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hu2'])
    by_cases hubt : u * b = t
    · apply htK₁
      rw [← hubt]
      exact mem_coreActionKernel_of_commute fun k hk => by
        have e1 : k * u = u * k := mem_centralizer_singleton_iff.mp (hK₁u hk)
        have e2 : k * b = b * k := mem_centralizer_singleton_iff.mp (hK₁b hk)
        calc u * b * k = u * (b * k) := by group
          _ = u * (k * b) := by rw [e2]
          _ = u * k * b := by group
          _ = k * u * b := by rw [e1]
          _ = k * (u * b) := by group
    · exact hQinv (u * b) (mem_inf.mpr ⟨mul_mem huS hbS, hK⟩)
        (orderOf_eq_prime (by rw [pow_two]; exact hub2) hub1) hubt fun y hy => by
          have e1 : y * u = u * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
          have e2 : y * b = b * y := hXb y hy
          calc y * (u * b) = y * u * b := by group
            _ = u * y * b := by rw [e1]
            _ = u * (y * b) := by group
            _ = u * (b * y) := by rw [e2]
            _ = u * b * y := by group
  have hbu' : b ∉ zpowers u := fun h => by
    rcases eq_one_or_eq_of_mem_zpowers' hu2' h with h' | h'
    · exact hb1 h'
    · exact hbu h'
  have hbcu : ∀ y ∈ zpowers u, b * y = y * b := fun y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute b u from hub.symm) k).eq
  obtain ⟨hBel, hBc⟩ := elemTwo_zpowers_sup hb2 (isElemTwo_zpowers hu2') hbcu hbu'
  refine false_of_four_le_centralizer hS hU hheld hSol hGW hset hmax
    (sup_le (zpowers_le.mpr (mem_inf.mpr ⟨hbS, hbL⟩)) (zpowers_le.mpr (mem_inf.mpr ⟨huS, huL⟩)))
    hBel (by have h := hBc; rw [Nat.card_zpowers, hu2] at h; omega) ?_ ?_
  · intro a ha ha1
    obtain ⟨i, w, hw, rfl⟩ := mem_zpowers_sup hbcu ha
    rcases eq_one_or_eq_of_mem_zpowers' hb2 (zpow_mem (mem_zpowers b) i) with h | h <;>
      rcases eq_one_or_eq_of_mem_zpowers' hu2' hw with h' | h' <;> rw [h, h'] at ha1 ⊢
    · exact absurd (one_mul (1 : G)) ha1
    · rw [one_mul]
      exact HSFLit.L34Uniq.not_mem_coreActionKernel_of_unbalancing hS hU hheld hSol hGW hMax hL34
        hset hu
    · rw [mul_one]
      exact hbK
    · rw [← hub]
      exact hubK
  · intro a ha y hy
    have hB : zpowers b ⊔ zpowers u ≤ centralizer ({y} : Set G) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hXb y hy).symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2).symm))
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hB ha)).symm

end CFSG.ComponentClassification.GrSLit.GrS5S
