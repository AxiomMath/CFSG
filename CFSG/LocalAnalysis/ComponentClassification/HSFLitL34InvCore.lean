module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvKernel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvSylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma55
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvTools

public section

namespace CFSG.ComponentClassification.HSFLit.L34Inv

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem odd_orderOf_of_mem_centralizer {K : Subgroup G} (hZodd : Odd (Nat.card ↥(zStarIn K)))
    {c : G} (hc : c ∈ K) (hcC : c ∈ centralizer (K : Set G)) : Odd (orderOf c) := by
  have h1 : c ∈ zStarIn K := by
    rw [L34Facts.mem_zStarIn_iff hc, mem_center_iff]
    intro e
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) e
    have hj : (j : G) * c = c * j := mem_centralizer_iff.mp hcC j j.2
    have hj' : j * (⟨c, hc⟩ : K) = ⟨c, hc⟩ * j := Subtype.ext hj
    show L34Facts.jq K j * L34Facts.jq K ⟨c, hc⟩ = L34Facts.jq K ⟨c, hc⟩ * L34Facts.jq K j
    rw [← map_mul, ← map_mul, hj']
  exact Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard _ h1)

omit [Finite G] in
theorem eq_or_eq_mul_of_mem_two {t z y z₀ : G} (ht : t * t = 1) (htz : t * z = z * t)
    (hy : y = z ∨ y = t * z) (hz₀ : z₀ = z ∨ z₀ = t * z) : y = z₀ ∨ y = t * z₀ := by
  rcases hy with rfl | rfl <;> rcases hz₀ with rfl | rfl
  · exact Or.inl rfl
  · right
    rw [← mul_assoc, ht, one_mul]
  · right; rfl
  · exact Or.inl rfl

theorem conj_eq_or_of_mem_omegaOne
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput) (h59 : L34Lemma59)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {z₀ : G}
    (hz₀Ω : z₀ ∈ omegaOne (S ⊓ coreActionKernel L)) (hz₀1 : z₀ ≠ 1) (hz₀t : z₀ ≠ t) :
    z₀ * z₀ = 1 ∧ ∀ s ∈ S, s * z₀ * s⁻¹ = z₀ ∨ s * z₀ * s⁻¹ = t * z₀ := by
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, -, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  obtain ⟨z, hz, -, hΩ, -, -⟩ := h59 G L t S T hset
  have hzΩ : z ∈ omegaOne (S ⊓ coreActionKernel L) := by
    rw [hΩ]; exact mem_sup_right (mem_zpowers z)
  have hzS : z ∈ S := (mem_inf.mp (omegaOne_le _ hzΩ)).1
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have htz : t * z = z * t := (hZS z hzS).symm
  have htwo : ∀ y ∈ omegaOne (S ⊓ coreActionKernel L), y ≠ 1 → y ≠ t → y = z ∨ y = t * z := by
    intro y hy hy1 hyt
    rw [hΩ] at hy
    rcases mem_four_of_mem_sup ht2 hz2 htz hy with h | h | h | h
    · exact absurd h hy1
    · exact absurd h hyt
    · exact Or.inl h
    · exact Or.inr h
  have hz₀zz := htwo z₀ hz₀Ω hz₀1 hz₀t
  have hz₀2 : z₀ * z₀ = 1 := by
    rcases hz₀zz with rfl | rfl
    · exact hz2
    · calc t * z * (t * z) = t * (z * t) * z := by group
        _ = t * (t * z) * z := by rw [htz]
        _ = (t * t) * (z * z) := by group
        _ = 1 := by rw [ht2, hz2, one_mul]
  have hz₀Q : z₀ ∈ S ⊓ coreActionKernel L := omegaOne_le _ hz₀Ω
  refine ⟨hz₀2, fun s hs => ?_⟩
  have hsQ : s * z₀ * s⁻¹ ∈ S ⊓ coreActionKernel L :=
    mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hz₀Q).1) (inv_mem hs),
      conj_mem_coreActionKernel (hSyl.1 hs) (mem_inf.mp hz₀Q).2⟩
  have hsΩ : s * z₀ * s⁻¹ ∈ omegaOne (S ⊓ coreActionKernel L) := subset_closure
    ⟨hsQ, by rw [show s * z₀ * s⁻¹ * (s * z₀ * s⁻¹) = s * (z₀ * z₀) * s⁻¹ by group, hz₀2]; group⟩
  have hne1 : s * z₀ * s⁻¹ ≠ 1 := by
    intro h
    apply hz₀1
    calc z₀ = s⁻¹ * (s * z₀ * s⁻¹) * s := by group
      _ = 1 := by rw [h]; group
  have hnet : s * z₀ * s⁻¹ ≠ t := by
    intro h
    apply hz₀t
    calc z₀ = s⁻¹ * (s * z₀ * s⁻¹) * s := by group
      _ = s⁻¹ * (t * s) := by rw [h, mul_assoc]
      _ = t := by rw [← hZS s hs]; group
  exact eq_or_eq_mul_of_mem_two ht2 htz (htwo _ hsΩ hne1 hnet) hz₀zz

theorem exists_involution_of_inner
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) (h59 : L34Lemma59)
    (hType : L34Lemma55TypeStep) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) {u : G} (hu : u ∈ L34UnbalancingSet L t S)
    {K₁ : Subgroup G} (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁)
    (hSN : S ≤ normalizer (K₁ : Set G)) (hO : ∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x)
    (hodd : ∀ c ∈ K₁, c ∈ centralizer (K₁ : Set G) → Odd (orderOf c))
    (houter : ∀ j ∈ K₁, j⁻¹ * t ∉ coreActionKernel K₁)
    (hinner : ∃ z₀ ∈ omegaOne (S ⊓ coreActionKernel L), z₀ ≠ 1 ∧ z₀ ≠ t ∧
      ∃ j ∈ K₁, j⁻¹ * z₀ ∈ coreActionKernel K₁)
    (hconj : ∀ z₁ ∈ S ⊓ K₁, z₁ * z₁ = 1 → z₁ ≠ 1 → z₁ * t = t * z₁ →
      ∃ v ∈ K₁, v * z₁ = z₁ * v ∧ v⁻¹ * t * v = t * z₁) :
    ∃ z₁ ∈ S ⊓ coreActionKernel L, orderOf z₁ = 2 ∧ z₁ ≠ t ∧ z₁ ∈ K₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  obtain ⟨huS₀, hu2, -⟩ := hu
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hperf : ⁅K₁, K₁⁆ = K₁ := GSThmB.commutator_eq_self_of_isPComponent hK₁u hK₁p
  obtain ⟨z₀, hz₀Ω, hz₀1, hz₀t, j, hj, hjz⟩ := hinner
  obtain ⟨hz₀2, hconjS⟩ := conj_eq_or_of_mem_omegaOne hS hU hheld hSol hGW h59 hset hz₀Ω hz₀1 hz₀t
  have hz₀Q : z₀ ∈ S ⊓ coreActionKernel L := omegaOne_le _ hz₀Ω
  have hz₀o : orderOf z₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz₀2) hz₀1
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  obtain ⟨hDN, -⟩ := (solomon_involutions hSol hto hu2 htu).2 K₁ hK₁u hK₁p
  have hYodd : Odd (Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) := by
    have h1 : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact Odd.of_dvd_nat h1 (Subgroup.card_dvd_of_le inf_le_left)
  have hinv := conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset hz₀Q hz₀o hz₀t
  have hz₀K₁ : z₀ ∉ coreActionKernel K₁ :=
    not_mem_coreActionKernel_of_inverts hperf hO (fun d hd => hDN (hYD hd)) hYodd hK₁n
      fun y hy => hinv y (mem_inf.mp hy).1
  obtain ⟨z₁, hz₁K, hz₁2, hz₁1, hwC⟩ := exists_decomp hperf hO hodd hz₀2 hj hjz hz₀K₁
  have hz₀c : ∀ s ∈ S, s * z₀ * s⁻¹ = z₀ := by
    intro s hs
    rcases hconjS s hs with h | h
    · exact h
    · exact (false_of_decomp_mul houter hz₁K hwC (hSN hs) h).elim
  have hz₁S' : ∀ s ∈ S, s * z₁ = z₁ * s := by
    intro s hs
    have h1 := conj_eq_of_decomp hodd hz₁K hz₁2 hwC (hSN hs) (hz₀c s hs)
    calc s * z₁ = s * z₁ * s⁻¹ * s := by group
      _ = z₁ * s := by rw [h1]
  have hz₁t : z₁ * t = t * z₁ := (hz₁S' t htS).symm
  have hz₁N : z₁ ∈ normalizer (L : Set G) := hCN (mem_centralizer_singleton_iff.mpr hz₁t)
  have hz₁S : z₁ ∈ S := mem_of_isSylowTwoIn hSyl hz₁N hz₁2 hz₁S'
  obtain ⟨v, hvK, hvz₁, hv⟩ := hconj z₁ (mem_inf.mpr ⟨hz₁S, hz₁K⟩) hz₁2 hz₁1 hz₁t
  have hvz₀ : v * z₀ = z₀ * v := by
    have hw : v * (z₁⁻¹ * z₀) = z₁⁻¹ * z₀ * v := mem_centralizer_iff.mp hwC v hvK
    calc v * z₀ = v * z₁ * (z₁⁻¹ * z₀) := by group
      _ = z₁ * (v * (z₁⁻¹ * z₀)) := by rw [hvz₁, mul_assoc]
      _ = z₁ * (z₁⁻¹ * z₀ * v) := by rw [hw]
      _ = z₀ * v := by group
  have hz₁L : z₁ ∈ coreActionKernel L := mem_coreActionKernel_of_conj hS hU hheld hSol hGW hMax
    hL34 hType hset hz₀Q hz₀o hz₁t hvz₀ hv
  refine ⟨z₁, mem_inf.mpr ⟨hz₁S, hz₁L⟩, orderOf_eq_prime (by rw [pow_two]; exact hz₁2) hz₁1,
    ?_, hz₁K⟩
  rintro rfl
  exact houter z₁ hz₁K (by rw [inv_mul_cancel]; exact one_mem _)

end CFSG.ComponentClassification.HSFLit.L34Inv
