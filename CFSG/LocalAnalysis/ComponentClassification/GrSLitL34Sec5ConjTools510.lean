module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Conj510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma55

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_mul_eq_of_le_centralizer {X : Subgroup G} {τ : G}
    (hX : X ≤ centralizer ({τ} : Set G)) (h : G) :
    X ⊓ centralizer ({τ * h} : Set G) = X ⊓ centralizer ({h} : Set G) := by
  ext x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  refine ⟨fun ⟨hx, hc⟩ => ⟨hx, ?_⟩, fun ⟨hx, hc⟩ => ⟨hx, ?_⟩⟩
  · have hxτ : x * τ = τ * x := mem_centralizer_singleton_iff.mp (hX hx)
    have h1 : τ * (x * h) = τ * (h * x) := by
      calc τ * (x * h) = (τ * x) * h := by group
        _ = (x * τ) * h := by rw [hxτ]
        _ = x * (τ * h) := by group
        _ = τ * h * x := hc
        _ = τ * (h * x) := by group
    exact mul_left_cancel h1
  · have hxτ : x * τ = τ * x := mem_centralizer_singleton_iff.mp (hX hx)
    calc x * (τ * h) = (x * τ) * h := by group
      _ = τ * (x * h) := by rw [hxτ]; group
      _ = τ * (h * x) := by rw [hc]
      _ = τ * h * x := by group

omit [Finite G] in
theorem card_inf_centralizer_conj {L : Subgroup G} {l : G} (hl : l ∈ L) (h : G) :
    Nat.card ↥(oddIn L ⊓ centralizer ({l⁻¹ * h * l} : Set G)) =
      Nat.card ↥(oddIn L ⊓ centralizer ({h} : Set G)) := by
  have hlN : l ∈ normalizer (oddIn L : Set G) :=
    normalizer_le_normalizer_oddIn L (le_normalizer hl)
  have hCX : conjugate (oddIn L ⊓ centralizer ({h} : Set G)) l =
      oddIn L ⊓ centralizer ({l⁻¹ * h * l} : Set G) := by
    rw [show conjugate (oddIn L ⊓ centralizer ({h} : Set G)) l =
        conjugate (oddIn L) l ⊓ conjugate (centralizer ({h} : Set G)) l from
      Subgroup.map_inf_eq _ _ _ (MulAut.conj l⁻¹).injective, conjugate_eq_self hlN,
      conjugate_centralizer_singleton]
  rw [← hCX]
  exact card_map_of_injective (MulAut.conj l⁻¹).injective

theorem exists_conj_eq_mul_of_involution
    {L S : Subgroup G}
    (htype : IsL34Type (↥L ⧸ Open.fusionZStar ↥L)) (hS₀ : IsSylowTwoIn (S ⊓ L) L)
    (hexp : ∀ z ∈ S ⊓ L ⊓ zStarIn L, z * z = 1) {y : G} (hyL : y ∈ L) (hyZ : y ∉ zStarIn L)
    (hy2 : y * y = 1) (hyc : ∀ z ∈ S ⊓ L ⊓ zStarIn L, y * z = z * y) {h : G} (hhL : h ∈ L)
    (hh2 : h * h = 1) (hhZ : h ∉ zStarIn L) :
    ∃ l ∈ L, ∃ z ∈ S ⊓ L ⊓ zStarIn L, l⁻¹ * h * l = y * z := by
  obtain ⟨g, hgL, hg⟩ := exists_conj_inv_mul_mem_zStarIn htype hhL hyL hh2 hy2 hhZ hyZ
  have hx2 : g⁻¹ * h * g * (g⁻¹ * h * g) = 1 := by
    rw [show g⁻¹ * h * g * (g⁻¹ * h * g) = g⁻¹ * (h * h) * g by group, hh2, mul_one,
      inv_mul_cancel]
  have hw := GrS4.zStarIn_le_oddIn_sup hS₀ hg
  rw [sup_comm] at hw
  have hle : S ⊓ L ⊓ zStarIn L ≤ normalizer (oddIn L : Set G) := fun w hw =>
    normalizer_le_normalizer_oddIn L (le_normalizer (mem_inf.mp (mem_inf.mp hw).1).2)
  have hw' : y⁻¹ * (g⁻¹ * h * g) ∈ ((S ⊓ L ⊓ zStarIn L ⊔ oddIn L : Subgroup G) : Set G) := hw
  rw [coe_mul_of_left_le_normalizer_right _ _ hle] at hw'
  obtain ⟨z, hz, o, ho, hzo⟩ := hw'
  have hzo' : z * o = y⁻¹ * (g⁻¹ * h * g) := hzo
  have hz2 : z * z = 1 := hexp z hz
  have hzy : y * z = z * y := hyc z hz
  have hyz2 : y * z * (y * z) = 1 := by
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [hzy]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hy2, hz2, one_mul]
  have hx' : g⁻¹ * h * g = y * (z * o) := by
    rw [hzo']
    group
  have hyx : y * z * (g⁻¹ * h * g) = o := by
    rw [hx']
    calc y * z * (y * (z * o)) = y * (z * y) * z * o := by group
      _ = y * (y * z) * z * o := by rw [hzy]
      _ = (y * y) * (z * z) * o := by group
      _ = o := by rw [hy2, hz2, one_mul, one_mul]
  have hodd : Odd (orderOf (y * z * (g⁻¹ * h * g))) := by
    rw [hyx]
    have h1 : orderOf o ∣ Nat.card (oddIn L) := by
      have := orderOf_dvd_natCard (⟨o, ho⟩ : oddIn L)
      rwa [Subgroup.orderOf_mk] at this
    have hoddL : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact hoddL.of_dvd_nat h1
  obtain ⟨c, hc, hcx⟩ := exists_conj_eq_of_odd_orderOf hyz2 hx2 hodd
  rw [hyx] at hc
  have hcL : c ∈ L := map_subtype_le _ ((zpowers_le.mpr ho) hc)
  refine ⟨g * c⁻¹, mul_mem hgL (inv_mem hcL), z, hz, ?_⟩
  rw [show (g * c⁻¹)⁻¹ * h * (g * c⁻¹) = c * (g⁻¹ * h * g) * c⁻¹ by group, ← hcx]
  group

theorem exists_eq_zpow_mul_of_mem_unbalancingSet
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) :
    ∃ i : ℤ, ∃ s ∈ S ⊓ L, u = t ^ i * s ∧ s * s = 1 ∧ s ∉ zStarIn L := by
  have hset' := hset
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, -, htS, -, -⟩ := hset
  obtain ⟨huU, huo, huX⟩ := hu
  have hu2 : u * u = 1 := by rw [← pow_two, ← huo, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS)) huU
  have hXt : oddIn L ≤ oddIn (centralizer ({t} : Set G)) :=
    GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt
  have htL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLt hl)
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    ((mem_centralizer_iff.mp htL) l hl).symm
  have hoddX : Odd (Nat.card (oddIn L)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have huU' : u ∈ zpowers t ⊔ S ⊓ L := by rwa [sup_comm] at huU
  obtain ⟨i, s, hs, hus⟩ := mem_zpowers_sup (fun y hy => (hZS y (mem_inf.mp hy).1).symm) huU'
  refine ⟨i, s, hs, hus, ?_, ?_⟩
  · have hsτ : s * t ^ i = t ^ i * s := (Commute.zpow_right (hZS s (mem_inf.mp hs).1) i).eq
    have hττ : t ^ i * t ^ i = 1 := by
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ht2, one_zpow]
    have h1 : t ^ i * s * (t ^ i * s) = 1 := hus ▸ hu2
    calc s * s = t ^ i * t ^ i * (s * s) := by rw [hττ, one_mul]
      _ = t ^ i * (t ^ i * s) * s := by group
      _ = t ^ i * (s * t ^ i) * s := by rw [hsτ]
      _ = t ^ i * s * (t ^ i * s) := by group
      _ = 1 := h1
  · intro hsZ
    have hsK : s ∈ coreActionKernel L := zStarIn_le_coreActionKernel L hsZ
    have huQ : u ∈ S ⊓ coreActionKernel L :=
      mem_inf.mpr ⟨huS, hus ▸ mul_mem (zpow_mem htK i) hsK⟩
    apply huX
    by_cases hut : u = t
    · rw [hut]
      exact inf_le_left.trans hXt
    · have hinv := conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset' huQ huo hut
      intro y hy
      obtain ⟨hyX, hyu⟩ := mem_inf.mp hy
      have h1 := hinv y hyX
      have h2 : u * y = y * u := (mem_centralizer_singleton_iff.mp hyu).symm
      have hy2 : y * y ∈ (⊥ : Subgroup G) := by
        rw [mem_bot, mul_eq_one_iff_eq_inv]
        rw [← h1, h2, mul_inv_cancel_right]
      have hyo : Odd (orderOf y) := hoddX.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hyX)
      have hy1 := mem_bot.mp (mem_of_mul_self_mem_of_odd hyo hy2)
      rw [hy1]
      exact one_mem _

end CFSG.ComponentClassification.GrSLit.GrS5
