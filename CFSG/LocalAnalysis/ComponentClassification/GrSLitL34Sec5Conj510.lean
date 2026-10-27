module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Reduce510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs510C
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma44
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_eq_of_odd_orderOf {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x * y))) : ∃ c ∈ zpowers (x * y), c⁻¹ * x * c = y := by
  obtain ⟨m, hm⟩ := hodd
  set c := (x * y) ^ (m + 1) with hc
  have hcc : c * c = x * y := by
    rw [hc, ← pow_add, show m + 1 + (m + 1) = orderOf (x * y) + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hxinv : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hx, mul_inv_rev, inv_eq_of_mul_eq_one_right hx,
      inv_eq_of_mul_eq_one_right hy, ← mul_assoc, hx, one_mul]
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    have h := map_pow (MulAut.conj x) (x * y) (m + 1)
    simp only [MulAut.conj_apply] at h
    rw [hc, h, hxinv, inv_pow]
  refine ⟨c, pow_mem (mem_zpowers _) _, ?_⟩
  calc c⁻¹ * x * c = c⁻¹ * (x * c * x⁻¹) * x := by group
    _ = (c * c)⁻¹ * x := by rw [hxc]; group
    _ = y := by
      rw [hcc, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy,
        mul_assoc, hx, mul_one]

theorem exists_conj_inv_mul_mem_zStarIn
    {L : Subgroup G} (h : IsL34Type (↥L ⧸ Open.fusionZStar ↥L))
    {l₁ l₂ : G} (hl₁ : l₁ ∈ L) (hl₂ : l₂ ∈ L) (hl₁2 : l₁ * l₁ = 1) (hl₂2 : l₂ * l₂ = 1)
    (hl₁Z : l₁ ∉ zStarIn L) (hl₂Z : l₂ ∉ zStarIn L) :
    ∃ g ∈ L, l₂⁻¹ * (g⁻¹ * l₁ * g) ∈ zStarIn L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπ, hker, -⟩ := exists_quotient_psl34 h
  set f := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hf
  set ψ : ↥L →* PSL3Four.S := π.comp f with hψ
  have hψsurj : Function.Surjective ψ := hπ.comp (QuotientGroup.mk'_surjective _)
  have hψZ : ∀ x : ↥L, ψ x = 1 ↔ (x : G) ∈ zStarIn L := by
    intro x
    rw [hψ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker]
    constructor
    · intro hx
      refine ⟨x, ?_, rfl⟩
      rw [Sol78.fusionZStar_eq_comap]
      exact hx
    · rintro ⟨x', hx', hxx'⟩
      have : x' = x := Subtype.ext hxx'
      subst this
      rw [Sol78.fusionZStar_eq_comap] at hx'
      exact hx'
  set a : ↥L := ⟨l₁, hl₁⟩ with ha
  set b : ↥L := ⟨l₂, hl₂⟩ with hb
  have hψa1 : ψ a ≠ 1 := fun h1 => hl₁Z ((hψZ a).mp h1)
  have hψb1 : ψ b ≠ 1 := fun h1 => hl₂Z ((hψZ b).mp h1)
  have hψa2 : ψ a * ψ a = 1 := by
    rw [← map_mul, show a * a = 1 from Subtype.ext hl₁2, map_one]
  have hψb2 : ψ b * ψ b = 1 := by
    rw [← map_mul, show b * b = 1 from Subtype.ext hl₂2, map_one]
  obtain ⟨y, hyS, hy⟩ := CatFactsL4U4.conj_of_mul_mem_S (PSL3Four.S_le_R (ψ b).2)
    (PSL3Four.S_le_R (ψ a).2) (congrArg Subtype.val hψb2) (congrArg Subtype.val hψa2)
    (fun h1 => hψb1 (Subtype.ext h1)) (fun h1 => hψa1 (Subtype.ext h1))
    (mul_mem (inv_mem (ψ b).2) (ψ a).2)
  set s : PSL3Four.S := ⟨y, hyS⟩ with hs
  have hsl : s * ψ b * s⁻¹ = ψ a := Subtype.ext hy
  obtain ⟨g, hg⟩ := hψsurj s
  refine ⟨g, g.2, ?_⟩
  have h1 : ψ (b⁻¹ * (g⁻¹ * a * g)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hg, ← hsl]
    group
  exact (hψZ _).mp h1

theorem exists_conj_mem_center_of_involution
    {L S : Subgroup G}
    (htype : IsL34Type (↥L ⧸ Open.fusionZStar ↥L)) (hS₀ : IsSylowTwoIn (S ⊓ L) L)
    (hexp : ∀ z ∈ S ⊓ L ⊓ zStarIn L, z * z = 1)
    (hZc : ∀ z ∈ S ⊓ L ⊓ zStarIn L, ∀ s ∈ S, s * z = z * s)
    {y₀ : G} (hy₀S : y₀ ∈ S) (hy₀L : y₀ ∈ L) (hy₀Z : y₀ ∉ zStarIn L) (hy₀2 : y₀ * y₀ = 1)
    (hy₀c : ∀ s ∈ S, s * y₀ = y₀ * s) {h : G} (hhL : h ∈ L) (hh2 : h * h = 1)
    (hhZ : h ∉ zStarIn L) :
    ∃ l ∈ L, l⁻¹ * h * l ∈ S ∧ ∀ s ∈ S, s * (l⁻¹ * h * l) = l⁻¹ * h * l * s := by
  obtain ⟨g, hgL, hg⟩ := exists_conj_inv_mul_mem_zStarIn htype hhL hy₀L hh2 hy₀2 hhZ hy₀Z
  have hx2 : g⁻¹ * h * g * (g⁻¹ * h * g) = 1 := by
    rw [show g⁻¹ * h * g * (g⁻¹ * h * g) = g⁻¹ * (h * h) * g by group, hh2, mul_one,
      inv_mul_cancel]
  have hw := GrS4.zStarIn_le_oddIn_sup hS₀ hg
  rw [sup_comm] at hw
  have hle : S ⊓ L ⊓ zStarIn L ≤ normalizer (oddIn L : Set G) := fun y hy =>
    normalizer_le_normalizer_oddIn L (le_normalizer (mem_inf.mp (mem_inf.mp hy).1).2)
  have hw' : y₀⁻¹ * (g⁻¹ * h * g) ∈ ((S ⊓ L ⊓ zStarIn L ⊔ oddIn L : Subgroup G) : Set G) := hw
  rw [coe_mul_of_left_le_normalizer_right _ _ hle] at hw'
  obtain ⟨z, hz, o, ho, hzo⟩ := hw'
  have hzo' : z * o = y₀⁻¹ * (g⁻¹ * h * g) := hzo
  have hzS : z ∈ S := (mem_inf.mp (mem_inf.mp hz).1).1
  have hz2 : z * z = 1 := hexp z hz
  have hzc : ∀ s ∈ S, s * z = z * s := hZc z hz
  have hzy₀ : y₀ * z = z * y₀ := hzc y₀ hy₀S
  have hy2 : y₀ * z * (y₀ * z) = 1 := by
    calc y₀ * z * (y₀ * z) = y₀ * (z * y₀) * z := by group
      _ = y₀ * (y₀ * z) * z := by rw [hzy₀]
      _ = (y₀ * y₀) * (z * z) := by group
      _ = 1 := by rw [hy₀2, hz2, one_mul]
  have hx' : g⁻¹ * h * g = y₀ * (z * o) := by
    rw [hzo']
    group
  have hyx : y₀ * z * (g⁻¹ * h * g) = o := by
    rw [hx']
    calc y₀ * z * (y₀ * (z * o)) = y₀ * (z * y₀) * z * o := by group
      _ = y₀ * (y₀ * z) * z * o := by rw [hzy₀]
      _ = (y₀ * y₀) * (z * z) * o := by group
      _ = o := by rw [hy₀2, hz2, one_mul, one_mul]
  have hodd : Odd (orderOf (y₀ * z * (g⁻¹ * h * g))) := by
    rw [hyx]
    have h1 : orderOf o ∣ Nat.card (oddIn L) := by
      have := orderOf_dvd_natCard (⟨o, ho⟩ : oddIn L)
      rwa [Subgroup.orderOf_mk] at this
    have hoddL : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact hoddL.of_dvd_nat h1
  obtain ⟨c, hc, hcx⟩ := exists_conj_eq_of_odd_orderOf hy2 hx2 hodd
  rw [hyx] at hc
  have hcL : c ∈ L := map_subtype_le _ ((zpowers_le.mpr ho) hc)
  have e : (g * c⁻¹)⁻¹ * h * (g * c⁻¹) = y₀ * z := by
    rw [show (g * c⁻¹)⁻¹ * h * (g * c⁻¹) = c * (g⁻¹ * h * g) * c⁻¹ by group, ← hcx]
    group
  refine ⟨g * c⁻¹, mul_mem hgL (inv_mem hcL), ?_, fun s hs => ?_⟩
  · rw [e]
    exact mul_mem hy₀S hzS
  · rw [e]
    calc s * (y₀ * z) = (s * y₀) * z := by group
      _ = y₀ * (s * z) := by rw [hy₀c s hs]; group
      _ = y₀ * (z * s) := by rw [hzc s hs]
      _ = y₀ * z * s := by group

theorem exists_conj_mem_center_of_le_center
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hLift : L34SylowCentralLiftFact) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) (hexp : ∀ y ∈ S ⊓ coreActionKernel L ⊓ L, y * y = 1)
    (hZc : ∀ y ∈ S ⊓ coreActionKernel L ⊓ L, ∀ s ∈ S, s * y = y * s) :
    ∀ u ∈ L34UnbalancingSet L t S, ∃ l ∈ L, l⁻¹ * u * l ∈ S ∧
      ∀ s ∈ S, s * (l⁻¹ * u * l) = l⁻¹ * u * l * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  obtain ⟨-, hfam, -, hSyl, htS, -, -⟩ := hset
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, htype, -, -, -⟩ := hfam
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have hZL : zStarIn L ≤ L := map_subtype_le _
  have hZsub : ∀ y ∈ S ⊓ L ⊓ zStarIn L, y ∈ S ⊓ coreActionKernel L ⊓ L := fun y hy =>
    mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hy).1).1,
      zStarIn_le_coreActionKernel L (mem_inf.mp hy).2⟩, (mem_inf.mp (mem_inf.mp hy).1).2⟩
  obtain ⟨y₀, hy₀SL, hy₀Z, hy₀2, hy₀c⟩ := hLift G L S hperf htype hSyl fun z hz =>
    hexp z (hZsub z (mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hz).1, hZL (mem_inf.mp hz).2⟩,
      (mem_inf.mp hz).2⟩))
  intro u hu
  obtain ⟨huS₀, hu2, -⟩ := hu
  have htc : ∀ y ∈ S ⊓ L, t * y = y * t := fun y hy => (hZS y (mem_inf.mp hy).1).symm
  rw [sup_comm] at huS₀
  obtain ⟨i, h, hh, rfl⟩ := mem_zpowers_sup htc huS₀
  have hhS : h ∈ S := (mem_inf.mp hh).1
  have hhL : h ∈ L := (mem_inf.mp hh).2
  have hti : ∀ s ∈ S, s * t ^ i = t ^ i * s := fun s hs => (Commute.zpow_right (hZS s hs) i).eq
  have key : ∀ l ∈ L, l⁻¹ * h * l ∈ S → (∀ s ∈ S, s * (l⁻¹ * h * l) = l⁻¹ * h * l * s) →
      ∃ l ∈ L, l⁻¹ * (t ^ i * h) * l ∈ S ∧
        ∀ s ∈ S, s * (l⁻¹ * (t ^ i * h) * l) = l⁻¹ * (t ^ i * h) * l * s := by
    intro l hl hlS hlc
    have hlt : Commute l⁻¹ (t ^ i) :=
      (Commute.zpow_right (mem_centralizer_singleton_iff.mp (hLt hl)) i).inv_left
    have e : l⁻¹ * (t ^ i * h) * l = t ^ i * (l⁻¹ * h * l) := by
      calc l⁻¹ * (t ^ i * h) * l = (l⁻¹ * t ^ i) * h * l := by group
        _ = (t ^ i * l⁻¹) * h * l := by rw [hlt.eq]
        _ = t ^ i * (l⁻¹ * h * l) := by group
    refine ⟨l, hl, ?_, fun s hs => ?_⟩
    · rw [e]
      exact mul_mem (zpow_mem htS i) hlS
    · rw [e]
      calc s * (t ^ i * (l⁻¹ * h * l)) = (s * t ^ i) * (l⁻¹ * h * l) := by group
        _ = t ^ i * (s * (l⁻¹ * h * l)) := by rw [hti s hs]; group
        _ = t ^ i * (l⁻¹ * h * l * s) := by rw [hlc s hs]
        _ = t ^ i * (l⁻¹ * h * l) * s := by group
  by_cases hhZ : h ∈ zStarIn L
  · have hhQ := hZsub h (mem_inf.mpr ⟨hh, hhZ⟩)
    exact key 1 (one_mem _) (by simpa using hhS) fun s hs => by simpa using hZc h hhQ s hs
  · have hh2 : h * h = 1 := by
      have hu' : t ^ i * h * (t ^ i * h) = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
      have ht2i : t ^ i * t ^ i = 1 := by
        rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ht2, one_zpow]
      calc h * h = (t ^ i * t ^ i) * (h * h) := by rw [ht2i, one_mul]
        _ = t ^ i * (t ^ i * h) * h := by group
        _ = t ^ i * (h * t ^ i) * h := by rw [hti h hhS]
        _ = t ^ i * h * (t ^ i * h) := by group
        _ = 1 := hu'
    obtain ⟨l, hl, hlS, hlc⟩ := exists_conj_mem_center_of_involution htype hS₀
      (fun z hz => hexp z (hZsub z hz)) (fun z hz => hZc z (hZsub z hz))
      (mem_inf.mp hy₀SL).1 (mem_inf.mp hy₀SL).2 hy₀Z hy₀2 hy₀c hhL hh2 hhZ
    exact key l hl hlS hlc

theorem exists_central_unbalancing_of_facts
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hLift : L34SylowCentralLiftFact)
    (hCen : L34Lemma510CentralStep) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) {u : G} (hu : u ∈ L34UnbalancingSet L t S)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) :
    ∃ u' ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u' = u' * s) ∧
      ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
        Nat.card ↥(oddIn L ⊓ centralizer ({u'} : Set G)) := by
  have hexp : ∀ y ∈ S ⊓ coreActionKernel L ⊓ L, y * y = 1 := by
    by_cases hZ : S ⊓ coreActionKernel L ⊓ L = ⊥
    · intro y hy
      rw [hZ, mem_bot] at hy
      rw [hy, one_mul]
    · exact ((h58 G L t S T hset).2 hZ).2
  obtain ⟨z, hz, hzt, hΩ, -, -⟩ := h59 G L t S T hset
  by_cases hZc : ∀ y ∈ S ⊓ coreActionKernel L ⊓ L, ∀ s ∈ S, s * y = y * s
  · exact exists_central_unbalancing hS hU hheld hSol hGW hset
      (exists_conj_mem_center_of_le_center hS hU hheld hSol hGW hLift hset hexp hZc) hu hmax
  · push Not at hZc
    exact hCen G L t S T hset hexp ⟨z, hz, hzt, hΩ⟩ hZc u hu hmax

end CFSG.ComponentClassification.GrSLit.GrS5
