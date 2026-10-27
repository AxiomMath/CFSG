module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma55
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs58
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32Tools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem exists_normalizer_not_mem_of_lt_two {S T : Subgroup G} (hT : IsPGroup 2 T)
    (hST : S < T) : ∃ x ∈ T, x ∉ S ∧ x ∈ normalizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hlt : S.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hST.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : T) ∈ S.subgroupOf T := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := T) _ hlt)
  refine ⟨y, y.2, fun h => hyS (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (S : Set G)).subgroupOf T := by
    rw [subgroupOf_normalizer_eq hST.le]
    exact hyN
  exact mem_subgroupOf.mp hy

theorem eq_zpowers_of_omegaOne_eq
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (h56 : L34Lemma56) (hAut : L34AutRankOneNormalFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    (hΩ : omegaOne (S ⊓ coreActionKernel L) = zpowers t) :
    S ⊓ coreActionKernel L = zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := S ⊓ coreActionKernel L with hQ
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hset' := hset
  obtain ⟨-, hfam, -, hSyl, -, hST, hTsyl⟩ := hset'
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, htype, -, -, -⟩ := hfam
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have htQ : t ∈ Q := omegaOne_le Q (hΩ ▸ mem_zpowers t)
  have hinv : ∀ s ∈ Q, s * s = 1 → s = 1 ∨ s = t := by
    intro s hs hs2
    have hsΩ : s ∈ omegaOne Q := subset_closure ⟨hs, hs2⟩
    rw [hΩ] at hsΩ
    exact eq_one_or_eq_of_mem_zpowers' ht2 hsΩ
  have hSneT : S ≠ T := fun h => h56 G L t S T hset (h ▸ hTsyl)
  obtain ⟨r, hrT, hrS, hrN⟩ :=
    exists_normalizer_not_mem_of_lt_two (IsSylowTwoIn.isPGroup hTsyl)
      (lt_of_le_of_ne hST hSneT)
  have hSN : S ≤ normalizer (L : Set G) := hSyl.1
  have hQS : S ≤ normalizer (Q : Set G) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hq).1) (inv_mem hs),
        FooteLit.conj_mem_coreActionKernel (hSN hs) (mem_inf.mp hq).2⟩
    · intro hq
      have h1 : s⁻¹ * (s * q * s⁻¹) * s⁻¹⁻¹ ∈ Q :=
        mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hs) (mem_inf.mp hq).1) (inv_mem (inv_mem hs)),
          FooteLit.conj_mem_coreActionKernel (inv_mem (hSN hs)) (mem_inf.mp hq).2⟩
      rwa [show s⁻¹ * (s * q * s⁻¹) * s⁻¹⁻¹ = q by group] at h1
  set D := conjugate Q r with hD
  have hDS : D ≤ S := by
    intro d hd
    rw [mem_conjugate_iff] at hd
    have h1 := (mem_normalizer_iff.mp (inv_mem hrN) _).mp (mem_inf.mp hd).1
    rwa [show r⁻¹ * (r * d * r⁻¹) * r⁻¹⁻¹ = d by group] at h1
  have hDn : S ≤ normalizer (D : Set G) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro d
    rw [mem_conjugate_iff, mem_conjugate_iff]
    have hs' : r * s * r⁻¹ ∈ S := (mem_normalizer_iff.mp hrN s).mp hs
    rw [show r * (s * d * s⁻¹) * r⁻¹ = (r * s * r⁻¹) * (r * d * r⁻¹) * (r * s * r⁻¹)⁻¹ by
      group]
    exact (mem_normalizer_iff.mp (hQS hs') _)
  have hDinv : ∀ d ∈ D, d * d = 1 → d ≠ 1 → r * d * r⁻¹ = t := by
    intro d hd hd2 hd1
    rw [mem_conjugate_iff] at hd
    have h2 : r * d * r⁻¹ * (r * d * r⁻¹) = 1 := by
      rw [show r * d * r⁻¹ * (r * d * r⁻¹) = r * (d * d) * r⁻¹ by group, hd2]
      group
    rcases hinv _ hd h2 with h | h
    · exact absurd (by rw [show d = r⁻¹ * (r * d * r⁻¹) * r by group, h]; group) hd1
    · exact h
  have hDQ : D ⊓ coreActionKernel L = ⊥ := by
    by_contra hne
    have h2 : IsPGroup 2 ↥(D ⊓ coreActionKernel L) :=
      (IsSylowTwoIn.isPGroup hSyl).to_le (inf_le_left.trans hDS)
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥(D ⊓ coreActionKernel L)) 2
      (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hsD : (s : G) ∈ D := (mem_inf.mp s.2).1
    have hs2 : (s : G) * s = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hs, pow_two] at h
      exact congrArg Subtype.val h
    have hs1 : (s : G) ≠ 1 := by
      intro h
      have h1 : s = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hs
      exact absurd hs (by norm_num)
    have hsQ : (s : G) ∈ Q := mem_inf.mpr ⟨hDS hsD, (mem_inf.mp s.2).2⟩
    have hst : (s : G) = t := (hinv _ hsQ hs2).resolve_left hs1
    have hrt : r * t * r⁻¹ = t := hst ▸ hDinv _ hsD hs2 hs1
    have hrC : r ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc r * t = r * t * r⁻¹ * r := by group
        _ = t * r := by rw [hrt]
    have hrL : r ∈ normalizer (L : Set G) := hCN hrC
    have hSr : S ⊔ zpowers r ≤ normalizer (L : Set G) := sup_le hSN (zpowers_le.mpr hrL)
    have hSr2 : IsPGroup 2 ↥(S ⊔ zpowers r) :=
      (IsSylowTwoIn.isPGroup hTsyl).to_le (sup_le hST (zpowers_le.mpr hrT))
    have heq := IsSylowTwoIn.eq_of_le hSyl le_sup_left hSr hSr2
    exact hrS (heq ▸ mem_sup_right (mem_zpowers r))
  have hD1 : ∀ d ∈ D, ∀ e ∈ D, d * d = 1 → e * e = 1 → d = 1 ∨ e = 1 ∨ d = e := by
    intro d hd e he hd2 he2
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    by_cases he1 : e = 1
    · exact Or.inr (Or.inl he1)
    right; right
    have h1 := hDinv d hd hd2 hd1
    have h2 := hDinv e he he2 he1
    calc d = r⁻¹ * (r * d * r⁻¹) * r := by group
      _ = r⁻¹ * (r * e * r⁻¹) * r := by rw [h1, h2]
      _ = e := by group
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hcard := hAut G L S D hperf htype hSyl hDS hDn hDQ hD1
  have hcardQ : Nat.card Q ≤ 2 := by
    rwa [hD, conjugate, card_map_of_injective (MulAut.conj r⁻¹).injective] at hcard
  symm
  refine eq_of_le_of_card_ge (zpowers_le.mpr htQ) ?_
  rwa [Nat.card_zpowers, hto]

end CFSG.ComponentClassification.GrSLit.GrS5
