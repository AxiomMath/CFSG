module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix
import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneTools
import CFSG.LocalAnalysis.ComponentClassification.FooteLitInitial
import CFSG.LocalAnalysis.ComponentClassification.FooteLitStep
import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem not_le_coreActionKernel_of_sup_oddCoreIn_eq {e : G} {K T : Subgroup G}
    (hK : IsTwoComponentAt e K) (hsup : T ⊔ oddCoreIn K = K) : ¬ T ≤ coreActionKernel K := by
  intro hT
  obtain ⟨-, hKC, hKc⟩ := hK
  obtain ⟨x, y, hxy⟩ := exists_mul_ne_mul_of_isQuasisimple
    (isQuasisimple_quotient_of_isPComponent hKC hKc)
  have hKK : K ≤ coreActionKernel K :=
    hsup.symm.le.trans (sup_le hT (GSThmB.oddCoreIn_le_coreActionKernel K))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  apply hxy
  obtain ⟨o, ho, hoeq⟩ := (mem_coreActionKernel.mp (hKK x.2)).2 y y.2
  have hc : y⁻¹ * x⁻¹ * y * x ∈ pPrimeCore 2 K := by
    have : o = y⁻¹ * x⁻¹ * y * x := Subtype.ext (by simpa using hoeq)
    rw [← this]
    exact ho
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  simpa [mul_assoc] using hc

theorem mem_normalizer_of_not_le_coreActionKernel {e g : G} {K T : Subgroup G}
    (hK : IsTwoComponentAt e K) (hTK : T ≤ K) (hT : ¬ T ≤ coreActionKernel K)
    (hge : g ∈ centralizer ({e} : Set G)) (hgT : g ∈ normalizer (T : Set G)) :
    g ∈ normalizer (K : Set G) := by
  obtain ⟨-, hKC, hKc⟩ := hK
  by_contra hgK
  have hle : conjugate K g ≤ coreActionKernel K :=
    GSThmB.B5a.le_coreActionKernel_of_ne hKC (conjugate_le_of_mem hKC hge) hKc
      (isPComponent_conjugate_subgroupOf hge hKc)
      (fun h => hgK (mem_normalizer_of_conjugate_eq h.symm))
  refine hT fun t ht => hle ?_
  have h1 := conj_mem_conjugate (hTK ((mem_normalizer_iff.mp hgT t).mp ht)) g
  rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h1

theorem inf_centralizer_le_normalizer_of_mem {e v : G} {K : Subgroup G}
    (hK : IsTwoComponentAt e K) (hZ : center (K ⧸ pPrimeCore 2 K) = ⊥) (hvK : v ∈ K)
    (hv : orderOf v = 2) :
    centralizer ({e} : Set G) ⊓ centralizer ({v} : Set G) ≤ normalizer (K : Set G) := by
  intro g hg
  obtain ⟨hge, hgv⟩ := mem_inf.mp hg
  obtain ⟨-, hKC, hKc⟩ := hK
  by_contra hgK
  have hle : conjugate K g ≤ coreActionKernel K :=
    GSThmB.B5a.le_coreActionKernel_of_ne hKC (conjugate_le_of_mem hKC hge) hKc
      (isPComponent_conjugate_subgroupOf hge hKc)
      (fun h => hgK (mem_normalizer_of_conjugate_eq h.symm))
  have h1 := conj_mem_conjugate hvK g
  rw [show g⁻¹ * v * g = v by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hgv, inv_mul_cancel_left]] at h1
  exact center_ne_bot_of_mem_coreActionKernel hvK hv (hle h1) hZ

theorem inf_centralizer_le_normalizer_of_odd {e : G} {K X : Subgroup G}
    (hK : IsTwoComponentAt e K) (hXodd : Odd (Nat.card X)) (hKX : K ≤ normalizer (X : Set G)) :
    X ⊓ centralizer ({e} : Set G) ≤ normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hKC, hKc⟩ := hK
  set D := X ⊓ centralizer ({e} : Set G) with hD
  set H := K ⊔ D with hH
  have hHC : H ≤ centralizer ({e} : Set G) := sup_le hKC inf_le_right
  have hHD : H ≤ normalizer (D : Set G) := sup_le
    (fun k hk => mem_normalizer_inf' (hKX hk) (le_normalizer (hKC hk)))
    le_normalizer
  have hDn : (D.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hHD
  have hDodd : Odd (Nat.card (D.subgroupOf H)) := by
    refine Odd.of_dvd_nat hXodd ?_
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_dvd_of_le (by
      rintro _ ⟨n, hn, rfl⟩
      exact (mem_inf.mp hn).1)
  have hDO : D.subgroupOf H ≤ pPrimeCore 2 H := le_sSup ⟨hDn, Nat.coprime_two_left.mpr hDodd⟩
  have hON := UnbalancedLayer.pPrimeCore_le_normalizer
    (GSThmB.B5a.isPComponent_subgroupOf_of_le le_sup_left hHC hKc)
  intro g hg
  have hgH : g ∈ H := mem_sup_right hg
  have hgN := hON (hDO (show (⟨g, hgH⟩ : H) ∈ D.subgroupOf H from hg))
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact (mem_normalizer_iff.mp hgN ⟨x, mem_sup_left hx⟩).mp hx
  · intro hx
    have hxH : x ∈ H := by
      have h1 := mul_mem (mul_mem (inv_mem hgH) (mem_sup_left hx : g * x * g⁻¹ ∈ H)) hgH
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
    exact (mem_normalizer_iff.mp hgN ⟨x, hxH⟩).mpr hx

end CFSG.ComponentClassification.FooteLit
