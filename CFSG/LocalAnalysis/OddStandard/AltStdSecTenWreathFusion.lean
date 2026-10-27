module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathInnerTable
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathOuter
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathPair
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathQuotCent
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathDiag

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G} {x : G}

theorem mk_conj_notMem_normalizer (hC : CentData z ι) (hN : NoSwapConj z ι) (hx : x = ι τ₀)
    (hO : CFSG.oddCore (TwoSec x) = ⊥) {K : Subgroup (TwoSec x)}
    (hE : ExactShape (zbar hC hx) (diagSub (ι := ι) hx) 8)
    (hK : WreathK (zbar hC hx) (diagSub (ι := ι) hx) K) (g : G)
    (hg : g⁻¹ * z * g ∈ centralizer ({x} : Set G)) :
    (QuotientGroup.mk ⟨g⁻¹ * z * g, hg⟩ : TwoSec x) ∉ normalizer (K : Set (TwoSec x)) ∧
      pairOrder (g⁻¹ * z * g) x = N10 1 := by
  have hx2 : x * x = 1 := by rw [hx, ← map_mul, τ₀_mul_self, map_one]
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : ι τ₀ = 1 := by rw [← hx]; exact h1
    have h3 : τ₀ = 1 := hC.inj (by rw [h2, map_one])
    exact absurd h3 (by decide)
  have hxz : ¬ IsConj z x := by rw [hx]; exact (hN τ₀ isSwap_τ₀).1
  have hc2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    rw [show (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, hC.mul_self]
    group
  have hcsub : (⟨g⁻¹ * z * g, hg⟩ : ↥(centralizer ({x} : Set G))) * ⟨g⁻¹ * z * g, hg⟩ = 1 :=
    Subtype.ext hc2
  have hcbar2 : (QuotientGroup.mk ⟨g⁻¹ * z * g, hg⟩ : TwoSec x) *
      (QuotientGroup.mk ⟨g⁻¹ * z * g, hg⟩ : TwoSec x) = 1 := by
    rw [← QuotientGroup.mk_mul, hcsub, QuotientGroup.mk_one]
  have hcbar1 : (QuotientGroup.mk ⟨g⁻¹ * z * g, hg⟩ : TwoSec x) ≠ 1 := by
    intro h1
    have hmem : (⟨g⁻¹ * z * g, hg⟩ : ↥(centralizer ({x} : Set G))) ∈ zpowers (selfC x) :=
      (QuotientGroup.eq_one_iff _).1 h1
    rcases (mem_zpowers_selfC_iff hx2).1 hmem with h2 | h2
    · have hc_eq : g⁻¹ * z * g = 1 := h2
      have hz1 : z = 1 := by
        calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
          _ = g * 1 * g⁻¹ := by rw [hc_eq]
          _ = 1 := by group
      have hord := hC.order
      rw [hz1, orderOf_one] at hord
      exact absurd hord (by decide)
    · have hc_eq : g⁻¹ * z * g = x := h2
      exact hxz (isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]; exact hc_eq⟩)
  obtain ⟨σ, _, _, hk1, hk5, _, hpair⟩ := exists_perm_of_conj_mem hC hx2 hx1 hxz g hg
  have hpairP : Nat.card ↥(centralizer ({g⁻¹ * z * g} : Set G) ⊓
      centralizer ({x} : Set G)) = N10 (Multiset.card σ.cycleType) := hpair
  have hcase := card_centralizer_mk_cases hx2 hx1 hg
  have hnot : (QuotientGroup.mk ⟨g⁻¹ * z * g, hg⟩ : TwoSec x) ∉
      normalizer (K : Set (TwoSec x)) := by
    intro hmem
    obtain ⟨c₁, c₂, j, hcard, hc₁, hc₂, hn, hj⟩ :=
      WreathK.card_centralizer_inner hE hK hO hmem hcbar2 hcbar1
    have hNmem : N10 (Multiset.card σ.cycleType) ∈
        ({161280, 11520, 2304, 1536, 7680} : Finset ℕ) := N10_mem hk1 hk5
    rcases hcase with hcase | hcase
    · refine false_of_card_centralizer_arith hc₁ hc₂ hn hj (Or.inr rfl) ?_
      rw [show c₁ * c₂ * 2 ^ j * 2 = 2 * Nat.card ↥(centralizer
          ({(QuotientGroup.mk ⟨g⁻¹ * z * g, hg⟩ : TwoSec x)} : Set (TwoSec x))) by
        rw [← hcard]; exact mul_comm _ 2,
        hcase, hpairP]
      exact hNmem
    · refine false_of_card_centralizer_arith hc₁ hc₂ hn hj (Or.inl rfl) ?_
      rw [show c₁ * c₂ * 2 ^ j * 1 = Nat.card ↥(centralizer
          ({(QuotientGroup.mk ⟨g⁻¹ * z * g, hg⟩ : TwoSec x)} : Set (TwoSec x))) by
        rw [← hcard]; exact mul_one _,
        hcase, hpairP]
      exact hNmem
  refine ⟨hnot, ?_⟩
  have hseven : 7 ∣ Nat.card ↥(centralizer
      ({(QuotientGroup.mk ⟨g⁻¹ * z * g, hg⟩ : TwoSec x)} : Set (TwoSec x))) :=
    WreathK.seven_dvd_card_centralizer_outer hK hcbar2 hnot
  have hdvdP : 7 ∣ Nat.card ↥(centralizer ({g⁻¹ * z * g} : Set G) ⊓
      centralizer ({x} : Set G)) := by
    rcases hcase with hcase | hcase
    · exact hcase ▸ hseven.mul_left 2
    · exact hcase ▸ hseven
  have hdvd : 7 ∣ N10 (Multiset.card σ.cycleType) := by
    rw [← hpairP]; exact hdvdP
  change Nat.card ↥(centralizer ({g⁻¹ * z * g} : Set G) ⊓ centralizer ({x} : Set G)) = N10 1
  rw [hpairP, eq_one_of_seven_dvd_N10 hk1 hk5 hdvd]

end CFSG.OddStandard.AltStdSec.SwapPattern
