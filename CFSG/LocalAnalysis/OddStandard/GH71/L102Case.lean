module

public import CFSG.LocalAnalysis.OddStandard.GH71.HBarCent2
public import CFSG.LocalAnalysis.OddStandard.GH71.Thompson
public import CFSG.LocalAnalysis.OddStandard.GH71.TwoOnThree
public import CFSG.LocalAnalysis.OddStandard.GH71.CUFacts

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem bar_mem_zpowers {H : Subgroup G} {z : G} (hzH : z ∈ H) {w : G}
    (hw : w ∈ pPrimeCoreOf 2 H ⊔ zpowers z) (hwH : w ∈ H) :
    QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨w, hwH⟩ ∈
      zpowers (QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨z, hzH⟩) := by
  have hzN : zpowers z ≤ normalizer (pPrimeCoreOf 2 H : Set G) :=
    (zpowers_le.mpr hzH).trans (le_normalizer_pPrimeCoreOf' H)
  have hw' : w ∈ ((pPrimeCoreOf 2 H ⊔ zpowers z : Subgroup G) : Set G) := hw
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzN] at hw'
  obtain ⟨o, ⟨o', ho', rfl⟩, t, ht, rfl⟩ := hw'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ht
  refine ⟨k, ?_⟩
  show QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨z, hzH⟩ ^ k =
    QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨(o' : G) * z ^ k, hwH⟩
  have e : (⟨(o' : G) * z ^ k, hwH⟩ : ↥H) = o' * ⟨z, hzH⟩ ^ k := Subtype.ext (by simp)
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥H) o' = 1 := (QuotientGroup.eq_one_iff _).mpr ho'
  rw [e, map_mul, h1, one_mul, map_zpow]

omit [Finite G] in
theorem le_of_isPGroup_three_of_le_sup {H W : Subgroup G} {z : G} (hzH : z ∈ H) (hz2 : z * z = 1)
    (hWH : W ≤ H) (hW3 : IsPGroup 3 ↥W) (hle : W ≤ pPrimeCoreOf 2 H ⊔ zpowers z) :
    W ≤ pPrimeCoreOf 2 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← IVK812.barIn_eq_bot_iff hWH]
  have hsub : barIn H W ≤ zpowers (QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨z, hzH⟩) := by
    rintro _ ⟨⟨w, hwH⟩, hw, rfl⟩
    exact bar_mem_zpowers hzH (hle (Subgroup.mem_subgroupOf.mp hw)) hwH
  have hdvd : Nat.card (barIn H W) ∣ 2 := by
    refine (card_dvd_of_le hsub).trans ?_
    rw [Nat.card_zpowers]
    refine orderOf_dvd_of_pow_eq_one ?_
    have hz1 : (⟨z, hzH⟩ * ⟨z, hzH⟩ : ↥H) = 1 := Subtype.ext hz2
    rw [pow_two, ← map_mul, hz1, map_one]
  rcases (IVK812.isPGroup_barIn hW3).card_eq_or_dvd with h1 | h3
  · exact card_eq_one.mp h1
  · exact absurd (h3.trans hdvd) (by norm_num)

variable {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem case_split_102 (h : Ctx71 G z S U u) (hB5 : SpecB5)
    {H P Q P₁ : Subgroup G} (hSH : S ≤ H) (hcov : Covers H (Cen z) (pPrimeCoreOf 2 (Cen z)))
    (hbar : IsDoubleCoverOfAlt (HBar H) 11 ∨ Blueprint.NativeSporadic.IsSporadic (HBar H) .Ly)
    (hP : MaxSInv 3 S H P) (hQ : P ⊓ pPrimeCoreOf 2 H = Q) (hHQ : H ≤ normalizer (Q : Set G))
    (hP₁Q : P₁ ≤ Q) (hP₁S : ¬ S ≤ centralizer (P₁ : Set G)) :
    Covers (normalizer (zIn P : Set G)) (Cen z) (pPrimeCoreOf 2 (Cen z)) ∨
      H ⊓ centralizer (zIn Q : Set G) ≤ pPrimeCoreOf 2 H ⊔ zpowers z := by
  have hzH : z ∈ H := hSH h.ctx.z_mem
  have hQP : Q ≤ P := by rw [← hQ]; exact inf_le_left
  have hS_of_cov : ∀ L : Subgroup G, H ≤ normalizer (L : Set G) →
      Covers L H (pPrimeCoreOf 2 H) → S ≤ L := by
    intro L hHL hc
    have hc' : H ≤ (L ⊓ H) ⊔ pPrimeCoreOf 2 H := hc
    exact le_of_isPGroup_two_of_odd_index h.S2 (hSH.trans hHL) ((pPrimeCoreOf_le' H).trans hHL)
      (hSH.trans (hc'.trans (sup_le_sup_right inf_le_left _))) (odd_card_pPrimeCoreOf' H)
  have hCQ : H ⊓ centralizer (Q : Set G) ≤ pPrimeCoreOf 2 H ⊔ zpowers z := by
    have hHn : H ≤ normalizer ((H ⊓ centralizer (Q : Set G) : Subgroup G) : Set G) := fun x hx =>
      inf_normalizer_le_normalizer_inf
        ⟨le_normalizer hx, normalizer_le_normalizer_centralizer Q (hHQ hx)⟩
    rcases h.normal_dichotomy hB5 hSH hbar inf_le_left hHn with hle | hc
    · exact hle
    · exact absurd ((hS_of_cov _ hHn hc).trans (inf_le_right.trans (centralizer_le hP₁Q))) hP₁S
  have hZQ : zIn P ≤ centralizer (Q : Set G) := inf_le_right.trans (centralizer_le hQP)
  have hZP : zIn P ≤ Q := by
    have h1 : zIn P ≤ H ⊓ centralizer (Q : Set G) := le_inf ((zIn_le P).trans hP.1) hZQ
    have h2 : zIn P ≤ pPrimeCoreOf 2 H :=
      le_of_isPGroup_three_of_le_sup hzH (h.sq_eq_one_of_mem_U h.z_mem) ((zIn_le P).trans hP.1)
        (hP.2.1.to_le (zIn_le P)) (h1.trans hCQ)
    rw [← hQ]; exact le_inf (zIn_le P) h2
  have hZE : zIn P ≤ zIn Q := le_inf hZP hZQ
  have hHE : H ≤ normalizer (zIn Q : Set G) := hHQ.trans (normalizer_le_normalizer_zIn Q)
  have hHL : H ≤ normalizer ((H ⊓ centralizer (zIn Q : Set G) : Subgroup G) : Set G) :=
    fun x hx => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer hx, normalizer_le_normalizer_centralizer _ (hHE hx)⟩
  rcases h.normal_dichotomy hB5 hSH hbar inf_le_left hHL with hle | hc
  · exact Or.inr hle
  · left
    have hSL := hS_of_cov _ hHL hc
    have hz2 : IsPGroup 2 ↥(zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_z, pow_one])
    have hNz := normalizer_zpowers_eq_centralizer h.orderOf_z
    have hcovL := covers_transfer hz2 (zpowers_le.mpr hzH) (zpowers_le.mpr (hSL h.ctx.z_mem))
      (by rw [hNz]; exact hcov) hc
    rw [hNz] at hcovL
    refine covers_mono ?_ hcovL
    exact inf_le_right.trans ((centralizer_le hZE).trans (Ctx71.centralizer_le_normalizer' _))

end Ctx71

end CFSG.OddStandard.GH71
