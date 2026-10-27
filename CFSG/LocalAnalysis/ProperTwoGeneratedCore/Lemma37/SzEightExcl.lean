module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightExclBase
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightExclCover
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleSplit

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace SzEightExclSetting

variable (hs : SzEightExclSetting S H z J) [J.Normal]
  (e : (J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1))
include hs e

theorem false_of_forall_centralizer
    (hγ : ∀ k ∈ escapingSylowImage S z, k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) →
      k = 1 ∨ k = escapingBar z) : False := by
  have hz := hs.central
  obtain ⟨φ, hφ⟩ := hs.exists_isInnerPart e
  obtain ⟨v, hvS, hvz⟩ := hs.square.square
  obtain ⟨q, hqJ, -, hk⟩ := hφ.exists_mul ⟨v, hvS⟩
  set k := sylowBar hz (q⁻¹ * ⟨v, hvS⟩) with hkdef
  have hkS : k ∈ escapingSylowImage S z := by
    rw [← sylowBar_range hz]
    exact ⟨_, rfl⟩
  have hkJ : k ∈ J := by
    rcases hγ k hkS hk with h | h
    · rw [h]
      exact J.one_mem
    · rw [h]
      exact hs.bar_mem
  have hvq : sylowBar hz ⟨v, hvS⟩ = sylowBar hz q * k := by
    rw [hkdef, map_mul, map_inv, mul_inv_cancel_left]
  have hvJ : sylowBar hz ⟨v, hvS⟩ ∈ J := hvq ▸ J.mul_mem hqJ hkJ
  have hvQ : (⟨_, hvJ⟩ : J) ∈ (sylowJ hz J : Subgroup J) := by
    rw [mem_sylowJ_iff, ← sylowBar_range hz]
    exact ⟨_, rfl⟩
  refine hs.mul_self_ne_bar e hvQ (Subtype.ext ?_)
  change sylowBar hz ⟨v, hvS⟩ * sylowBar hz ⟨v, hvS⟩ = escapingBar z
  rw [← map_mul, ← sylowBar_self hz]
  congr 1
  apply Subtype.ext
  change v * v = z
  rw [← pow_two, hvz]

end SzEightExclSetting

theorem false_of_szModel_of_center_ne
    {H : Subgroup G} (hq : EscapingQuotientData H z)
    (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∈ J)
    {c₀ : J} (hc₀ : c₀ ∈ Subgroup.center J) (hc₀1 : (c₀ : EscapingQuotient z) ≠ 1)
    (hc₀z : (c₀ : EscapingQuotient z) ≠ escapingBar z)
    (e : (J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ2, hZO⟩ := component_center_le_twoCore hq.oddCore_eq_bot hJ
  have hinv : ∀ s ∈ Subgroup.center J, orderOf s = 2 → s = ⟨escapingBar z, hzJ⟩ := by
    intro s hs hs2
    apply Subtype.ext
    exact eq_of_mem_twoCore_of_rank_one hq.bar_mem_center hq.bar_order hq.bar_mem_twoCore
      hq.twoCore_rank (hZO (Subgroup.mem_map_of_mem J.subtype hs))
      (by rw [Subgroup.orderOf_coe]; exact hs2)
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hZ2 ⟨c₀, hc₀⟩
  rw [Subgroup.orderOf_mk] at hn
  obtain _ | _ | n := n
  · rw [pow_zero, orderOf_eq_one_iff] at hn
    exact hc₀1 (by rw [hn]; rfl)
  · rw [zero_add, pow_one] at hn
    exact hc₀z (congrArg Subtype.val (hinv c₀ hc₀ hn))
  set c := c₀ ^ 2 ^ n with hcdef
  have hcZ : c ∈ Subgroup.center J := Subgroup.pow_mem _ hc₀ _
  have hc4 : orderOf c = 4 := by
    rw [hcdef, orderOf_pow_of_dvd (by positivity) (by rw [hn]; exact pow_dvd_pow 2 (by omega)),
      hn, show n + 1 + 1 = n + 2 by ring, pow_add, Nat.mul_div_cancel_left _ (by positivity)]
    norm_num
  have hcc2 : orderOf (c * c) = 2 := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by rw [hc4]; norm_num), hc4]
  have hcc : c * c ≠ 1 := fun h => by
    rw [h, orderOf_one] at hcc2
    exact absurd hcc2 (by decide)
  have hcccc : c * c * (c * c) = 1 := by
    have h4 := pow_orderOf_eq_one c
    rw [hc4] at h4
    calc c * c * (c * c) = c ^ 4 := by
          rw [pow_succ, pow_succ, pow_succ, pow_one, ← mul_assoc]
      _ = 1 := h4
  have hu : ∀ s ∈ Subgroup.center J, s * s = 1 → s = 1 ∨ s = c * c := by
    intro s hs hss
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · right
      rw [hinv s hs (orderOf_eq_prime (by rw [pow_two]; exact hss) hs1),
        hinv (c * c) (Subgroup.mul_mem _ hcZ hcZ) hcc2]
  exact false_of_szModel_of_mem_center hJ.1.1.commutator_eq_top hZ2 hcZ hcc hcccc hu e

theorem squareCaseSzEightExcluded : SquareCaseSzEightExcluded := by
  intro G _ _ S H z hS J hJ _ hrank hK ⟨e⟩
  have hq := escapingQuotientData hS.core (hS.core.sylow_le hS.central.1) hS.central.2.1
    hS.escape
  have hzJ : escapingBar z ∈ J := hS.caseTwo J hJ
  by_cases hα : ∃ c ∈ Subgroup.center J, (c : EscapingQuotient z) ≠ 1 ∧
      (c : EscapingQuotient z) ≠ escapingBar z
  · obtain ⟨c, hc, hc1, hcz⟩ := hα
    exact false_of_szModel_of_center_ne hq hJ hzJ hc hc1 hcz e
  push Not at hα
  have hs : SzEightExclSetting S H z J := ⟨hS, hJ, hrank, fun c hc => by
    by_cases h1 : (c : EscapingQuotient z) = 1
    · exact Or.inl h1
    · exact Or.inr (hα c hc h1)⟩
  have := hs.normal
  rcases hK with hγ | ⟨c, hc, hc1, hcz⟩
  · exact hs.false_of_forall_centralizer e hγ
  · exact hcz (hα c hc hc1)

end CFSG.ProperTwoGeneratedCore.Lemma37
