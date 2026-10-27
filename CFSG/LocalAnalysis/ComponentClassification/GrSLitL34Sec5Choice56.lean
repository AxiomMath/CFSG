module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools582
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitConjOrbit
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs56X
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_not_mem_commutator_mem {S N Q : Subgroup G} (hS : IsPGroup 2 S)
    (hNS : N ≤ S) (hNn : (N.subgroupOf S).Normal) (hQn : (Q.subgroupOf S).Normal)
    (hNQ : ¬ N ≤ Q) :
    ∃ y ∈ N, y ∉ Q ∧ y * y ∈ Q ∧ ∀ x ∈ S, x⁻¹ * y⁻¹ * x * y ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Q.subgroupOf S) with hπ
  have hSb : IsPGroup 2 (↥S ⧸ Q.subgroupOf S) := hS.to_quotient _
  have : Group.IsNilpotent (↥S ⧸ Q.subgroupOf S) := hSb.isNilpotent
  set H := (N.subgroupOf S).map π with hH
  have : H.Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  have hH1 : H ≠ ⊥ := by
    intro h
    apply hNQ
    intro n hn
    have h1 : π ⟨n, hNS hn⟩ ∈ H := mem_map_of_mem π (mem_subgroupOf.mpr hn)
    rw [h, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_subgroupOf.mp h1
  have hHZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hH1
  have h2 : 2 ∣ Nat.card ↥(H ⊓ center (↥S ⧸ Q.subgroupOf S)) := by
    obtain ⟨k, hk⟩ := (hSb.to_subgroup (H ⊓ center _)).exists_card_eq
    rw [hk]
    rcases k with _ | k
    · exfalso
      apply hHZ
      rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    · exact Dvd.intro_left _ (pow_succ 2 k).symm
  obtain ⟨⟨h, hh⟩, hh2⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hh2' : orderOf h = 2 := (Subgroup.orderOf_mk h hh).symm.trans hh2
  obtain ⟨n, hn, rfl⟩ := mem_map.mp (mem_inf.mp hh).1
  have hnc := mem_center_iff.mp (mem_inf.mp hh).2
  refine ⟨(n : G), mem_subgroupOf.mp hn, ?_, ?_, fun x hx => ?_⟩
  · intro hnQ
    have h1 : π n = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact mem_subgroupOf.mpr hnQ
    rw [h1, orderOf_one] at hh2'
    exact absurd hh2' (by norm_num)
  · have h1 : π (n * n) = 1 := by
      rw [map_mul, ← pow_two, ← hh2', pow_orderOf_eq_one]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_subgroupOf.mp h1
  · have h1 := hnc (π ⟨x, hx⟩)
    have h2 : π ((⟨x, hx⟩ : ↥S)⁻¹ * n⁻¹ * ⟨x, hx⟩ * n) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_assoc ((π ⟨x, hx⟩)⁻¹ * (π n)⁻¹) (π ⟨x, hx⟩) (π n), h1]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact mem_subgroupOf.mp h2

theorem card_le_four_mul_card_centralizer (hRank : L34CenterRankFact) {L S : Subgroup G}
    (hLperf : ⁅L, L⁆ = L) (htype : IsL34Type (L ⧸ Open.fusionZStar L))
    (hSyl : IsSylowTwoIn S (normalizer (L : Set G))) {u₀ : G} (hu₀S : u₀ ∈ S) (hu₀L : u₀ ∈ L)
    (hu₀2 : u₀ * u₀ = 1)
    (hcen : ∀ x ∈ S, x⁻¹ * u₀⁻¹ * x * u₀ ∈ coreActionKernel L) :
    Nat.card S ≤ 4 * Nat.card ↥(S ⊓ centralizer ({u₀} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have hΩ := hRank G L (S ⊓ L) hLperf htype hS₀
  have hrel := HSFLit.relIndex_inf_centralizer_eq_ncard S u₀
  set W := omegaOne (S ⊓ L ⊓ zStarIn L) with hW
  have hsub : {y | ∃ g ∈ S, g * u₀ * g⁻¹ = y} ⊆ (fun z => u₀ * z) '' (W : Set G) := by
    rintro y ⟨g, hg, rfl⟩
    refine ⟨u₀⁻¹ * (g * u₀ * g⁻¹), ?_, by group⟩
    have hgN : g ∈ normalizer (L : Set G) := hSyl.1 hg
    have hzS : u₀⁻¹ * (g * u₀ * g⁻¹) ∈ S :=
      mul_mem (inv_mem hu₀S) (mul_mem (mul_mem hg hu₀S) (inv_mem hg))
    have hzL : u₀⁻¹ * (g * u₀ * g⁻¹) ∈ L :=
      mul_mem (inv_mem hu₀L) ((mem_normalizer_iff.mp hgN u₀).mp hu₀L)
    have hzK : u₀⁻¹ * (g * u₀ * g⁻¹) ∈ coreActionKernel L := by
      have h1 := hcen g⁻¹ (inv_mem hg)
      rw [inv_inv] at h1
      have h2 := inv_mem h1
      rwa [show (g * u₀⁻¹ * g⁻¹ * u₀)⁻¹ = u₀⁻¹ * (g * u₀ * g⁻¹) by group] at h2
    have hzu := commute_of_mem_coreActionKernel hS2 hzS hzK hu₀S hu₀L
    have hz2 : u₀⁻¹ * (g * u₀ * g⁻¹) * (u₀⁻¹ * (g * u₀ * g⁻¹)) = 1 := by
      set z := u₀⁻¹ * (g * u₀ * g⁻¹) with hz
      have h1 : u₀ * z * (u₀ * z) = 1 := by
        rw [hz, show u₀ * (u₀⁻¹ * (g * u₀ * g⁻¹)) * (u₀ * (u₀⁻¹ * (g * u₀ * g⁻¹))) =
          g * (u₀ * u₀) * g⁻¹ by group, hu₀2, mul_one, mul_inv_cancel]
      calc z * z = u₀ * u₀ * (z * z) := by rw [hu₀2, one_mul]
        _ = u₀ * (u₀ * z) * z := by group
        _ = u₀ * (z * u₀) * z := by rw [hzu]
        _ = u₀ * z * (u₀ * z) := by group
        _ = 1 := h1
    exact subset_closure ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨hzS, hzL⟩,
      inf_coreActionKernel_le_zStarIn L (mem_inf.mpr ⟨hzL, hzK⟩)⟩, hz2⟩
  have hcard : {y | ∃ g ∈ S, g * u₀ * g⁻¹ = y}.ncard ≤ 4 := by
    calc {y | ∃ g ∈ S, g * u₀ * g⁻¹ = y}.ncard
        ≤ ((fun z => u₀ * z) '' (W : Set G)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (W : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Nat.card W := Nat.card_coe_set_eq _ |>.symm
      _ ≤ 4 := hΩ
  have hmul : (S ⊓ centralizer ({u₀} : Set G)).relIndex S *
      Nat.card ↥(S ⊓ centralizer ({u₀} : Set G)) = Nat.card S := by
    rw [relIndex, mul_comm, ← Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,
      card_mul_index]
  rw [← hmul, hrel]
  exact Nat.mul_le_mul_right _ hcard

theorem exists_lemma56_involution (hFour : L34CommutatorFourGroupFact) {L S : Subgroup G}
    (hLperf : ⁅L, L⁆ = L) (htype : IsL34Type (L ⧸ Open.fusionZStar L))
    (hSyl : IsSylowTwoIn S (normalizer (L : Set G))) :
    ∃ u₀ ∈ S ⊓ L, u₀ ∉ coreActionKernel L ∧ u₀ * u₀ = 1 ∧
      ∀ x ∈ S, x⁻¹ * u₀⁻¹ * x * u₀ ∈ coreActionKernel L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  obtain ⟨Y, hYP, hYe, hY4, hYZ, -, hYc⟩ := hFour G L (S ⊓ L) hLperf htype hS₀
  have hNQ : ¬ S ⊓ L ≤ S ⊓ coreActionKernel L := by
    intro h
    obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
      by_contra hne
      push Not at hne
      rw [(eq_bot_iff_forall Y).mpr hne, card_bot] at hY4
      omega
    have hyK : y ∈ coreActionKernel L := (mem_inf.mp (h (hYP hyY))).2
    have hyZ : y ∈ Y ⊓ zStarIn L := mem_inf.mpr ⟨hyY, inf_coreActionKernel_le_zStarIn L
      (mem_inf.mpr ⟨(mem_inf.mp (hYP hyY)).2, hyK⟩)⟩
    rw [hYZ] at hyZ
    exact hy1 (mem_bot.mp hyZ)
  have hNn : ((S ⊓ L).subgroupOf S).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact mem_inf.mpr ⟨mul_mem (mul_mem g.2 (mem_inf.mp hn).1) (inv_mem g.2),
      (mem_normalizer_iff.mp (hSyl.1 g.2) n).mp (mem_inf.mp hn).2⟩⟩
  have hQn : ((S ⊓ coreActionKernel L).subgroupOf S).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact mem_inf.mpr ⟨mul_mem (mul_mem g.2 (mem_inf.mp hn).1) (inv_mem g.2),
      (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel L (hSyl.1 g.2)) n).mp
        (mem_inf.mp hn).2⟩⟩
  obtain ⟨y, hyN, hyQ, -, hyc⟩ := exists_mem_not_mem_commutator_mem hS2 inf_le_left hNn hQn hNQ
  have hyS : y ∈ S := (mem_inf.mp hyN).1
  have hyL : y ∈ L := (mem_inf.mp hyN).2
  have hyK : y ∉ coreActionKernel L := fun h => hyQ (mem_inf.mpr ⟨hyS, h⟩)
  have hcZ : ∀ p ∈ S ⊓ L, p⁻¹ * y⁻¹ * p * y ∈ zStarIn L := by
    intro p hp
    have hpL : p ∈ L := (mem_inf.mp hp).2
    exact inf_coreActionKernel_le_zStarIn L (mem_inf.mpr
      ⟨mul_mem (mul_mem (mul_mem (inv_mem hpL) (inv_mem hyL)) hpL) hyL,
        (mem_inf.mp (hyc p (mem_inf.mp hp).1)).2⟩)
  obtain ⟨y', hy'Y, hy'y⟩ := hYc y hyN hcZ
  have hzK : y'⁻¹ * y ∈ coreActionKernel L := zStarIn_le_coreActionKernel L hy'y
  refine ⟨y', hYP hy'Y, fun hK => hyK ?_, hYe.2 y' hy'Y, fun x hx => ?_⟩
  · rw [show y = y' * (y'⁻¹ * y) by group]
    exact mul_mem hK hzK
  · have hxN : x⁻¹ ∈ normalizer (coreActionKernel L : Set G) :=
      normalizer_le_normalizer_coreActionKernel L (hSyl.1 (inv_mem hx))
    have h1 : x⁻¹ * (y'⁻¹ * y) * x ∈ coreActionKernel L := by
      have h := (mem_normalizer_iff.mp hxN (y'⁻¹ * y)).mp hzK
      rwa [inv_inv] at h
    rw [show x⁻¹ * y'⁻¹ * x * y' =
      x⁻¹ * (y'⁻¹ * y) * x * (x⁻¹ * y⁻¹ * x * y) * (y'⁻¹ * y)⁻¹ by group]
    exact mul_mem (mul_mem h1 (mem_inf.mp (hyc x hx)).2) (inv_mem hzK)

end CFSG.ComponentClassification.GrSLit.GrS5
