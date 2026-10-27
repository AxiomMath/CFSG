module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Covers

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

namespace CoverExcl

theorem isBenderGroup_of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : CFSG.BenderSuzuki.IsBenderGroup K) : CFSG.BenderSuzuki.IsBenderGroup K' := by
  cases h with
  | isPSL2 n hn f => exact .isPSL2 n hn (e.symm.trans f)
  | isSuzuki n hn f => exact .isSuzuki n hn (e.symm.trans f)
  | isPSU3 n hn f => exact .isPSU3 n hn (e.symm.trans f)

theorem center_eq_bot_of_isSimpleGroup {K : Type*} [Group K] [IsSimpleGroup K]
    (h : ∃ a b : K, a * b ≠ b * a) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h' | h'
  · exact h'
  · obtain ⟨a, b, hab⟩ := h
    exact absurd (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top b) a) hab

variable {J : Type*} [Group J]

theorem center_quotient_eq_map {Z₀ : Subgroup J} [Z₀.Normal] (hZ₀ : Z₀ ≤ Subgroup.center J)
    (hbot : Subgroup.center (J ⧸ Subgroup.center J) = ⊥) :
    Subgroup.center (J ⧸ Z₀) = (Subgroup.center J).map (QuotientGroup.mk' Z₀) := by
  refine le_antisymm (fun c hc => ?_)
    (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective Z₀))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z₀ c
  refine ⟨g, ?_, rfl⟩
  have hg : (g : J ⧸ Subgroup.center J) ∈ Subgroup.center (J ⧸ Subgroup.center J) := by
    refine Subgroup.mem_center_iff.mpr fun h => ?_
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective h
    have hc' := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk' Z₀ h)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at hc'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact hZ₀ hc'
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hg
  exact hg

theorem quotientCenterEquiv {Z₀ : Subgroup J} [Z₀.Normal] (hZ₀ : Z₀ ≤ Subgroup.center J)
    (h : Subgroup.center (J ⧸ Z₀) = (Subgroup.center J).map (QuotientGroup.mk' Z₀)) :
    Nonempty ((J ⧸ Z₀) ⧸ Subgroup.center (J ⧸ Z₀) ≃* J ⧸ Subgroup.center J) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq h).trans
    (QuotientGroup.quotientQuotientEquivQuotient Z₀ _ hZ₀)⟩

theorem not_mem_zpowers_sq [Finite J] (h2 : IsPGroup 2 (Subgroup.center J))
    (hne : Subgroup.center J ≠ ⊥) {c : Subgroup.center J}
    (hc : ∀ x, x ∈ Subgroup.zpowers c) : (c : J) ∉ Subgroup.zpowers ((c : J) ^ 2) := by
  rintro ⟨k, hk⟩
  have hk' : (c : J) ^ (2 * k) = c := by
    rw [zpow_mul, zpow_two, ← pow_two]
    exact hk
  have h1 : (c : J) ^ (2 * k - 1) = 1 := by
    rw [zpow_sub_one, hk', mul_inv_cancel]
  have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hc] at hdvd
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
  have h2d : (2 : ℤ) ∣ (Nat.card (Subgroup.center J) : ℤ) := by
    rw [hn]
    exact Int.natCast_dvd_natCast.mpr (dvd_pow_self 2 hn0)
  have := h2d.trans hdvd
  omega

theorem card_map_center_zpowers_sq [Finite J] (h2 : IsPGroup 2 (Subgroup.center J))
    (hne : Subgroup.center J ≠ ⊥) {c : Subgroup.center J} (hc : ∀ x, x ∈ Subgroup.zpowers c)
    {Z₀ : Subgroup J} [Z₀.Normal] (hZ₀ : Z₀ = Subgroup.zpowers ((c : J) ^ 2)) :
    Nat.card ((Subgroup.center J).map (QuotientGroup.mk' Z₀)) = 2 := by
  have hZ : Subgroup.center J = Subgroup.zpowers (c : J) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.zpow_mem _ c.2 k
  rw [hZ, MonoidHom.map_zpowers, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ₀]
    exact Subgroup.mem_zpowers _
  · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, hZ₀]
    exact not_mem_zpowers_sq h2 hne hc

theorem bender_cover_quotient_of_isCyclic
    {J : Type} [Group J] [Finite J]
    (hperf : commutator J = ⊤) (h2 : IsPGroup 2 (Subgroup.center J))
    (hcyc : IsCyclic (Subgroup.center J)) (hne : Subgroup.center J ≠ ⊥)
    [IsSimpleGroup (J ⧸ Subgroup.center J)]
    (hnonab : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (J ⧸ Subgroup.center J)) :
    Nonempty ((J ⧸ Subgroup.center J) ≃* CFSG.Theory.Comparator.PSL2Model 2) ∨
      Nonempty ((J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) := by
  obtain ⟨c, hc⟩ := hcyc.exists_generator
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Subgroup J, Z₀ = Subgroup.zpowers ((c : J) ^ 2) := ⟨_, rfl⟩
  have hle : Z₀ ≤ Subgroup.center J := by
    rw [hZ₀, Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ c.2 2
  have : Z₀.Normal := Subgroup.normal_of_le_center hle
  have hcen := center_quotient_eq_map hle (center_eq_bot_of_isSimpleGroup hnonab)
  obtain ⟨e⟩ := quotientCenterEquiv hle hcen
  have : Group.IsPerfect J := ⟨hperf⟩
  have hcard : Nat.card (Subgroup.center (J ⧸ Z₀)) = 2 := by
    rw [hcen]
    exact card_map_center_zpowers_sq h2 hne hc hZ₀
  rcases bender_cover_quotient (Group.IsPerfect.commutator_eq_top (G := J ⧸ Z₀)) hcard
    (isBenderGroup_of_mulEquiv e.symm hB) with h | h
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.symm.trans f⟩
  · obtain ⟨f⟩ := h
    exact Or.inr ⟨e.symm.trans f⟩

end CoverExcl

end CFSG.ProperTwoGeneratedCore.Lemma37
