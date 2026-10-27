module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Basic
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Rank

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open Subgroup

variable {N : Type*} [Group N]

theorem normalCore_le_glbConj (M : Subgroup N) (g : N) : M.normalCore ≤ GLBConj g M := fun x hx =>
  (mem_inf_glbConj (M.normalCore_le hx)
    (M.normalCore_le ((Subgroup.normalCore_normal M).conj_mem x hx g))).2

variable (N₀ : Subgroup N)

@[expose] def coreMk : N →* N ⧸ N₀.normalCore := QuotientGroup.mk' N₀.normalCore

@[expose] def coreImage : Subgroup (N ⧸ N₀.normalCore) := N₀.map (coreMk N₀)

theorem coreMk_eq_iff {a b : N} : coreMk N₀ a = coreMk N₀ b ↔ a⁻¹ * b ∈ N₀.normalCore :=
  QuotientGroup.eq

theorem mem_coreImage_iff {g : N} :
    coreMk N₀ g ∈ coreImage N₀ ↔ g ∈ N₀ := by
  constructor
  · rintro ⟨n, hn, hng⟩
    have : n⁻¹ * g ∈ N₀.normalCore := (coreMk_eq_iff N₀).mp hng
    have h2 : n⁻¹ * g ∈ N₀ := N₀.normalCore_le this
    simpa using mul_mem hn h2
  · intro hg
    exact ⟨g, hg, rfl⟩

variable {N₀}

theorem coreMk_surjective : Function.Surjective (coreMk N₀) := QuotientGroup.mk'_surjective _

variable [Finite N]

theorem stronglyEmbedded_coreImage (hM : GLBStronglyEmbedded 3 N₀) :
    GLBStronglyEmbedded 3 (coreImage N₀) := by
  have hC3 := not_dvd_card_normalCore hM
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hM.1
    refine eq_top_iff.mpr fun g _ => ?_
    have : coreMk N₀ g ∈ coreImage N₀ := htop ▸ Subgroup.mem_top _
    exact (mem_coreImage_iff N₀).mp this
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := N₀) 3 hM.2.1
    have hn' : orderOf (n : N) = 3 := by rw [← hn]; exact orderOf_submonoid n
    have hne : coreMk N₀ n ≠ 1 := by
      intro h1
      have hmem : (n : N) ∈ N₀.normalCore := by
        have := (QuotientGroup.eq_one_iff (n : N)).mp h1
        exact this
      have hdvd : orderOf (n : N) ∣ Nat.card N₀.normalCore :=
        Subgroup.orderOf_dvd_natCard N₀.normalCore hmem
      rw [hn'] at hdvd
      exact hC3 hdvd
    have hord : orderOf (coreMk N₀ n) = 3 := by
      have hdvd : orderOf (coreMk N₀ n) ∣ 3 := hn' ▸ orderOf_map_dvd (coreMk N₀) (n : N)
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne
      · exact h
    have hmemM : coreMk N₀ n ∈ coreImage N₀ := ⟨n, n.2, rfl⟩
    have := Subgroup.orderOf_dvd_natCard (coreImage N₀) hmemM
    rwa [hord] at this
  · intro x hx h3
    obtain ⟨g, rfl⟩ := coreMk_surjective x
    have hg : g ∉ N₀ := fun hg => hx ((mem_coreImage_iff N₀).mpr hg)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := (coreImage N₀ ⊓ GLBConj (coreMk N₀ g) (coreImage N₀) : Subgroup _)) 3 h3
    have hz' : orderOf (z : N ⧸ N₀.normalCore) = 3 := by rw [← hz]; exact orderOf_submonoid z
    obtain ⟨⟨n₁, hn₁, hn₁z⟩, ⟨m, ⟨n₂, hn₂, rfl⟩, hmz⟩⟩ := z.2
    have hzeq : coreMk N₀ n₁ = coreMk N₀ (g⁻¹ * n₂ * g) := by
      rw [hn₁z, ← hmz]
      simp [coreMk]
    have hc : n₁⁻¹ * (g⁻¹ * n₂ * g) ∈ N₀.normalCore := (coreMk_eq_iff N₀).mp hzeq
    have hn₁conj : n₁ ∈ GLBConj g N₀ := by
      have hA : g⁻¹ * n₂ * g ∈ GLBConj g N₀ :=
        Subgroup.mem_map.mpr ⟨n₂, hn₂, by simp⟩
      have hB : (n₁⁻¹ * (g⁻¹ * n₂ * g))⁻¹ ∈ GLBConj g N₀ :=
        inv_mem (normalCore_le_glbConj N₀ g hc)
      have := mul_mem hA hB
      simpa [mul_assoc] using this
    have hdvd1 : orderOf (coreMk N₀ n₁) ∣ orderOf n₁ := orderOf_map_dvd (coreMk N₀) n₁
    rw [hn₁z, hz'] at hdvd1
    have hdvd2 : orderOf n₁ ∣ Nat.card (N₀ ⊓ GLBConj g N₀ : Subgroup N) :=
      Subgroup.orderOf_dvd_natCard _ (⟨hn₁, hn₁conj⟩ : n₁ ∈ N₀ ⊓ GLBConj g N₀)
    exact hM.2.2 g hg (hdvd1.trans hdvd2)

omit [Finite N] in
theorem normalCore_coreImage : (coreImage N₀).normalCore = ⊥ := by
  have hW'n : ((coreImage N₀).normalCore.comap (coreMk N₀)).Normal :=
    (Subgroup.normalCore_normal _).comap _
  have hW'le : (coreImage N₀).normalCore.comap (coreMk N₀) ≤ N₀ := fun g hg =>
    (mem_coreImage_iff N₀).mp ((coreImage N₀).normalCore_le hg)
  have hle : (coreImage N₀).normalCore.comap (coreMk N₀) ≤ N₀.normalCore :=
    Subgroup.normal_le_normalCore.mpr hW'le
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨g, rfl⟩ := coreMk_surjective x
  exact (QuotientGroup.eq_one_iff g).mpr (hle hx)

theorem exists_elemAbelian_coreImage (hM : GLBStronglyEmbedded 3 N₀) (h2 : 2 ≤ pRank 3 N₀) :
    ∃ E : Subgroup (N ⧸ N₀.normalCore), E ≤ coreImage N₀ ∧ IsElemAbelian 3 E ∧
      9 ≤ Nat.card E := by
  obtain ⟨E₀, hE₀M, hE₀, hcard⟩ := exists_isElemAbelian_card_pRank Nat.prime_three N₀
  have hC3 := not_dvd_card_normalCore hM
  have hcop : Nat.Coprime 3 (Nat.card N₀.normalCore) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hC3
  have hinj : Function.Injective ((coreMk N₀).subgroupMap E₀) := by
    refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
    have hx1 : coreMk N₀ (x : N) = 1 := congrArg Subtype.val hx
    have hmem : (x : N) ∈ N₀.normalCore := (QuotientGroup.eq_one_iff (x : N)).mp hx1
    have h3 : (x : N) ^ 3 = 1 := hE₀.2 x x.2
    have hd1 : orderOf (x : N) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hd2 : orderOf (x : N) ∣ Nat.card N₀.normalCore := Subgroup.orderOf_dvd_natCard _ hmem
    have : orderOf (x : N) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact Subtype.ext (orderOf_eq_one_iff.mp this)
  have hcard' : Nat.card (E₀.map (coreMk N₀)) = Nat.card E₀ :=
    (Nat.card_eq_of_bijective _ ⟨hinj, MonoidHom.subgroupMap_surjective _ _⟩).symm
  have := hE₀.1
  refine ⟨E₀.map (coreMk N₀), Subgroup.map_mono hE₀M, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hE₀.2 e he, map_one]
  · rw [hcard', hcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ pRank 3 N₀ := Nat.pow_le_pow_right (by norm_num) h2

section KGroup

theorem isKGroup_quotient {N : Type*} [Group N] (h : IsKGroup N) (C : Subgroup N) [C.Normal] :
    IsKGroup (N ⧸ C) :=
  CFSG.KCore.KGroupNonab.quotient (fun e ⟨i, ⟨f⟩⟩ => ⟨i, ⟨e.trans f⟩⟩) h C

end KGroup

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
