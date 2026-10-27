module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Main
public import CFSG.LocalAnalysis.ComponentInitial.OddQuadraticEmptyLayer

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5 CFSG.Goldschmidt CFSG.Goldschmidt75
  CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem coreSep_at {a : G} {M X₁ X₂ : Subgroup G} (hMC : M ≤ centralizer ({a} : Set G))
    (hMn : centralizer ({a} : Set G) ≤ normalizer (M : Set G))
    (hX₁ : X₁ ⊓ centralizer ({a} : Set G) ≤ M)
    (hX₂ : X₂ ⊓ centralizer ({a} : Set G) ≤ coreActionKernel M)
    {K : Subgroup (centralizer ({a} : Set G) ⧸ goldschmidtOddCore (centralizer ({a} : Set G)))}
    (hK : CFSG.IsComponent K) :
    barOf (centralizer ({a} : Set G)) X₁ ≤ centralizer (K : Set _) ∨
      barOf (centralizer ({a} : Set G)) X₂ ≤ centralizer (K : Set _) := by
  set π := QuotientGroup.mk' (goldschmidtOddCore (centralizer ({a} : Set G))) with hπ
  set H₁ := (M.subgroupOf (centralizer ({a} : Set G))).map π with hH₁
  have hMn' : (M.subgroupOf (centralizer ({a} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hMC).mpr hMn
  have hH₁n : H₁.Normal := hMn'.map π (QuotientGroup.mk'_surjective _)
  have hOM : (oddCoreIn M).subgroupOf (centralizer ({a} : Set G)) ≤
      goldschmidtOddCore (centralizer ({a} : Set G)) := by
    have hOC : oddCoreIn M ≤ centralizer ({a} : Set G) := (map_subtype_le _).trans hMC
    refine le_sSup ⟨(normal_subgroupOf_iff_le_normalizer hOC).mpr
      fun c hc => mem_normalizer_oddCoreIn (hMn hc), ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hOC).toEquiv, oddCoreIn,
      card_map_of_injective M.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hX₂H : barOf (centralizer ({a} : Set G)) X₂ ≤ centralizer (H₁ : Set _) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨m, hm, rfl⟩
    have hxK := hX₂ (mem_inf.mpr ⟨mem_subgroupOf.mp hx, x.2⟩)
    have h1 := hxK.2 _ (mem_subgroupOf.mp hm)
    have h2 : π (m⁻¹ * x⁻¹ * m * x) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hOM (show ((m⁻¹ * x⁻¹ * m * x : centralizer ({a} : Set G)) : G) ∈ oddCoreIn M
        from h1)
    have h2' : (π m)⁻¹ * (π x)⁻¹ * π m * π x = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h2
    calc π m * π x = π x * π m * ((π m)⁻¹ * (π x)⁻¹ * π m * π x) := by group
      _ = π x * π m := by rw [h2', mul_one]
  rcases CFSG.LocalCores.component_normal_subgroup hK hH₁n with hKH | hKH
  · right
    exact hX₂H.trans (centralizer_le (SetLike.coe_subset_coe.mpr hKH))
  · left
    have h1 : H₁ ≤ centralizer (K : Set _) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hKH)
    refine le_trans ?_ h1
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, mem_subgroupOf.mpr (hX₁ (mem_inf.mpr ⟨mem_subgroupOf.mp hx, x.2⟩)), rfl⟩

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem exists_component_of_mem_Rs {a : G} (haRs : a ∈ conjugate (S ⊓ L) s)
    (ha2 : orderOf a = 2) :
    ∃ M : Subgroup G, IsTwoComponentAt a M ∧ M ∈ footeFamilyOf L₀ ∧ S ⊓ L ≤ M ∧
      conjugate (S ⊓ L) s ⊓ centralizer ({a} : Set G) ≤ coreActionKernel M := by
  have haQ := H.l511 haRs
  obtain ⟨hfix, hM, hMF, -, -, -⟩ := H.sec5.footeF_data haQ ha2
  refine ⟨footeF L₀ a, hM, hMF, hfix ▸ H.sec5.R_le_footeFixed haQ, fun y hy => ?_⟩
  obtain ⟨hyRs, hya⟩ := mem_inf.mp hy
  rw [H.sec5.mem_coreActionKernel_footeF_iff (H.sec5.Q_le haQ) ha2
    (H.sec5.S_le (H.Rs_le_S hyRs)) hya]
  exact H.sec5.Q_le (H.l511 hyRs)

theorem coreSep (h3 : Asc76.Asc76Theorem3Large) : CoreSep (S ⊓ L) (conjugate (S ⊓ L) s) := by
  intro a ha ha2 K hK
  have ha2' : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
  have hsN := H.s_mem_normalizer
  have huniq := H.sec5.sec4.huniq
  by_cases haRs : a ∈ conjugate (S ⊓ L) s
  ·
    obtain ⟨M, hM, hMF, hRM, hRsM⟩ := H.exists_component_of_mem_Rs haRs ha2
    exact coreSep_at hM.2.1 (le_normalizer_of_mem_footeFamilyOf huniq hM hMF)
      (fun x hx => hRM (mem_inf.mp hx).1) hRsM hK
  by_cases haR : a ∈ S ⊓ L
  ·
    set a' := s * a * s⁻¹ with ha'
    have ha'Rs : a' ∈ conjugate (S ⊓ L) s := H.conj_s_mem_Rs haR
    have ha'2 : orderOf a' = 2 := by rw [ha', orderOf_conj', ha2]
    obtain ⟨M₀, hM₀, hM₀F, hRM₀, hRsM₀⟩ := H.exists_component_of_mem_Rs ha'Rs ha'2
    have hM : IsTwoComponentAt a (conjugate M₀ s) := by
      have h1 := isTwoComponentAt_map_mulEquiv (MulAut.conj s⁻¹) hM₀
      rwa [MulAut.conj_apply, inv_inv, ha', show s⁻¹ * (s * a * s⁻¹) * s = a by group] at h1
    have hMF := conjugate_mem_footeFamilyOf hM₀F s
    refine (coreSep_at hM.2.1 (le_normalizer_of_mem_footeFamilyOf huniq hM hMF)
      (fun x hx => ?_) (fun y hy => ?_) hK).symm
    ·
      rw [mem_conjugate_iff]
      exact hRM₀ (mem_conjugate_iff.mp (mem_inf.mp hx).1)
    ·
      obtain ⟨hyR, hya⟩ := mem_inf.mp hy
      rw [Foote47.coreActionKernel_conjugate, mem_conjugate_iff]
      refine hRsM₀ (mem_inf.mpr ⟨H.conj_s_mem_Rs hyR, ?_⟩)
      rw [mem_centralizer_singleton_iff] at hya ⊢
      calc s * y * s⁻¹ * a' = s * (y * a) * s⁻¹ := by rw [ha']; group
        _ = s * (a * y) * s⁻¹ := by rw [hya]
        _ = a' * (s * y * s⁻¹) := by rw [ha']; group
  ·
    exfalso
    have hsolv := H.isSolvable_centralizer_of_mem h3 ha ha2' haR haRs
    have : Group.IsSolvable (centralizer ({a} : Set G) ⧸
        goldschmidtOddCore (centralizer ({a} : Set G))) :=
      Group.isSolvable_of_surjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    exact LocalAnalysis.ComponentInitial.not_isComponent_of_isSolvable K hK

end Hyp

end CFSG.ComponentClassification.Sol78.F514
