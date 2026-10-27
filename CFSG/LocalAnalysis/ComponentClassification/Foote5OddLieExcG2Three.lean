module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcCore
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1ToralData
public import CFSG.RankThree.SteinbergR3ESmallReeRadical

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_card_eq_three_pow {K : Type} [Field K] [Finite K] (hK3 : ringChar K = 3) :
    CharP K ReeTag.G2.prime ∧ ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 3 ^ f := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h3 : CharP K 3 := hK3 ▸ ringChar.charP K
  refine ⟨h3, ?_⟩
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 3
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

theorem commutator_mem_range_conj_G2_three
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K = 3)
    (a b : MulAut (adjointGroup Tag.G2 K)) :
    a * b * a⁻¹ * b⁻¹ ∈
      (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range := by
  obtain ⟨hch, f, hf, hK⟩ := exists_card_eq_three_pow hK3
  obtain ⟨-, hNF, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  refine commutator_mem_range_conj_of_forall (φ := ReeTag.G2.finiteExceptionalAut K)
    (fun c => ?_) a b
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF c
  exact ⟨g, k, hgk⟩

theorem outerCoreAt_toral_G2_three
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K = 3) {c : Fin Tag.G2.rank → Kˣ}
    (hc : ∀ i, c i = 1 ∨ c i = -1) {i₀ : MulAut (adjointGroup Tag.G2 K)}
    (hi₀ : ∀ h : adjointGroup Tag.G2 K,
      (i₀ h : ModGL Tag.G2 K) = rootDiagUnit Tag.G2 c * h * (rootDiagUnit Tag.G2 c)⁻¹) :
    OuterCoreAt i₀ := by
  classical
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK2 : ringChar K ≠ 2 := by
    rw [hK3]
    decide
  have hle : toralCentralizer Tag.G2 K c ≤ adjointGroup Tag.G2 K := inf_le_left
  refine outerCoreAt_of_pPrimeCore center_adjointGroup_eq_bot
    (F := (toralCentralizer Tag.G2 K c).subgroupOf (adjointGroup Tag.G2 K)) (fun s => ?_) ?_
    fun a b _ _ => commutator_mem_range_conj_G2_three hK3 a b
  · rw [Subgroup.mem_subgroupOf, mem_toralCentralizer, ← Subtype.coe_inj, hi₀]
    exact ⟨fun h => ⟨s.2, h⟩, fun h => h.2⟩
  · refine pPrimeCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) ?_
    by_cases hc1 : c = 1
    · subst hc1
      have htop : toralCentralizer Tag.G2 K 1 = adjointGroup Tag.G2 K := by
        ext g
        rw [mem_toralCentralizer, rootDiagUnit_one, one_mul, inv_one, mul_one]
        exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
      obtain ⟨hsimp, hnab, -⟩ := odd_pinned_Chevalley_p_components Tag.G2 K hK2
      exact pPrimeCore_eq_bot_of_mulEquiv (MulEquiv.subgroupCongr htop)
        (pPrimeCore_eq_bot_of_isSimpleGroup hnab)
    · exact CatLeafProof.pPrimeCore_toralCentralizer_G2 hK2 hc hc1

theorem g2ThreeInnerCoreInput :
    G2ThreeInnerCoreInput := by
  intro K _ _ hK3 α hα _ g a hαg
  have hKodd : Odd (Nat.card K) := by
    obtain ⟨-, f, -, hK⟩ := exists_card_eq_three_pow hK3
    rw [hK]
    exact Odd.pow (by decide)
  exact outerCoreAt_innerDiag_of_toral (Or.inl rfl) hKodd
    (fun c hc i₀ hi₀ => outerCoreAt_toral_G2_three hK3 hc hi₀) hαg hα

theorem outerCoreAt_G2_three_field
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K = 3) {e : ℕ} (he : 1 ≤ e)
    (hKe : Nat.card K = (3 ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (3 ^ e))
    {α : MulAut (adjointGroup Tag.G2 K)} {g : adjointGroup Tag.G2 K} {a : Fin Tag.G2.rank → Kˣ}
    (hαg : ∀ h : adjointGroup Tag.G2 K, (α h : ModGL Tag.G2 K) =
      (g : ModGL Tag.G2 K) * rootDiagUnit Tag.G2 a *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL Tag.G2 K) * (rootDiagUnit Tag.G2 a)⁻¹ *
          (g : ModGL Tag.G2 K)⁻¹)
    (hα : α ^ 2 = 1) : OuterCoreAt α := by
  classical
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have : Finite (fixSubfield δ) := Subtype.finite
  have hK2 : ringChar K ≠ 2 := by
    rw [hK3]
    decide
  obtain ⟨hQ1, -⟩ :=
    exceptional_Lang_quadratic_field_coset_conjugacy Nat.prime_three he K hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 Tag.G2
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, hψ, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hψ' : ψ * α * ψ⁻¹ = β := MulEquiv.ext fun u => Subtype.ext ((hψ u).trans (hβ u).symm)
  refine outerCoreAt_of_conj hψ' ?_
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage_of_det_one (τ := Tag.G2) (Or.inl rfl) δ
  have hJC : fixedFieldImage Tag.G2 δ ≤ adjointGroup Tag.G2 K := fun x hx =>
    (fixedFieldImage_le hx).1
  have hfix : ∀ s : adjointGroup Tag.G2 K,
      β s = s ↔ s ∈ (fixedFieldImage Tag.G2 δ).subgroupOf (adjointGroup Tag.G2 K) := by
    intro s
    rw [Subgroup.mem_subgroupOf, ← hΓJ]
    constructor
    · intro hs
      refine mem_inf.2 ⟨s.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (s : ModGL Tag.G2 K) = s
      rw [← hβ, hs]
    · intro hs
      apply Subtype.ext
      rw [hβ]
      exact (mem_inf.1 hs).2
  obtain ⟨hJs0, hJna0, -⟩ :=
    odd_pinned_Chevalley_p_components Tag.G2 (fixSubfield δ) (ringChar_fixSubfield_ne_two hK2 δ)
  have eJ : (fixedFieldImage Tag.G2 δ).subgroupOf (adjointGroup Tag.G2 K) ≃*
      adjointGroup Tag.G2 (fixSubfield δ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv δ).symm
  exact outerCoreAt_of_pPrimeCore center_adjointGroup_eq_bot hfix
    (pPrimeCore_eq_bot_of_mulEquiv eJ (pPrimeCore_eq_bot_of_isSimpleGroup hJna0))
    fun a b _ _ => commutator_mem_range_conj_G2_three hK3 a b

theorem outerCoreAt_G2_three_ree
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime] (hK3 : ringChar K = 3) {b : ℕ}
    (hK : Nat.card K = 3 ^ (2 * b + 1)) (g : adjointGroup ReeTag.G2.tag K)
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut K b) ^ 2 = 1) :
    OuterCoreAt (MulAut.conj g * ReeTag.G2.finiteReeAut K b) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨ψ, hψ⟩ := G2_exceptional_coset_involution_conj b K hK g hα
  refine outerCoreAt_of_conj hψ ?_
  obtain ⟨-, -, hfixF, hmap, -⟩ := G2_exceptional_field_involution_fixed_p_components b K hK
  have e : ReeTag.G2.finiteReeFixedGroup K b ≃* ReeTag.G2.reeGamma K b :=
    ((ReeTag.G2.finiteReeFixedGroup K b).equivMapOfInjective _
      (adjointGroup ReeTag.G2.tag K).subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  obtain ⟨hsolv, -⟩ := RankThree.small_Ree_native_fixed_groups_solvable_radical_trivial b K hK
  exact outerCoreAt_of_pPrimeCore center_adjointGroup_eq_bot hfixF
    (pPrimeCore_eq_bot_of_mulEquiv e (pPrimeCore_eq_bot_of_solvable hsolv))
    fun a b _ _ => commutator_mem_range_conj_G2_three hK3 a b

theorem g2ThreeOuterCoreInput :
    G2ThreeOuterCoreInput := by
  intro K _ _ hK3 α hα _ hnot
  obtain ⟨hch, f, hf, hK⟩ := exists_card_eq_three_pow hK3
  rcases G2_three_involution_inner_quadratic_or_exceptional hf hK hα with
    hin | ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, hαF⟩
  · exact absurd hin hnot
  · exact outerCoreAt_G2_three_field hK3 he hKe δ hδ hαg hα
  · have hKb : Nat.card K = 3 ^ (2 * b + 1) := by rw [hK, hfb]
    subst hαF
    exact outerCoreAt_G2_three_ree hK3 hKb g hα

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
