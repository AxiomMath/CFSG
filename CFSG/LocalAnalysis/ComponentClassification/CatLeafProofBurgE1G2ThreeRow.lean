module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1G2Three
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1G2
public import CFSG.RankThree.Chevalley.SteinbergBTThreeG2Subfield

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem burgOddCoreFor_G2_three_field
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (hfe : Even f)
    {α : MulAut (adjointGroup ReeTag.G2.tag K)} {g : adjointGroup ReeTag.G2.tag K}
    (hαg : α = MulAut.conj g * ReeTag.G2.finiteExceptionalAut K ^ f) (hα : orderOf α = 2) :
    BurgOddCoreFor α := by
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; decide
  obtain ⟨-, -, -, -, -, h6, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨-, σ, -, -, hσc, hcard, hσφ⟩ := h6 hfe
  have hαg' : ∀ h : adjointGroup ReeTag.G2.tag K, (α h : ModGL ReeTag.G2.tag K) =
      (g : ModGL ReeTag.G2.tag K) * rootDiagUnit ReeTag.G2.tag 1 *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL ReeTag.G2.tag K) *
          (rootDiagUnit ReeTag.G2.tag 1)⁻¹ * (g : ModGL ReeTag.G2.tag K)⁻¹ := by
    intro h
    rw [hαg, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hσφ, rootDiagUnit_one, inv_one, mul_one, mul_one]
  obtain ⟨e, he⟩ := hfe
  have hKe : Nat.card K = (3 ^ e) ^ 2 := by rw [hK, ← pow_mul, he, mul_two]
  have hfe2 : f / 2 = e := by omega
  have he1 : 1 ≤ e := by omega
  refine burgOddCoreFor_of_quadratic ReeTag.G2.tag Nat.prime_three he1 hKe σ
    (fun c => by rw [hσc, hfe2]) hαg' hα ?_
  refine burgOddCoreFor_entrywise ReeTag.G2.tag (by decide) hK2 σ fun γ hγ _ hfix => ?_
  have hk : Nat.card (fixSubfield σ) = 3 ^ e := by
    rw [← hfe2]
    exact hcard
  obtain ⟨-, -, hfixing, -, hcard2⟩ :=
    three_G2_subfield_normalizer_and_pointwise_automorphism_centralizer hf he1 ⟨2, by omega⟩ hK
      (fixSubfield σ) hk
  have hJ : ∀ x : adjointGroup ReeTag.G2.tag K,
      (x : ModGL ReeTag.G2.tag K) ∈ subfieldImage ReeTag.G2.tag (fixSubfield σ) →
        x ∈ fixedSubgroup (entrywiseAdjointAut ReeTag.G2.tag σ) := by
    intro x hx
    have h1 : (x : ModGL ReeTag.G2.tag K) ∈ entrywiseFixedGroup ReeTag.G2.tag σ := by
      rw [RankThree.entrywiseFixedGroup_eq_fixedFieldImage_of_det_one (by decide) σ]
      exact hx
    rw [← map_fixedSubgroup_entrywiseAdjointAut] at h1
    obtain ⟨x', hx', hxx'⟩ := h1
    obtain rfl : x' = x := Subtype.ext hxx'
    exact hx'
  have hγ' : γ ∈ fixingSubgroup (MulAut (adjointGroup ReeTag.G2.tag K))
      (((subfieldImage ReeTag.G2.tag (fixSubfield σ)).subgroupOf
        (adjointGroup ReeTag.G2.tag K) : Subgroup (adjointGroup ReeTag.G2.tag K)) :
          Set (adjointGroup ReeTag.G2.tag K)) := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact hfix x (hJ x hx)
  rw [hfixing] at hγ'
  have hfe' : f / e = 2 := by rw [he, ← two_mul, Nat.mul_div_cancel 2 (show 0 < e by omega)]
  have hdvd : orderOf γ ∣ 2 := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hγ'
    rwa [hcard2, hfe'] at h1
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · rw [h1] at hγ
    exact absurd hγ (by decide)

theorem burgOddCoreRow_G2_three
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (hRee : ∀ a : ℕ, f = 2 * a + 1 → ∀ β : MulAut (adjointGroup ReeTag.G2.tag K),
      Odd (orderOf β) → ReeTag.G2.finiteReeAut K a * β = β * ReeTag.G2.finiteReeAut K a →
        (∀ x ∈ fixedSubgroup (ReeTag.G2.finiteReeAut K a), β x = x) → β = 1) :
    BurgOddCoreRow (adjointGroup ReeTag.G2.tag K) := by
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; decide
  intro α hα
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  obtain ⟨-, huniq, -, hinv, -, -, h7⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hgk, -⟩ := huniq α
  dsimp only at hgk
  rcases hinv α g k k.2 hgk hα2 with hk0 | hkf
  · rw [hk0, pow_zero, mul_one] at hgk
    have hαg : ∀ h : adjointGroup ReeTag.G2.tag K, (α h : ModGL ReeTag.G2.tag K) =
        (g : ModGL ReeTag.G2.tag K) * rootDiagUnit ReeTag.G2.tag 1 * (h : ModGL ReeTag.G2.tag K) *
          (rootDiagUnit ReeTag.G2.tag 1)⁻¹ * (g : ModGL ReeTag.G2.tag K)⁻¹ := by
      intro h
      rw [hgk, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        rootDiagUnit_one, inv_one, mul_one, mul_one]
    refine burgOddCoreFor_innerDiagonal (τ := ReeTag.G2.tag) (Or.inl rfl) hK2
      (fun k => k = g2Long) (fun b hb => exists_long_mem_rootCharKernel_G2 hK2 hb)
      (fun b hb hb1 => pPrimeCore_toralCentralizer_G2 hK2 hb hb1)
      (fun k hk h hU Z hZ η hη hodd => ?_) hαg hα
    subst hk
    exact G2_three_descended_root_SL2_pointwise_odd hf hK (AlgebraicClosure K) 1 h hU Z hZ η hη
      hodd
  · rw [hkf] at hgk
    rcases Nat.even_or_odd f with hfe | ⟨a, ha⟩
    · exact burgOddCoreFor_G2_three_field hf hK hfe hgk hα
    · obtain ⟨-, hF, -⟩ := h7 a ha
      rw [hF] at hgk
      have hKa : Nat.card K = 3 ^ (2 * a + 1) := by rw [hK, ha]
      obtain ⟨⟨ψ, hψ⟩, -, -⟩ := G2_exceptional_coset_involution_fixed_p_components a K hKa g
        (by rw [← hgk]; exact hα2)
      refine burgOddCoreFor_of_conj ψ α ?_
      rw [hgk, hψ]
      exact ⟨pPrimeCore_fixedSubgroup_finiteReeAut a hKa, hRee a ha⟩

end CFSG.ComponentClassification.CatLeafProof
