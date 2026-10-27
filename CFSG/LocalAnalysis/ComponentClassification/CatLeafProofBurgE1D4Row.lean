module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Conj
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Field
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1D4Inner

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem burgOddCoreRow_triality_of_conj
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hc₁ : BurgE1D4OrderThreeInput)
    (hconj : ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, orderOf s = 2 →
      ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        ((c * s * c⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
          ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag (aLongTD4 K)) :
    BurgOddCoreRow (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  intro α hα
  obtain ⟨-, huniq, ⟨Θ, hΘ, -, -, hinv⟩, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := huniq α
  dsimp only at hgδ
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  have hΘα : Θ α = δ := hΘ α g δ hgδ
  rcases hinv α hα2 with h1 | ⟨hfe, hδc⟩
  ·
    rw [hΘα] at h1
    subst h1
    rw [fieldActor_one, mul_one] at hgδ
    have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
    have hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxZ : x ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h3 := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) => φ y)
          hx
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc y * x = x * y * x⁻¹ * x := by rw [h3]
          _ = x * y := by group
      rw [hZ, Subgroup.mem_bot] at hxZ
      exact hxZ
    have hg2 : orderOf g = 2 := by
      rw [← orderOf_injective _ hinj g, ← hgδ]
      exact hα
    obtain ⟨c, hc⟩ := hconj g hg2
    have ht := burgOddCoreFor_conj_aLong hp hp2 hf hK σ hσ hc₁ hc
    refine burgOddCoreFor_of_conj (MulAut.conj c) α ?_
    rw [hgδ, ← map_inv, ← map_mul, ← map_mul]
    exact ht
  ·
    rw [hΘα] at hδc
    obtain ⟨a, ha⟩ := hfe
    have ha1 : 1 ≤ a := by omega
    have hK6 : Nat.card K = (p ^ a) ^ 6 := by rw [hK, ha]; ring
    have hσ' : ∀ c, σ c = c ^ ((p ^ a) ^ 2) := fun c => by rw [hσ, ha, ← two_mul, pow_mul']
    have hδ' : ∀ c, δ c = c ^ ((p ^ a) ^ 3) := fun c => by
      rw [hδc, show 3 * f / 2 = a * 3 by omega, pow_mul]
    have hr : IsPrimePow (p ^ a) := hp.isPrimePow.pow (by omega)
    have hro : Odd (p ^ a) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    obtain ⟨-, ⟨ψ, hψ⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components hr hro K hK6
      σ hσ' δ hδ' g (by rw [← hgδ]; exact hα2)
    refine burgOddCoreFor_of_conj ψ α ?_
    rw [hgδ, hψ]
    exact burgOddCoreFor_fieldActor_triality hp hp2 ha1 hK6 σ δ hσ' hδ'

theorem burgOddCoreRow_triality
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (hc₁ : BurgE1D4OrderThreeInput) :
    BurgOddCoreRow (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  burgOddCoreRow_triality_of_conj hp hp2 hf hK σ hσ hc₁ (exists_conj_eq_aLong hp hp2 hf hK σ hσ)

theorem burgE1D4RowInput_holds
    :
    BurgE1D4OrderThreeInput → ∀ (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Odd q →
      Nat.card K = q ^ 3 → (∀ c, σ c = c ^ q) →
        BurgOddCoreRow (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  intro hc₁ q K _ _ σ hq hK hσ
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hqd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q (by norm_num)
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hqd
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_pow] at hK
      have := Finite.one_lt_card (α := K)
      omega
    · exact h0
  have hp2 : ringChar K ≠ 2 := fun h2 => by
    rw [h2] at hq
    exact (Nat.not_even_iff_odd.2 hq) ((Nat.even_pow' (by omega)).2 even_two)
  exact burgOddCoreRow_triality hp hp2 hf hK σ hσ hc₁

end CFSG.ComponentClassification.CatLeafProof
