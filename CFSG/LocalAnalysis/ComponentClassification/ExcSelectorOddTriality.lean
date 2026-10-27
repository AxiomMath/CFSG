module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddTwisted
public import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_smallType_of_conj_eq {C : Type} [Group C] {ψ β γ : MulAut C}
    (hψ : ψ * β * ψ⁻¹ = γ)
    (h : ∀ K : Subgroup C, Assembly.IsComponentOf K (fixedSubgroup γ) → ¬ SmallType K)
    {K : Subgroup C} (hK : Assembly.IsComponentOf K (fixedSubgroup β)) : ¬ SmallType K := by
  have hc : MulAut.congr ψ β = ψ * β * ψ⁻¹ := MulEquiv.ext fun _ => rfl
  have hfix := fixedSubgroup_congr ψ β
  rw [hc, hψ] at hfix
  have hK' : Assembly.IsComponentOf (K.map ψ.toMonoidHom) (fixedSubgroup γ) := by
    rw [hfix]
    exact isComponentOf_map_of_equiv ψ hK
  exact fun hs => h _ hK' ((smallType_congr (ψ.subgroupMap K)).1 hs)

variable {K : Type} [Field K] [Finite K]

theorem odd_triality_field_not_smallType {ℓ a : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (ha : 1 ≤ a)
    (hK : Nat.card K = ℓ ^ (3 * a * 2)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ (a * 2))
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ ℓ ^ (3 * a))
    {L : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ))) :
    ¬ SmallType L := by
  obtain ⟨-, -, -, -, hord, hJC, hfixJ, hsimple, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      hℓ ha (le_refl 2) (by norm_num : Nat.Coprime 2 3) K hK σ hσ δ hδ
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set J := trialityFieldImage σ δ
  have hF : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) = J.subgroupOf C := by
    change _ = (J).comap C.subtype
    rw [← hfixJ, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    rfl
  rw [hF] at hL
  have eJ : J.subgroupOf C ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  have : IsSimpleGroup (J.subgroupOf C) := (MulEquiv.isSimpleGroup_congr eJ).2 hsimple
  rw [eq_of_isComponentOf_of_isSimpleGroup hL, smallType_congr eJ]
  have e₁ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥J :=
    (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  have : Finite (fixSubfield δ) := Subtype.finite
  rw [← smallType_congr e₁]
  exact graphFixedRootGroup_D4_odd_not_smallType (ringChar_fixSubfield_ne_two hK2 δ) _
    (by rw [← hord]; exact pow_orderOf_eq_one _)

theorem odd_triality_not_smallType {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα : α ^ 2 = 1)
    {L : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
  classical
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, -, hinv⟩, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF α
  change α = MulAut.conj g * fieldActor σ δ at hgδ
  by_cases hδ : δ = 1
  ·
    subst hδ
    rw [fieldActor_one, mul_one] at hgδ
    subst hgδ
    have hg2 : g ^ 2 = 1 := mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hα, map_one])
    exact odd_twisted_inner_not_smallType TwistTag.D4 hp hp2 hf hK σ hσ g hg2 hL
  ·
    have hΘα : Θ α = δ := hΘ α g δ hgδ
    obtain ⟨⟨a, ha⟩, hδc⟩ := (hinv α hα).resolve_left (by rw [hΘα]; exact hδ)
    rw [hΘα] at hδc
    have hodd : Odd (p ^ a) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hK6 : Nat.card K = (p ^ a) ^ 6 := by
      rw [hK, ha, ← pow_mul, ← pow_mul]
      ring_nf
    have hσr : ∀ c, σ c = c ^ ((p ^ a) ^ 2) := fun c => by
      rw [hσ, ha, ← pow_mul]
      ring_nf
    have hδr : ∀ c, δ c = c ^ ((p ^ a) ^ 3) := fun c => by
      rw [hδc, ha, ← pow_mul, show 3 * (a + a) / 2 = a * 3 by omega]
    subst hgδ
    obtain ⟨-, ⟨ψ, hψ⟩, -⟩ := odd_triality_field_coset_involution_fixed_p_components
      (hp.isPrimePow.pow (by omega)) hodd K hK6 σ hσr δ hδr g hα
    have hK6' : Nat.card K = p ^ (3 * a * 2) := by
      rw [hK6, ← pow_mul]
      ring_nf
    have hσ' : ∀ c, σ c = c ^ p ^ (a * 2) := fun c => by rw [hσr, ← pow_mul]
    have hδ' : ∀ c, δ c = c ^ p ^ (3 * a) := fun c => by rw [hδr, ← pow_mul, mul_comm]
    exact not_smallType_of_conj_eq hψ
      (fun L' hL' => odd_triality_field_not_smallType hp hp2 (by omega) hK6' σ hσ' δ hδ' hL') hL

end CFSG.ComponentClassification.ExcSelector
