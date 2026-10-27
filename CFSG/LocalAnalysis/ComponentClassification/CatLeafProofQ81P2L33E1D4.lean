module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1Base
public import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem not_isPGroup_of_conj_eq {C : Type} [Group C] [Finite C] {ψ β γ : MulAut C}
    (hψ : ψ * β * ψ⁻¹ = γ)
    (h : ¬ IsPGroup 2 (↥(fixedSubgroup γ) ⧸ pPrimeCore 2 ↥(fixedSubgroup γ))) :
    ¬ IsPGroup 2 (↥(fixedSubgroup β) ⧸ pPrimeCore 2 ↥(fixedSubgroup β)) := by
  have hc : MulAut.congr ψ β = ψ * β * ψ⁻¹ := MulEquiv.ext fun _ => rfl
  have hfix := ExcSelector.fixedSubgroup_congr ψ β
  rw [hc, hψ] at hfix
  exact not_isPGroup_of_mulEquiv ((Subgroup.equivMapOfInjective _ ψ.toMonoidHom
    ψ.injective).trans (MulEquiv.subgroupCongr hfix.symm)) h

variable {K : Type} [Field K] [Finite K]

theorem not_isPGroup_triality_field
    {ℓ a : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (ha : 1 ≤ a)
    (hK : Nat.card K = ℓ ^ (3 * a * 2)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ (a * 2))
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ ℓ ^ (3 * a)) :
    ¬ IsPGroup 2 (↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) ⧸
      pPrimeCore 2 ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ))) := by
  obtain ⟨-, -, -, -, hord, hJC, hfixJ, -, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      hℓ ha (le_refl 2) (by norm_num : Nat.Coprime 2 3) K hK σ hσ δ hδ
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set J := trialityFieldImage σ δ
  have hF : fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) = J.subgroupOf C := by
    change _ = (J).comap C.subtype
    rw [← hfixJ, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    rfl
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  refine not_isPGroup_of_mulEquiv
    ((MulEquiv.subgroupCongr hF).trans (Subgroup.subgroupOfEquivOfLe hJC)) ?_
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  have : Finite (fixSubfield δ) := Subtype.finite
  have hσ₀ : fixSubfieldRestrict σ δ ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  set b : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩
  refine not_isPGroup_of_sl2
    (ExcSelector.ringChar_subfield_ne_two (ringChar_fixSubfield_ne_two hK2 δ) _)
    ((baseChangeGL (fixSubfield δ).subtype).comp
      (orbitRankOneHom TwistTag.D4 (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom b))
    ((baseChangeGL_injective _).comp (orbitRankOneHom_injective_D4 hσ₀ b)) ?_
  rw [MonoidHom.range_comp]
  exact Subgroup.map_mono (range_orbitRankOneHom_le b)

theorem not_isPGroup_triality
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα : α ^ 2 = 1) (hα1 : α ≠ 1)
    (hinn : ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, x ^ 2 = 1 → x ≠ 1 →
      ∃ X : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        X ≤ fixedSubgroup (MulAut.conj x) ∧ ⁅X, X⁆ = X ∧ 2 ∣ Nat.card X) :
    ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α)) := by
  classical
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
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
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hα1 (map_one _)
    obtain ⟨X, hXF, hXp, hX2⟩ := hinn g hg2 hg1
    exact not_isPGroup_of_perfect hXF hXp hX2
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
    exact not_isPGroup_of_conj_eq hψ
      (not_isPGroup_triality_field hp hp2 (by omega) hK6' σ hσ' δ hδ')

end CFSG.ComponentClassification.HarrisLit.L33.E1
