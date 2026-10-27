module

public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionFixedComponents

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem pComponent_quasisimple_of_ambient {M : Type*} [Group M] {X : Subgroup M} {ℓ : ℕ}
    (h : ∀ L : Subgroup M, L ≤ X → CFSG.IsPComponent ℓ (L.subgroupOf X) → CFSG.IsQuasisimple L)
    (J : Subgroup X) (hJ : CFSG.IsPComponent ℓ J) : CFSG.IsQuasisimple J := by
  have hJL : (J.map X.subtype).subgroupOf X = J :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective J
  have hq := h (J.map X.subtype) (Subgroup.map_subtype_le J) (by rw [hJL]; exact hJ)
  exact (isQuasisimple_congr (J.equivMapOfInjective X.subtype X.subtype_injective)).2 hq

theorem inner_involution_fixed_p_components
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : x ^ 2 = 1) (ℓ : ℕ) (hℓ : ℓ.Prime) (J : Subgroup (fixedSubgroup (MulAut.conj x)))
    (hJ : CFSG.IsPComponent ℓ J) : CFSG.IsQuasisimple J := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k := by
    let _ : Algebra (ZMod p) k := ZMod.algebra k p
    refine ⟨fun y => ?_⟩
    obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := K) ({y} : Finset k)
    have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
    have : Fintype E := Fintype.ofFinite E
    have hpow : y ^ Fintype.card E = y :=
      congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
    refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]
  obtain ⟨-, -, hHR, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.D4
    hp hf hodd K hK σ.toRingHom hσ k Fr hFr
  have hRF : fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)) =
        twistedFixedGroup TwistTag.D4 k Fr := rfl
  set y := baseChangeGL ι (x : ModGL TwistTag.D4.tag K) with hydef
  have hyR : y ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)) := by
    rw [hRF]
    exact hHR ⟨x, x.2, rfl⟩
  have hy2 : y ^ 2 = 1 := by
    rw [hydef, ← map_pow, ← Subgroup.coe_pow, hx, Subgroup.coe_one, map_one]
  have hcomp := (e7_twisted_e6_triality_rational_inner_involution_fixed_p_components p k hp2 halg
    f hf).2.2 y hyR hy2 ℓ hℓ
  let φ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* ModGL TwistTag.D4.tag k :=
    (baseChangeGL ι).comp (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
  have hφ : Function.Injective φ := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hmap : (fixedSubgroup (MulAut.conj x)).map φ =
      ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k))⁆ ⊓
        Subgroup.centralizer {y} := by
    rw [hRF, hder]
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have hc' : x * c * x⁻¹ = c := hc
      have hcx : c * x = x * c := by
        calc c * x = x * c * x⁻¹ * x := by rw [hc']
          _ = x * c := by group
      change baseChangeGL ι (c : ModGL TwistTag.D4.tag K) * y =
        y * baseChangeGL ι (c : ModGL TwistTag.D4.tag K)
      rw [hydef, ← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hcx]
    · rintro ⟨⟨c, hc, rfl⟩, hcy⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      change x * ⟨c, hc⟩ * x⁻¹ = ⟨c, hc⟩
      have hcx : (⟨c, hc⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * x =
          x * ⟨c, hc⟩ := by
        refine Subtype.ext (baseChangeGL_injective ι ?_)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
        exact hcy
      rw [← hcx]
      group
  exact OddToralFixed.pComponent_quasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap))
    (pComponent_quasisimple_of_ambient fun L hL hLc => hcomp L hL hLc) J hJ

theorem odd_triality_all_involution_fixed_p_components
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hα : α ^ 2 = 1) (ℓ : ℕ) (hℓ : ℓ.Prime) (L : Subgroup (fixedSubgroup α))
    (hL : CFSG.IsPComponent ℓ L) : CFSG.IsQuasisimple L := by
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
    exact inner_involution_fixed_p_components hp hp2 hf K hK σ hσ g hg2 ℓ hℓ L hL
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
    exact (odd_triality_field_coset_involution_fixed_p_components
      (hp.isPrimePow.pow (by omega)) hodd K hK6 σ hσr δ hδr g hα).2.2 ℓ hℓ L hL

end CFSG.LieType.Chevalley
