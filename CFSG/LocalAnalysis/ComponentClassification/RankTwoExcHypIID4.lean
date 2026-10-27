module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIBasic
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)

theorem even_card_graphFixedRootGroup
    (t : TwistTag)
    (ht : 0 < t.foldedTag.rank) (K : Type) [Field K] (σ : K →+* K) (h2 : (2 : K) = 0) :
    Even (Nat.card (graphFixedRootGroup t K σ)) := by
  set a : Fin t.foldedTag.rank := ⟨0, ht⟩
  set x : graphFixedRootGroup t K σ :=
    ⟨orbitX t K σ a 1, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (orbitX_mem_graphFixedPosUnipotent _ _ a 1)⟩
  have h2a : (1 : orbitField t K σ a) + 1 = 0 :=
    Subtype.ext (by
      change (1 : K) + 1 = 0
      rw [one_add_one_eq_two, h2])
  have hx2 : x ^ 2 = 1 := Subtype.ext (by
    rw [pow_two, Subgroup.coe_mul]
    change ((orbitX t K σ a 1 : ModGL t.tag K)) * (orbitX t K σ a 1 : ModGL t.tag K) = 1
    rw [← Subgroup.coe_mul, ← orbitX_add, h2a, orbitX_zero]
    rfl)
  have hx1 : x ≠ 1 := fun h => by
    have h' : orbitX t K σ a 1 = orbitX t K σ a 0 := by
      rw [orbitX_zero]
      exact Subtype.ext (congrArg (fun g : graphFixedRootGroup t K σ => (g : ModGL t.tag K)) h)
    exact one_ne_zero (orbitX_injective σ a h')
  rw [even_iff_two_dvd, ← orderOf_eq_prime hx2 hx1]
  exact orderOf_dvd_natCard _

theorem rigidInvolution_trialityD4
    {m : ℕ} (hm : 1 ≤ m)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ m) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ m)) (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hαX : α ∉ OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hα2 : α ^ 2 = 1) :
    RigidInvolution (OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      α := by
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 3 * m) (by rw [hK, ← pow_mul, mul_comm])
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_injective (fun x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      (x : ModGL TwistTag.D4.tag K)) Subtype.val_injective
  have hZ : center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  obtain ⟨⟨e, he⟩, δ, hδ, -, ψ, hψ, -⟩ :=
    even_triality_outer_involutions_canonical_field hm K hK σ hσ α hα2 hαX
  have he1 : 1 ≤ e := by omega
  refine rigidInvolution_of_conj hψ ?_
  set η := fieldActor (t := TwistTag.D4) σ δ
  have hη2 : η ^ 2 = 1 := by
    rw [← hψ, sq, show ψ * α * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (α * α) * ψ⁻¹ by group, ← sq, hα2,
      mul_one, mul_inv_cancel]
  have hηX : η ∉ OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    fun h => hαX (by
    have := (inner_normal _).conj_mem _ h ψ⁻¹
    rwa [← hψ, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at this)
  obtain ⟨-, -, hk, -, hσ₀, hJC, -, hJs, -, -, -, hNη, hNnorm, hcent, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      (ℓ := 2) (d := e) (m := 2) Nat.prime_two he1 le_rfl (by norm_num) K
      (by rw [hK, ← pow_mul, he]; ring_nf) σ (fun c => by rw [hσ, he]; ring_nf)
      δ (fun c => by rw [hδ, show 3 * m / 2 = 3 * e by omega])
  have h2 : (2 : fixSubfield δ) = 0 := by
    have : CharP (fixSubfield δ) 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega : 1 ≤ 3 * e) hk
    exact CharTwo.two_eq_zero
  have hJe : Even (Nat.card (trialityFieldImage σ δ)) := by
    rw [trialityFieldImage, ← Nat.card_congr ((graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _
        (baseChangeGL_injective _)).toEquiv]
    exact even_card_graphFixedRootGroup TwistTag.D4 (by decide) _ _ h2
  exact rigidInvolution_of_simple' hZ hηX hη2 hJC hJs hJe hNη hNnorm hcent.le

theorem hypII_of_trialityD4
    {A : Type} [Group A] [Finite A]
    (hA : commutator A = ⊤) {m : ℕ} (h : ChevalleyExceptionalModel (A ⧸ center A) .trialityD4 2 m) :
    HypII A := by
  obtain ⟨⟨hp, hm, -⟩, hmod⟩ := h
  have hmod' : TwistedChevalleyModel (A ⧸ center A) .D4 (2 ^ m) := hmod
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hm hmod'
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv _ e.toEquiv
  exact hypII_of_forall_rigid (exceptional_fixed_center_trivial TwistTag.D4 K σ)
    (fun α hα hα2 => rigidInvolution_trialityD4 hm hK σ hσ α hα hα2) hA e

end CFSG.ComponentClassification.RankTwoExcHypII
