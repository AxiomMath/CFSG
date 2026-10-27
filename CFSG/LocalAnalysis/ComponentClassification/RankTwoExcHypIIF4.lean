module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIBasic
public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem finiteReeFixedGroup_eq_reeFixed
    (m : ℕ) :
    ReeTag.F4.finiteReeFixedGroup K m = reeFixed ReeTag.F4 K m := by
  apply map_injective (adjointGroup ReeTag.F4.tag K).subtype_injective
  change ReeTag.F4.reeGamma K m = _
  rw [ReeTag.reeGamma_eq_reeFixedGroup, reeFixedGroup_eq_map_reeFixed]

theorem forall_comm_finiteReeFixedGroup
    {m : ℕ}
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ∀ z ∈ ReeTag.F4.finiteReeFixedGroup K m,
      (∀ g ∈ ReeTag.F4.finiteReeFixedGroup K m, z * g = g * z) → z = 1 :=
  forall_comm_eq_one_of_mulEquiv ((ReeTag.F4.finiteReeFixedGroup K m).equivMapOfInjective
    (adjointGroup ReeTag.F4.tag K).subtype Subtype.val_injective).symm
    (ReeTag.large_Ree_fixed_group_center_trivial m K hK)

theorem finiteReeFixedGroup_simple_even
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    IsSimpleGroup (ReeTag.F4.finiteReeFixedGroup K m) ∧
      Even (Nat.card (ReeTag.F4.finiteReeFixedGroup K m)) := by
  set Γ := ReeTag.F4.finiteReeFixedGroup K m with hΓ
  let e : Γ ≃* ReeTag.F4.reeGamma K m :=
    Γ.equivMapOfInjective (adjointGroup ReeTag.F4.tag K).subtype Subtype.val_injective
  refine ⟨?_, ?_⟩
  ·
    have hZ : center (reeFixed ReeTag.F4 K m) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz' : ReeTag.reeFixedEquivReeGamma K m z ∈ center (ReeTag.F4.reeGamma K m) :=
        (MulEquivClass.apply_mem_center_iff _).2 hz
      rw [ReeTag.large_Ree_fixed_group_center_trivial m K hK, mem_bot] at hz'
      exact mem_bot.2 ((ReeTag.reeFixedEquivReeGamma K m).injective (hz'.trans (map_one _).symm))
    have : IsSimpleGroup (reeFixed ReeTag.F4 K m) := isSimpleGroup_of_quotient_center
      (CFSG.LieType.Simplicity.isSimpleGroup_quotient_center_reeFixed_F4 m hm hK) hZ
    rw [hΓ, finiteReeFixedGroup_eq_reeFixed]
    infer_instance
  · obtain ⟨y, hy, hy2⟩ := ReeTag.involution_mem_reeGamma (K := K) hK
    have hord : orderOf (e.symm ⟨y, hy⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, hy2]
    exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)

theorem commutator_finiteReeFixedGroup_tits
    (hK : Nat.card K = 2) :
    IsSimpleGroup ↥(⁅ReeTag.F4.finiteReeFixedGroup K 0, ReeTag.F4.finiteReeFixedGroup K 0⁆ :
        Subgroup (adjointGroup ReeTag.F4.tag K)) ∧
      (¬ ∀ a b : ↥(⁅ReeTag.F4.finiteReeFixedGroup K 0, ReeTag.F4.finiteReeFixedGroup K 0⁆ :
        Subgroup (adjointGroup ReeTag.F4.tag K)), a * b = b * a) ∧
      Even (Nat.card ↥(⁅ReeTag.F4.finiteReeFixedGroup K 0, ReeTag.F4.finiteReeFixedGroup K 0⁆ :
        Subgroup (adjointGroup ReeTag.F4.tag K))) := by
  have : Fact (Nat.card K = 2) := ⟨hK⟩
  rw [finiteReeFixedGroup_eq_reeFixed]
  set R := reeFixed ReeTag.F4 K 0
  let e : ↥(commutator R) ≃* ↥(⁅R, R⁆ : Subgroup (adjointGroup ReeTag.F4.tag K)) :=
    ((commutator R).equivMapOfInjective R.subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr R.map_subtype_commutator)
  have hs := CFSG.Sporadic.Schreier.Tits.commutator_reeFixed_simple hK
  have hZ := CFSG.Sporadic.Schreier.Tits.center_commutator_reeFixed hK
  refine ⟨e.symm.isSimpleGroup, fun h => ?_, ?_⟩
  ·
    obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
    have hc : ∀ x : commutator R, x = 1 := fun x => by
      have hx : x ∈ center (commutator R) := mem_center_iff.mpr fun y =>
        e.injective (by rw [map_mul, map_mul]; exact h _ _)
      rw [hZ, mem_bot] at hx
      exact hx
    exact hab ((hc a).trans (hc b).symm)
  · rw [← Nat.card_congr e.toEquiv,
      Nat.card_congr (CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := K)).toEquiv,
      CFSG.Sporadic.Schreier.Tits.card_titsD]
    decide

theorem rigidInvolution_F4
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (α : MulAut (adjointGroup ReeTag.F4.tag K))
    (hαX : α ∉ OuterAutomorphisms.inner (adjointGroup ReeTag.F4.tag K)) (hα2 : α ^ 2 = 1) :
    RigidInvolution (OuterAutomorphisms.inner (adjointGroup ReeTag.F4.tag K)) α := by
  have : Finite (adjointGroup ReeTag.F4.tag K) := Finite.of_injective
    (fun x : adjointGroup ReeTag.F4.tag K => (x : ModGL ReeTag.F4.tag K)) Subtype.val_injective
  have hZ : center (adjointGroup ReeTag.F4.tag K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨ψ, hψ, -⟩ := even_F4_all_outer_involutions_canonical hf K hK α hα2 hαX
  refine rigidInvolution_of_conj hψ ?_
  set η := ReeTag.F4.finiteExceptionalAut K ^ f
  have hη2 : η ^ 2 = 1 := by
    rw [← hψ, sq, show ψ * α * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (α * α) * ψ⁻¹ by group, ← sq, hα2,
      mul_one, mul_inv_cancel]
  have hηX : η ∉ OuterAutomorphisms.inner (adjointGroup ReeTag.F4.tag K) := fun h => hαX (by
    have := (inner_normal _).conj_mem _ h ψ⁻¹
    rwa [← hψ, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at this)
  rcases Nat.even_or_odd' f with ⟨e, rfl | rfl⟩
  ·
    obtain ⟨fr, hfr, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two hf hK
    obtain ⟨-, -, -, -, hJC, -, ⟨-, hJs, hJe, -⟩, -, -, -, hNη, hNnorm, hcent⟩ :=
      even_F4_canonical_field_full_centralizer (by omega) K hK (fr ^ e)
        (ringAut_pow_apply_of_frobenius hfr e)
    exact rigidInvolution_of_simple' hZ hηX hη2 hJC hJs hJe hNη hNnorm hcent.le
  ·
    obtain ⟨-, -, -, -, -, hNη, hNnorm, hcent⟩ :=
      ReeTag.even_F4_canonical_exceptional_full_centralizer e K hK
    rw [inf_comm] at hcent
    rcases Nat.eq_zero_or_pos e with rfl | he
    ·
      obtain ⟨hDs, hDc, hDe⟩ := commutator_finiteReeFixedGroup_tits (K := K) hK
      exact rigidInvolution_of_derived hZ hη2 hDs hDc hDe
        (inf_centralizer_commutator_eq_bot (forall_comm_finiteReeFixedGroup hK) hDs hDc)
        hNη hNnorm hcent.le
    · obtain ⟨hΓs, hΓe⟩ := finiteReeFixedGroup_simple_even he hK
      exact rigidInvolution_of_simple hZ hηX hη2 hΓs hΓe hNη hNnorm hcent.le

theorem hypII_of_F4
    {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤) {m : ℕ}
    (h : ChevalleyExceptionalModel (A ⧸ center A) .F4 2 m) : HypII A := by
  obtain ⟨⟨hp, hm, -⟩, hmod⟩ := h
  have hmod' : UntwistedChevalleyModel (A ⧸ center A) .F4 (2 ^ m) := hmod
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hmod'
  have : CharP K ReeTag.F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hm hK
  have : Finite (adjointGroup ReeTag.F4.tag K) := Finite.of_equiv _ e.toEquiv
  exact hypII_of_forall_rigid center_adjointGroup_eq_bot
    (fun α hα hα2 => rigidInvolution_F4 hm hK α hα hα2) hA e

end CFSG.ComponentClassification.RankTwoExcHypII
