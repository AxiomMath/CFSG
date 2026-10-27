module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LieType.Chevalley.G2SolvableNormalTrivial
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)
open CFSG.ComponentClassification.UnbalancedCatalog

section Fixed

variable {K : Type} [Field K] [Finite K]

theorem isSimpleGroup_fixedFieldImage_G2
    (σ : K ≃+* K) (h3 : 3 ≤ Nat.card (fixSubfield σ)) :
    IsSimpleGroup (fixedFieldImage .G2 σ) := by
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield σ) h3
  have : IsSimpleGroup ↥(adjointGroup .G2 (fixSubfield σ)) :=
    isSimpleGroup_of_quotient_center hq.2.1 center_adjointGroup_eq_bot
  exact (fixedFieldImageEquiv σ).symm.isSimpleGroup

theorem commutator_fixedFieldImage_G2_two
    (σ : K ≃+* K)
    (hk : Nat.card (fixSubfield σ) = 2) :
    IsSimpleGroup ↥(⁅fixedFieldImage .G2 σ, fixedFieldImage .G2 σ⁆ : Subgroup (ModGL .G2 K)) ∧
      (¬ ∀ a b : ↥(⁅fixedFieldImage .G2 σ, fixedFieldImage .G2 σ⁆ : Subgroup (ModGL .G2 K)),
        a * b = b * a) ∧
      Even (Nat.card
        ↥(⁅fixedFieldImage .G2 σ, fixedFieldImage .G2 σ⁆ : Subgroup (ModGL .G2 K))) := by
  set k := fixSubfield σ
  set H := adjointGroup .G2 k with hH
  set ι := baseChangeGL (τ := .G2) k.subtype with hι
  have hJ : fixedFieldImage .G2 σ = H.map ι := rfl
  have hD : (⁅fixedFieldImage .G2 σ, fixedFieldImage .G2 σ⁆ : Subgroup (ModGL .G2 K)) =
      (⁅H, H⁆ : Subgroup (ModGL .G2 k)).map ι := by
    rw [hJ, map_commutator]
  let eD : ↥(⁅H, H⁆ : Subgroup (ModGL .G2 k)) ≃*
      ↥(⁅fixedFieldImage .G2 σ, fixedFieldImage .G2 σ⁆ : Subgroup (ModGL .G2 K)) :=
    ((⁅H, H⁆ : Subgroup (ModGL .G2 k)).equivMapOfInjective ι (baseChangeGL_injective _)).trans
      (MulEquiv.subgroupCongr hD.symm)
  have hLie := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk
  have hs : IsSimpleGroup ↥(⁅H, H⁆ : Subgroup (ModGL .G2 k)) := by
    rcases hLie with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hM).2
    all_goals exact absurd h0 (by norm_num)
  have hnc : ¬ ∀ a b : ↥(⁅H, H⁆ : Subgroup (ModGL .G2 k)), a * b = b * a := by
    intro hcomm
    set R : Subgroup H := (⁅H, H⁆ : Subgroup (ModGL .G2 k)).subgroupOf H
    have hDH : (⁅H, H⁆ : Subgroup (ModGL .G2 k)) ≤ H := commutator_le_self H
    have : R.Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact (mem_normalizer_iff.mp (normalizer_commutator_ge_left H H g.2) n).mp hn⟩
    have hRs : Group.IsSolvable R := by
      refine Group.isSolvable_of_comm fun a b => ?_
      have := hcomm ((subgroupOfEquivOfLe hDH) a) ((subgroupOfEquivOfLe hDH) b)
      exact (subgroupOfEquivOfLe hDH).injective (by rwa [map_mul, map_mul])
    have hR := G2_solvable_normal_subgroups_trivial k R hRs
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hs.exists_pair_ne
    have h1 : ∀ x (hx : x ∈ (⁅H, H⁆ : Subgroup (ModGL .G2 k))), x = 1 := fun x hx => by
      have hxR : (⟨x, hDH hx⟩ : H) ∈ R := hx
      rw [hR, mem_bot] at hxR
      exact congrArg Subtype.val hxR
    exact hab (Subtype.ext ((h1 a ha).trans (h1 b hb).symm))
  have he : Even (Nat.card ↥(⁅H, H⁆ : Subgroup (ModGL .G2 k))) := by
    have : Finite k := Subtype.finite
    have : CharP k 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        le_rfl (by rw [hk, pow_one])
    obtain ⟨hLH, -, hLp, hx, hx2⟩ := G2_long_root_subgroup_perfect k
    have hLD : g2LongRootGroup k ≤ ⁅H, H⁆ := by
      rw [← hLp]
      exact commutator_mono hLH hLH
    have hord : orderOf (⟨_, hLD hx⟩ : ↥(⁅H, H⁆ : Subgroup (ModGL .G2 k))) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hx2 (ringChar.eq k 2)
    exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)
  refine ⟨eD.symm.isSimpleGroup, fun h => hnc fun a b => eD.injective ?_, ?_⟩
  · rw [map_mul, map_mul]
    exact h _ _
  · rwa [← Nat.card_congr eD.toEquiv]

end Fixed

theorem rigidInvolution_G2
    {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ m)
    (α : MulAut (adjointGroup .G2 K)) (hαX : α ∉ OuterAutomorphisms.inner (adjointGroup .G2 K))
    (hα2 : α ^ 2 = 1) :
    RigidInvolution (OuterAutomorphisms.inner (adjointGroup .G2 K)) α := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have : Finite (adjointGroup .G2 K) := Subtype.finite
  have hZ : center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hα1 : α ≠ 1 := fun h => hαX (h ▸ one_mem _)
  rcases even_G2_involution_inner_or_canonical_field hm K hK α (orderOf_eq_prime hα2 hα1) with
    h | ⟨⟨e, he⟩, hδ⟩
  · exact absurd h hαX
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hK
  set σ := fr ^ e with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ e := ringAut_pow_apply_of_frobenius hfr e
  obtain ⟨β, ψ, hβ, hψ, -⟩ := hδ σ.toRingHom fun c => by
    rw [show m / 2 = e by omega]
    exact hσ c
  have hβδ : β = entrywiseAdjointAut .G2 σ :=
    MulEquiv.ext fun u => Subtype.ext (by rw [hβ u, coe_entrywiseAdjointAut])
  rw [hβδ] at hψ
  refine rigidInvolution_of_conj hψ ?_
  set δ := entrywiseAdjointAut .G2 σ
  have hδ2 : δ ^ 2 = 1 := by
    rw [← hψ, sq, show ψ * α * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (α * α) * ψ⁻¹ by group, ← sq, hα2,
      mul_one, mul_inv_cancel]
  have hδX : δ ∉ OuterAutomorphisms.inner (adjointGroup .G2 K) := fun h => hαX (by
    have := (inner_normal _).conj_mem _ h ψ⁻¹
    rwa [← hψ, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at this)
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
  obtain ⟨-, hk, hJC, -, -, -, hNη, hNnorm, hcent⟩ :=
    even_G2_canonical_field_full_centralizer (by omega) K hK' σ hσ
  rcases Nat.lt_or_ge 1 e with he2 | he1
  ·
    have h3 : 3 ≤ Nat.card (fixSubfield σ) := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
    exact rigidInvolution_of_simple' hZ hδX hδ2 hJC (isSimpleGroup_fixedFieldImage_G2 σ h3)
      (even_card_fixedFieldImage (by decide) σ) hNη hNnorm hcent.le
  ·
    have hk2 : Nat.card (fixSubfield σ) = 2 := by rw [hk, show e = 1 by omega, pow_one]
    obtain ⟨hDs, hDc, hDe⟩ := commutator_fixedFieldImage_G2_two σ hk2
    exact rigidInvolution_of_derived' hZ hδ2 hJC hDs hDc hDe
      (forall_comm_eq_one_of_mulEquiv (fixedFieldImageEquiv σ) center_adjointGroup_eq_bot)
      hNη hNnorm hcent.le

theorem hypII_of_G2
    {A : Type} [Group A] [Finite A] (hA : commutator A = ⊤)
    {m : ℕ} (hm : 2 ≤ m)
    (h : ChevalleyExceptionalModel (A ⧸ center A) .G2 2 m) : HypII A := by
  obtain ⟨-, hmod⟩ := h
  have hmod' : UntwistedChevalleyModel (A ⧸ center A) .G2 (2 ^ m) := hmod
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmod'
  have : Finite (adjointGroup .G2 K) := Subtype.finite
  exact hypII_of_forall_rigid center_adjointGroup_eq_bot
    (fun α hα hα2 => rigidInvolution_G2 hm hK α hα hα2) hA e

end CFSG.ComponentClassification.RankTwoExcHypII
