module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.AlgebraicGroups

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint WithConv
open scoped CFSG.ConvolutionPoints Pointwise


variable {τ : Tag} {M : Type} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem neg_mem_kernelRoots {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) :
    -α ∈ kernelRoots χ := by
  refine ⟨IsRoot.neg hα.1, ?_⟩
  have h : χ (Multiplicative.ofAdd (-α)) = (χ (Multiplicative.ofAdd α))⁻¹ := by
    rw [ofAdd_neg, map_inv]
  rw [h, hα.2, inv_one]

theorem torus_sup_rootSpan_le_adjointGroup {L : Type} [Field L] (S : Set (Fin τ.rank → ℤ)) :
    torusGroup τ L ⊔ rootSpan τ L S ≤ adjointGroup τ L :=
  sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' (rootSpan_le_adjointGroup L S)

theorem canonicalRep_mem_torus_sup_rootSpan_kernelRoots {L : Type} [Field L]
    {y : WeylGroup τ}
    (hy : y ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots χ)) :
    canonicalRep (coxeterSystem τ) L y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) := by
  set Mχ := torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ)
  let R : Subgroup (WeylGroup τ) :=
    { carrier := {x | canonicalRep (coxeterSystem τ) L x ∈ Mχ}
      mul_mem' := fun {x x'} hx hx' => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := τ) (R := L) x x'
        have hmul : canonicalRep (coxeterSystem τ) L (x * x') =
            k⁻¹ * (canonicalRep (coxeterSystem τ) L x *
              canonicalRep (coxeterSystem τ) L x') := by
          rw [hkk]
          group
        show canonicalRep (coxeterSystem τ) L (x * x') ∈ Mχ
        rw [hmul]
        exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) (mul_mem hx hx')
      one_mem' := by
        show canonicalRep (coxeterSystem τ) L 1 ∈ Mχ
        rw [canonicalRep_one]
        exact one_mem _
      inv_mem' := fun {x} hx => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := τ) (R := L) x x⁻¹
        rw [mul_inv_cancel, canonicalRep_one, mul_one] at hkk
        have hinv : canonicalRep (coxeterSystem τ) L x⁻¹ =
            (canonicalRep (coxeterSystem τ) L x)⁻¹ * k := by
          rw [← hkk]
          group
        show canonicalRep (coxeterSystem τ) L x⁻¹ ∈ Mχ
        rw [hinv]
        exact mul_mem (inv_mem hx) (Subgroup.mem_sup_left hk) }
  have hgen : ∀ r ∈ (fun α => rootReflection α) '' kernelRoots χ, r ∈ R := by
    rintro r ⟨α, hα, rfl⟩
    show canonicalRep (coxeterSystem τ) L (rootReflection α) ∈ Mχ
    have hn := canonicalRep_rootReflection_mem (τ := τ) (K := L) hα.1
    have hsub : rootSubgroup τ L α ⊔ rootSubgroup τ L (-α) ≤ Mχ :=
      sup_le ((rootSubgroup_le_rootSpan (τ := τ) (K := L) hα).trans le_sup_right)
        ((rootSubgroup_le_rootSpan (τ := τ) (K := L) (neg_mem_kernelRoots hα)).trans
          le_sup_right)
    exact (sup_le le_sup_left hsub) hn
  exact (Subgroup.closure_le R).2 (fun r hr => hgen r hr) hy

section Lang

variable {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]

theorem entrywiseFrobGL_mem_torus_sup_rootSpan (e : ℕ) {S : Set (Fin τ.rank → ℤ)}
    {g : ModGL τ L} (hg : g ∈ torusGroup τ L ⊔ rootSpan τ L S) :
    entrywiseFrobGL τ L ℓ e g ∈ torusGroup τ L ⊔ rootSpan τ L S := by
  have hmap : (torusGroup τ L ⊔ rootSpan τ L S).map (entrywiseFrobGL τ L ℓ e) ≤
      torusGroup τ L ⊔ rootSpan τ L S := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      rw [entrywiseFrobGL_rootDiagUnit_eq_map]
      exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup _)
    · rw [rootSpan, Subgroup.map_iSup]
      refine iSup_le fun α => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hα => ?_
      rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      exact Subgroup.mem_sup_right (le_iSup₂_of_le (f := fun β (_ : β ∈ S) =>
        rootSubgroup τ L β) α hα le_rfl (Subgroup.subset_closure
          ⟨iterateFrobenius L ℓ e c, (entrywiseFrobGL_pinnedX ℓ e α c).symm⟩))
  exact hmap ⟨g, hg, rfl⟩

theorem lang_torus_sup_rootSpan (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (e : ℕ)
    (he : 1 ≤ e) : ∀ c ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ),
      ∃ z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ),
        z⁻¹ * entrywiseFrobGL τ L ℓ e z = c := by
  have hZ : IsConnectedAlgebraicSubgroup L
      ((torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ)).map (modGLPoint τ L).toMonoidHom) :=
    isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots (τ := τ) (k := L) χ
  have hst : ∀ g ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ),
      frobTwistGL τ L ℓ e 1 g ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) := fun g hg => by
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    exact entrywiseFrobGL_mem_torus_sup_rootSpan ℓ e hg
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction ℓ hZ he 1 hst
  intro c hc
  obtain ⟨z, hz, hzc⟩ := hlang c hc
  exact ⟨z, hz, by rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hzc; exact hzc⟩

end Lang

theorem pow_card_sub_one_eq_one_of_mem_torusGroup {K : Type} [Field K] [Finite K]
    {t : ModGL τ K} (ht : t ∈ torusGroup τ K) : t ^ (Nat.card K - 1) = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hl : l ^ (Nat.card K - 1) = 1 := by
    funext i
    refine Units.ext ?_
    rw [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply, Units.val_one,
      Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero _)
  have e := map_pow (rootDiagUnitHom τ K) l (Nat.card K - 1)
  rw [hl, map_one] at e
  exact e.symm

theorem mem_rootSpan_of_mem_torus_sup_of_pow_eq_one {K : Type} [Field K] [Finite K]
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) {n : ℕ}
    (hn : Nat.Coprime n (Nat.card K - 1)) {x : ModGL τ K}
    (hx : x ∈ torusGroup τ K ⊔ rootSpan τ K S) (hxn : x ^ n = 1) : x ∈ rootSpan τ K S := by
  have hN := torusGroup_le_normalizer_rootSpan (K := K) hS
  have hx' : x ∈ (torusGroup τ K : Set (ModGL τ K)) * (rootSpan τ K S : Set (ModGL τ K)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN]
    exact hx
  obtain ⟨t, ht, r, hr, rfl⟩ := hx'
  have hconj : ∀ r' ∈ rootSpan τ K S, t⁻¹ * r' * t ∈ rootSpan τ K S := fun r' hr' => by
    have h := (Subgroup.mem_normalizer_iff.1 (inv_mem (hN ht)) r').1 hr'
    rwa [inv_inv] at h
  have hpow : ∀ k : ℕ, ∃ r' ∈ rootSpan τ K S, (t * r) ^ k = t ^ k * r' := by
    intro k
    induction k with
    | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, one_mul]⟩
    | succ k ih =>
      obtain ⟨r', hr', e⟩ := ih
      refine ⟨t⁻¹ * r' * t * r, mul_mem (hconj r' hr') hr, ?_⟩
      rw [pow_succ, e, pow_succ]
      group
  obtain ⟨r', hr', e⟩ := hpow n
  have htn : t ^ n ∈ rootSpan τ K S := by
    rw [hxn] at e
    have : t ^ n = r'⁻¹ := eq_inv_of_mul_eq_one_left e.symm
    rw [this]
    exact inv_mem hr'
  have htq : t ^ (Nat.card K - 1) = 1 := pow_card_sub_one_eq_one_of_mem_torusGroup ht
  have hAB : (n : ℤ) * Nat.gcdA n (Nat.card K - 1) +
      ((Nat.card K - 1 : ℕ) : ℤ) * Nat.gcdB n (Nat.card K - 1) = 1 := by
    have h := Nat.gcd_eq_gcd_ab n (Nat.card K - 1)
    rw [hn.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  have ht' : t ∈ rootSpan τ K S := by
    have heq : t = (t ^ n) ^ Nat.gcdA n (Nat.card K - 1) *
        (t ^ (Nat.card K - 1)) ^ Nat.gcdB n (Nat.card K - 1) := by
      rw [← zpow_natCast t n, ← zpow_natCast t (Nat.card K - 1), ← zpow_mul, ← zpow_mul,
        ← zpow_add, hAB, zpow_one]
    rw [heq, htq, one_zpow, mul_one]
    exact Subgroup.zpow_mem _ htn _
  exact mul_mem ht' hr

end CFSG.LieType.AlgebraicGroups
