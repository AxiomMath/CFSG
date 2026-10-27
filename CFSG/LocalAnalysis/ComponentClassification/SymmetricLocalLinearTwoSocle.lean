module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoAutomorphism
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalSocleSelector

public noncomputable section

namespace CFSG.ComponentClassification.SymmetricLocal

open Equiv Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section Extension

theorem linear_two_socle_extension {A : Type*} [Group A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {K : Type} [Field K] [Finite K]
    (φ : W ≃* coordinateG K) :
    ∃ ρ : A →* coordinateE K, Function.Injective ρ ∧
      (∀ w : W, (ρ w : Perm (Omega K)) = φ w) ∧
      (∀ ρ' : A →* coordinateE K, (∀ w : W, (ρ' w : Perm (Omega K)) = φ w) → ρ' = ρ) ∧
      (∀ (g : A) (w : W), (ρ g : Perm (Omega K)) * φ w * (ρ g : Perm (Omega K))⁻¹ =
        φ (MulAut.conjNormal g w)) ∧
      (∀ (g : A) (w : W), MulAut.conjNormal g = MulAut.conj w →
        (ρ g : Perm (Omega K)) = φ w) := by
  obtain ⟨c, hc, hcG, -⟩ :=
    LocalAnalysis.ComponentInitial.UnitaryHigher.linear_two_automorphism_semilinear_isomorphism K
  set α : A →* MulAut (coordinateG K) :=
    (MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal with hα
  set ρ : A →* coordinateE K := c.symm.toMonoidHom.comp α with hρ
  have hcρ : ∀ g, c (ρ g) = α g := fun g => c.apply_symm_apply (α g)
  have hαapp : ∀ (g : A) (y : coordinateG K),
      α g y = φ (MulAut.conjNormal g (φ.symm y)) := fun _ _ => rfl
  have hconj : ∀ (g : A) (w : W), (ρ g : Perm (Omega K)) * φ w * (ρ g : Perm (Omega K))⁻¹ =
      φ (MulAut.conjNormal g w) := by
    intro g w
    have h := hc (ρ g) (φ w)
    rw [hcρ, hαapp, MulEquiv.symm_apply_apply] at h
    exact h.symm
  have hαW : ∀ w : W, α (w : A) = MulAut.conj (φ w) := by
    intro w
    ext y
    rw [hαapp, MulAut.conj_apply]
    have h : MulAut.conjNormal (w : A) (φ.symm y) = w * φ.symm y * w⁻¹ := Subtype.ext rfl
    rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hρW : ∀ w : W, (ρ w : Perm (Omega K)) = φ w := by
    intro w
    have h1 : c (ρ w) = c ⟨φ w, (coordinateG_le_D K).trans (coordinateD_le_E K) (φ w).2⟩ := by
      rw [hcρ, hαW, hcG]
    exact congrArg Subtype.val (c.injective h1)
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hα1 : α g = 1 := by rw [← hcρ, hg, map_one]
    have hgW : g ∈ centralizer (W : Set A) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun χ : MulAut (coordinateG K) => χ (φ ⟨x, hx⟩)) hα1
      simp only [MulAut.one_apply] at h
      rw [hαapp, MulEquiv.symm_apply_apply] at h
      have h3 : g * x * g⁻¹ = x := by
        simpa only [MulAut.conjNormal_apply] using congrArg Subtype.val (φ.injective h)
      calc x * g = g * x * g⁻¹ * g := by rw [h3]
        _ = g * x := by group
    rw [hCW] at hgW
    exact hgW
  have huniq : ∀ ρ' : A →* coordinateE K, (∀ w : W, (ρ' w : Perm (Omega K)) = φ w) →
      ρ' = ρ := by
    intro ρ' hρ'
    refine MonoidHom.ext fun g => c.injective (MulEquiv.ext fun y => Subtype.ext ?_)
    rw [hc, hc]
    obtain ⟨w, rfl⟩ := φ.surjective y
    rw [hconj]
    have h := hρ' (MulAut.conjNormal g w)
    rw [show ((MulAut.conjNormal g w : W) : A) = g * w * g⁻¹ from rfl, map_mul, map_mul,
      map_inv] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hρ'] using h
  have houter : ∀ (g : A) (w : W), MulAut.conjNormal g = MulAut.conj w →
      (ρ g : Perm (Omega K)) = φ w := by
    intro g w h
    have h1 : α g = α (w : A) := by
      change MulAut.congr φ (MulAut.conjNormal g) = MulAut.congr φ (MulAut.conjNormal (w : A))
      rw [h, MulAut.conjNormal_val]
    have h2 : ρ g = ρ w := c.injective (by rw [hcρ, hcρ, h1])
    rw [h2, hρW]
  exact ⟨ρ, hinj, hρW, huniq, hconj, houter⟩

end Extension

section Generic

theorem isComponent_eq_of_simple_normal {D : Type*} [Group D] [Finite D] (G' : Subgroup D)
    [G'.Normal] (hab : IsMulCommutative (D ⧸ G')) (hsimple : IsSimpleGroup G')
    {M : Subgroup D} (hM : CFSG.IsComponent M) : M = G' := by
  have : Group.IsPerfect M := hM.1.1
  have hMG : M ≤ G' := by
    intro x hx
    have h1 := PerfectAutomorphisms.hom_eq_one_of_commutative
      ((QuotientGroup.mk' G').comp M.subtype)
    have h2 := DFunLike.congr_fun h1 ⟨x, hx⟩
    simpa [QuotientGroup.eq_one_iff] using h2
  have hcomp := LocalAnalysis.ComponentInitial.component_overgroup hM hMG
  have hnt : Nontrivial (M.subgroupOf G') := CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
  rcases hcomp.2.eq_bot_or_top_of_isSimpleGroup hsimple with h | h
  · exact absurd h ((M.subgroupOf G').nontrivial_iff_ne_bot.mp hnt)
  · exact le_antisymm hMG (Subgroup.subgroupOf_eq_top.mp h)

theorem isComponent_comap_of_isComponentOf_range {D P : Type*} [Group D] [Group P] (f : D →* P)
    (hf : Function.Injective f) {X : Subgroup P} (hX : CFSG.Assembly.IsComponentOf X f.range) :
    CFSG.IsComponent (X.comap f) ∧ (X.comap f).map f = X := by
  have hX' := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hX.1).mp hX
  have hEq : (X.subgroupOf f.range).map (MonoidHom.ofInjective hf).symm.toMonoidHom =
      X.comap f := by
    ext y
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf, Subgroup.mem_comap,
      MonoidHom.ofInjective_apply]
  refine ⟨?_, Subgroup.map_comap_eq_self hX.1⟩
  rw [← hEq]
  exact LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent _ hX'

theorem coordinateD_isSolvable_of_card_le_three {k : Type*} [Field k] [Finite k]
    (hk : Nat.card k ≤ 3) : Group.IsSolvable (coordinateD k) := by
  have : Group.IsSolvable (Perm (Omega k)) := Equiv.Perm.isSolvable (by
    rw [Finite.card_option]
    omega)
  exact Group.isSolvable_of_isSolvable_injective (f := (coordinateD k).subtype)
    Subtype.val_injective

theorem coordinateG_isSimpleGroup_of_four_le {k : Type*} [Field k] [Finite k]
    (hk : 4 ≤ Nat.card k) : IsSimpleGroup (coordinateG k) := by
  have := Fintype.ofFinite k
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset k)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hk)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) :=
    (CFSG.LinearGroups.linear_projective_simple (K := k) (n := 2) le_rfl (Or.inr ⟨t, ht⟩)).2.1
  exact (pslEquivCoordinateG k).symm.isSimpleGroup

end Generic

section Involutions

open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField mem_fixedField_iff
  subfieldCoordinateImage)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog (subfieldGImage)
open CFSG.Wreathed.CentralSL2 (fieldPerm fieldPerm_apply)
open CFSG.Semidihedral.SemilinearOuterQuotient (fieldProjection linearPart
  coordinate_decomposition_coe fieldProjection_ker)

variable {K : Type} [Field K] [Finite K]

theorem false_of_perfect_le_solvable {G : Type*} [Group G] {M N : Subgroup G}
    [Group.IsPerfect M] [Nontrivial M] (hN : Group.IsSolvable N) (hMN : M ≤ N) : False := by
  have : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hMN) (Subgroup.inclusion_injective hMN)
  exact Group.IsPerfect.not_isSolvable M this

theorem false_of_perfect_commute {G : Type*} [Group G] {M : Subgroup G} [Group.IsPerfect M]
    [Nontrivial M] (h : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) : False := by
  refine Group.IsPerfect.not_isMulCommutative M ?_
  exact isMulCommutative_iff.mpr fun a b => Subtype.ext (h a a.2 b b.2)

theorem linear_two_odd_involution_data {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (s : coordinateE K) (hs2 : orderOf s = 2)
    {M : Subgroup (Perm (Omega K))} [Group.IsPerfect M] [Nontrivial M]
    (hM : M ≤ coordinateG K ⊓ centralizer {(s : Perm (Omega K))}) :
    (s : Perm (Omega K)) ∉ coordinateD K ∧ Even e ∧
      ∃ σ : K ≃+* K, (∀ x, σ x = x ^ ℓ ^ (e / 2)) ∧ orderOf σ = 2 ∧
        ∃ d ∈ coordinateD K, (s : Perm (Omega K)) = d * fieldExtension K σ * d⁻¹ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := Fintype.ofFinite K
  have hchar : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hsq : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  have hsD : (s : Perm (Omega K)) ∉ coordinateD K := by
    intro hD
    set a : coordinateD K := ⟨s, hD⟩
    have hne : a ≠ 1 := by
      intro h
      have h' : (s : Perm (Omega K)) = 1 := congrArg Subtype.val h
      have hs1 : s = 1 := Subtype.ext h'
      rw [hs1, orderOf_one] at hs2
      exact absurd hs2 (by decide)
    have hasq : a ^ 2 = 1 := Subtype.ext (by
      change (s : Perm (Omega K)) ^ 2 = 1
      rw [← Subgroup.coe_pow, hsq, Subgroup.coe_one])
    have h2 : (2 : K) ≠ 0 := by
      intro h
      have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff K ℓ] at h2'
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h2')
    have hsolv := (CatalogueBLinearTwo.coordinate_involution_centralizer_structure K h2 a hne
      hasq).2.2.2
    have hMG : M.subgroupOf (coordinateG K) ≤
        (centralizer {a.val}).subgroupOf (coordinateG K) := by
      intro x hx
      exact (hM hx).2
    have : Group.IsPerfect (M.subgroupOf (coordinateG K)) := by
      have e := Subgroup.subgroupOfEquivOfLe (hM.trans inf_le_left)
      exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have : Nontrivial (M.subgroupOf (coordinateG K)) :=
      (Subgroup.subgroupOfEquivOfLe (hM.trans inf_le_left)).toEquiv.nontrivial
    exact false_of_perfect_le_solvable hsolv hMG
  have hτ : fieldProjection K s ≠ 1 := by
    intro h
    apply hsD
    have hker : s ∈ (fieldProjection K).ker := h
    rw [fieldProjection_ker] at hker
    exact hker
  have hsq' : (s : Perm (Omega K)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hsq, Subgroup.coe_one]
  obtain ⟨heven, hformula, -, d, hd⟩ :=
    CatalogueBLinearTwoDescent.quadratic_semilinear_involution_conjugacy_in_E K ℓ e hℓ
      (hℓ.odd_of_ne_two hℓ2) he hK s (linearPart K s) (fieldProjection K s) hτ
      (coordinate_decomposition_coe K s) hsq
  have hσsq := (CatalogueBLinearTwoDescent.coordinate_semilinear_square_data K (linearPart K s)
    (fieldProjection K s) (by rw [← coordinate_decomposition_coe K s]; exact hsq')).1
  have hσ2 : orderOf (fieldProjection K s) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hσsq hτ
  exact ⟨hsD, heven, fieldProjection K s, hformula, hσ2, d, d.2, hd⟩

theorem linear_two_even_involution_data {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ e)
    (s : coordinateE K) (hs2 : orderOf s = 2) {M : Subgroup (Perm (Omega K))}
    [Group.IsPerfect M] [Nontrivial M]
    (hM : M ≤ coordinateG K ⊓ centralizer {(s : Perm (Omega K))}) :
    (s : Perm (Omega K)) ∉ coordinateG K ∧ Even e ∧
      ∃ σ : K ≃+* K, (∀ x, σ x = x ^ 2 ^ (e / 2)) ∧ orderOf σ = 2 ∧
        ∃ d ∈ coordinateG K, (s : Perm (Omega K)) = d * fieldExtension K σ * d⁻¹ := by
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := e)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hcases⟩ :=
    LocalAnalysis.ComponentInitial.UnitaryHigher.even_linear_two_involution_normal_forms he hK
  have hs2' : orderOf (s : Perm (Omega K)) = 2 := by rw [Subgroup.orderOf_coe]; exact hs2
  rcases hcases s s.2 hs2' with ⟨-, h, hhG, hsh⟩ |
      ⟨hsG, heven, σ, hσ1, hσσ, hσx, -, -, ⟨h, hhG, hsh⟩, -⟩
  · exfalso
    have key : ∀ m ∈ M, ∃ b : K, h⁻¹ * m * h = translation K b := by
      intro m hm
      obtain ⟨hmG, hmc⟩ := Subgroup.mem_inf.mp (hM hm)
      have hmc' : m * s = s * m := Subgroup.mem_centralizer_singleton_iff.mp hmc
      have hconjG : h⁻¹ * m * h ∈ coordinateG K := mul_mem (mul_mem (inv_mem hhG) hmG) hhG
      have hconjc : h⁻¹ * m * h * translation K 1 = translation K 1 * (h⁻¹ * m * h) := by
        have hτ : translation K 1 = h⁻¹ * s * h := by rw [hsh]; group
        rw [hτ]
        calc h⁻¹ * m * h * (h⁻¹ * s * h) = h⁻¹ * (m * s) * h := by group
          _ = h⁻¹ * (s * m) * h := by rw [hmc']
          _ = h⁻¹ * s * h * (h⁻¹ * m * h) := by group
      obtain ⟨b, φ, hbφ⟩ := UnbalancedCatalog.EvenCatalog.mem_inf_centralizer_translation_one_iff.mp
        (Subgroup.mem_inf.mpr ⟨coordinateD_le_E K (coordinateG_le_D K hconjG),
          Subgroup.mem_centralizer_singleton_iff.mpr hconjc⟩)
      have hφG : fieldExtension K φ ∈ coordinateG K := by
        have h1 : fieldExtension K φ = (translation K b)⁻¹ * (h⁻¹ * m * h) := by
          rw [hbφ]; group
        rw [h1]
        exact mul_mem (inv_mem (CFSG.LinearGroups.translation_mem_coordinateG b)) hconjG
      rw [LocalAnalysis.ComponentInitial.UnitaryHigher.fieldExtension_mem_G_iff] at hφG
      subst hφG
      refine ⟨b, ?_⟩
      rw [hbφ, LocalAnalysis.ComponentInitial.UnitaryHigher.fieldExtension_one, mul_one]
    refine false_of_perfect_commute (M := M) fun x hx y hy => ?_
    obtain ⟨b, hb⟩ := key x hx
    obtain ⟨c, hc⟩ := key y hy
    have h1 : h⁻¹ * (x * y) * h = h⁻¹ * (y * x) * h := by
      calc h⁻¹ * (x * y) * h = (h⁻¹ * x * h) * (h⁻¹ * y * h) := by group
        _ = translation K b * translation K c := by rw [hb, hc]
        _ = translation K c * translation K b := by
          rw [UnbalancedCatalog.EvenCatalog.translation_mul_translation,
            UnbalancedCatalog.EvenCatalog.translation_mul_translation, add_comm]
        _ = (h⁻¹ * y * h) * (h⁻¹ * x * h) := by rw [hb, hc]
        _ = h⁻¹ * (y * x) * h := by group
    have h2 := congrArg (fun z => h * z * h⁻¹) h1
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h2
  · exact ⟨hsG, heven, σ, hσx, orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1, h, hhG, hsh⟩

theorem field_involution_centralizer_E (σ : K ≃+* K) (hσ : orderOf σ = 2) :
    coordinateE K ⊓ centralizer {fieldExtension K σ} =
      subfieldCoordinateImage K (fixedField K σ) ⊔ (fieldPerm K).range := by
  have hcyc : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have hD := CatalogueBLinearTwoFixed.subfieldCoordinateImage_eq_D_centralizer K σ hσ
  apply le_antisymm
  · intro x hx'
    obtain ⟨hxE, hx⟩ := Subgroup.mem_inf.mp hx'
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have hdec : x = (linearPart K ⟨x, hxE⟩ : Perm (Omega K)) *
        fieldExtension K (fieldProjection K ⟨x, hxE⟩) := coordinate_decomposition_coe K ⟨x, hxE⟩
    set y := linearPart K ⟨x, hxE⟩
    set τ := fieldProjection K ⟨x, hxE⟩
    have hy1 : (y : Perm (Omega K)) * fieldExtension K σ = fieldExtension K σ * y := by
      have h1 : (y : Perm (Omega K)) * fieldExtension K σ * fieldExtension K τ =
          fieldExtension K σ * y * fieldExtension K τ := by
        calc (y : Perm (Omega K)) * fieldExtension K σ * fieldExtension K τ =
            y * (fieldExtension K σ * fieldExtension K τ) := by group
          _ = y * (fieldExtension K τ * fieldExtension K σ) := by
            rw [UnbalancedCatalog.EvenCatalog.fieldExtension_commute hcyc σ τ]
          _ = (y * fieldExtension K τ) * fieldExtension K σ := by group
          _ = x * fieldExtension K σ := by rw [← hdec]
          _ = fieldExtension K σ * x := hx
          _ = fieldExtension K σ * y * fieldExtension K τ := by rw [hdec]; group
      exact mul_right_cancel h1
    have hyj : (y : Perm (Omega K)) ∈ subfieldCoordinateImage K (fixedField K σ) := by
      rw [hD]
      exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hy1⟩
    rw [hdec]
    exact mul_mem (Subgroup.mem_sup_left hyj) (Subgroup.mem_sup_right ⟨τ, fieldPerm_apply K τ⟩)
  · refine sup_le ?_ ?_
    · rw [hD]
      exact inf_le_inf_right _ (coordinateD_le_E K)
    · rintro _ ⟨τ, rfl⟩
      rw [fieldPerm_apply]
      exact Subgroup.mem_inf.mpr
        ⟨LocalAnalysis.ComponentInitial.UnitaryHigher.fieldExtension_mem_E τ,
          Subgroup.mem_centralizer_singleton_iff.mpr
            (UnbalancedCatalog.EvenCatalog.fieldExtension_commute hcyc τ σ)⟩

theorem fieldPerm_normalizes_subfieldCoordinateImage (σ : K ≃+* K) (hσ : orderOf σ = 2) :
    (∀ x ∈ (fieldPerm K).range, ∀ y ∈ subfieldCoordinateImage K (fixedField K σ),
      x * y * x⁻¹ ∈ subfieldCoordinateImage K (fixedField K σ)) ∧
      subfieldCoordinateImage K (fixedField K σ) ⊓ (fieldPerm K).range = ⊥ := by
  have hcyc : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have hD := CatalogueBLinearTwoFixed.subfieldCoordinateImage_eq_D_centralizer K σ hσ
  refine ⟨?_, ?_⟩
  · rintro _ ⟨τ, rfl⟩ y hy
    rw [hD] at hy ⊢
    obtain ⟨hyD, hyc⟩ := Subgroup.mem_inf.mp hy
    rw [fieldPerm_apply]
    have hτE := LocalAnalysis.ComponentInitial.UnitaryHigher.fieldExtension_mem_E (K := K) τ
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := (coordinateD_normal_in_E K).conj_mem ⟨y, coordinateD_le_E K hyD⟩
        (Subgroup.mem_subgroupOf.mpr hyD) ⟨_, hτE⟩
      exact Subgroup.mem_subgroupOf.mp h
    · have hτσ : Commute (fieldExtension K τ) (fieldExtension K σ) :=
        UnbalancedCatalog.EvenCatalog.fieldExtension_commute hcyc τ σ
      have hyσ : Commute y (fieldExtension K σ) := Subgroup.mem_centralizer_singleton_iff.mp hyc
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((hτσ.mul_left hyσ).mul_left hτσ.inv_left).eq
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxj, τ, rfl⟩ := Subgroup.mem_inf.mp hx
    rw [hD] at hxj
    have hτD := (Subgroup.mem_inf.mp hxj).1
    rw [fieldPerm_apply] at hτD
    have hτ1 := LocalAnalysis.ComponentInitial.UnitaryHigher.eq_one_of_fieldExtension_mem_D hτD
    rw [Subgroup.mem_bot, hτ1, map_one]

omit [Finite K] in
theorem fieldPerm_acts_by_restriction {r : ℕ} (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ r)
    (τ : K ≃+* K) : ∃ τk : fixedField K σ ≃+* fixedField K σ,
      (∀ x : fixedField K σ, (τk x : K) = τ x) ∧
      ∀ A : GL (Fin 2) (fixedField K σ),
        fieldExtension K τ *
            coordinateGLAction K (Matrix.GeneralLinearGroup.map (fixedField K σ).subtype A) *
            (fieldExtension K τ)⁻¹ =
          coordinateGLAction K (Matrix.GeneralLinearGroup.map (fixedField K σ).subtype
            (Matrix.GeneralLinearGroup.map τk.toRingHom A)) := by
  have hmem : ∀ (υ : K ≃+* K) (x : K), x ∈ fixedField K σ → υ x ∈ fixedField K σ := by
    intro υ x hx
    rw [mem_fixedField_iff] at hx ⊢
    rw [hσ] at hx ⊢
    rw [← map_pow, hx]
  let τk : fixedField K σ ≃+* fixedField K σ :=
    { toFun := fun x => ⟨τ x, hmem τ x x.2⟩
      invFun := fun x => ⟨τ.symm x, hmem τ.symm x x.2⟩
      left_inv := fun x => Subtype.ext (τ.symm_apply_apply (x : K))
      right_inv := fun x => Subtype.ext (τ.apply_symm_apply (x : K))
      map_mul' := fun x y => Subtype.ext (map_mul τ (x : K) y)
      map_add' := fun x y => Subtype.ext (map_add τ (x : K) y) }
  refine ⟨τk, fun x => rfl, fun A => ?_⟩
  rw [CFSG.Wreathed.CentralSL2.fieldExtension_conj_coordinateGLAction]
  congr 1

end Involutions

section Main

open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField mem_fixedField_iff
  subfieldCoordinateImage)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog (subfieldGImage)
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer (subfieldD)
open CFSG.Wreathed.CentralSL2 (fieldPerm fieldPerm_apply)
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial (conjSub conjSub_centralizer
  map_conj_centralizer_singleton conjSub_inv_conjSub conjSub_conjSub_inv)

theorem faithful_projective_linear_two_socle_involution_component_model
    {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (_hWsimple : IsSimpleGroup W) (_hWnonab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    {ℓ e : ℕ} [hℓ : Fact ℓ.Prime] (he : 1 ≤ e) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ e) (_hK4 : 4 ≤ ℓ ^ e) (φ : W ≃* coordinateG K) :
    Even e ∧ 4 ≤ ℓ ^ (e / 2) ∧
    ∃ σ : K ≃+* K, (∀ x, σ x = x ^ ℓ ^ (e / 2)) ∧ orderOf σ = 2 ∧
      Nat.card (fixedField K σ) = ℓ ^ (e / 2) ∧
    ∃ ρ : A →* coordinateE K, Function.Injective ρ ∧ (∀ w : W, (ρ w : Perm (Omega K)) = φ w) ∧
      (∀ ρ' : A →* coordinateE K, (∀ w : W, (ρ' w : Perm (Omega K)) = φ w) → ρ' = ρ) ∧
      coordinateG K ≤ ((coordinateE K).subtype.comp ρ).range ∧
      ∃ d ∈ coordinateD K, (ℓ = 2 → d ∈ coordinateG K) ∧
        Function.Injective (subfieldD (fixedField K σ)) ∧
        (ρ a : Perm (Omega K)) = d * fieldExtension K σ * d⁻¹ ∧
        (W ⊓ centralizer {a}).map ((coordinateE K).subtype.comp ρ) =
          conjSub d (subfieldCoordinateImage K (fixedField K σ)) ∧
        L.map ((coordinateE K).subtype.comp ρ) = conjSub d (subfieldGImage (fixedField K σ)) ∧
        (centralizer {a}).map ((coordinateE K).subtype.comp ρ) =
          ((coordinateE K).subtype.comp ρ).range ⊓
            conjSub d (subfieldCoordinateImage K (fixedField K σ) ⊔ (fieldPerm K).range) ∧
        (∀ x ∈ (fieldPerm K).range, ∀ y ∈ subfieldCoordinateImage K (fixedField K σ),
          x * y * x⁻¹ ∈ subfieldCoordinateImage K (fixedField K σ)) ∧
        subfieldCoordinateImage K (fixedField K σ) ⊓ (fieldPerm K).range = ⊥ ∧
        (∀ τ : K ≃+* K, ∃ τk : fixedField K σ ≃+* fixedField K σ,
          (∀ x : fixedField K σ, (τk x : K) = τ x) ∧ ∀ A : GL (Fin 2) (fixedField K σ),
            fieldExtension K τ *
                coordinateGLAction K (Matrix.GeneralLinearGroup.map (fixedField K σ).subtype A) *
                (fieldExtension K τ)⁻¹ =
              coordinateGLAction K (Matrix.GeneralLinearGroup.map (fixedField K σ).subtype
                (Matrix.GeneralLinearGroup.map τk.toRingHom A))) ∧
        IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧ center L = ⊥ ∧
        StatedClassicalModel L .PSL 2 ℓ (e / 2) ∧
        Assembly.ComponentType.ClassicalModel L .PSL 2 ℓ (e / 2) ∧
        (∃ θ : L ≃* coordinateG (fixedField K σ), ∀ l : L,
          (subfieldD (fixedField K σ) ⟨θ l, coordinateG_le_D _ (θ l).2⟩ : Perm (Omega K)) =
            d⁻¹ * φ ⟨l, hLW l.2⟩ * d) ∧
        centralizer (L : Set A) = zpowers a ∧
        MulAut.conjNormal a ∉ (MulAut.conj : W →* MulAut W).range ∧
        (ℓ ≠ 2 → coordinateG K ⊓ centralizer {fieldExtension K σ} =
            subfieldCoordinateImage K (fixedField K σ) ∧
          subfieldCoordinateImage K (fixedField K σ) ≤ coordinateG K ∧
          Nonempty (CFSG.GorensteinWalter.PGL2 (fixedField K σ) ≃*
            ↥(coordinateG K ⊓ centralizer {fieldExtension K σ}))) ∧
        (ℓ = 2 → coordinateD (fixedField K σ) = coordinateG (fixedField K σ)) ∧
        Nat.card K ≠ 4 ∧ Nat.card K ≠ 9 := by
  have hℓp : ℓ.Prime := hℓ.out
  obtain ⟨ρ, hinj, hρW, huniq, -, houter⟩ := linear_two_socle_extension hCW φ
  set ρ' : A →* Perm (Omega K) := (coordinateE K).subtype.comp ρ with hρ'
  have hinj' : Function.Injective ρ' := Subtype.val_injective.comp hinj
  have hρ'W : ∀ w : W, ρ' w = φ w := hρW
  have hWimage : W.map ρ' = coordinateG K := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [show w = ((⟨w, hw⟩ : W) : A) from rfl, hρ'W]
      exact (φ _).2
    · intro hy
      refine ⟨(φ.symm ⟨y, hy⟩ : A), (φ.symm ⟨y, hy⟩).2, ?_⟩
      rw [hρ'W, MulEquiv.apply_symm_apply]
  have hGT : coordinateG K ≤ ρ'.range := hWimage ▸ Subgroup.map_le_range ρ' W
  have hTE : ρ'.range ≤ coordinateE K := by
    rintro _ ⟨g, rfl⟩
    exact (ρ g).2
  set s : coordinateE K := ρ a with hsdef
  have hs2 : orderOf s = 2 := by rw [orderOf_injective ρ hinj a]; exact ha
  have hρ'a : ρ' a = (s : Perm (Omega K)) := rfl
  have hLCW : L ≤ W ⊓ centralizer {a} := le_inf hLW hL.1
  have hLperf : Group.IsPerfect L := ⟨hL.2.2.1⟩
  have : IsSimpleGroup (L ⧸ center L) := hL.2.2.2
  have hLnt : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  set M := L.map ρ' with hMdef
  have hMperf : Group.IsPerfect M := Group.IsPerfect.ofSurjective
    (f := (L.equivMapOfInjective ρ' hinj').toMonoidHom) (L.equivMapOfInjective ρ' hinj').surjective
  have hMnt : Nontrivial M := (L.equivMapOfInjective ρ' hinj').symm.toEquiv.nontrivial
  have hMle : M ≤ coordinateG K ⊓ centralizer {(s : Perm (Omega K))} := by
    rintro _ ⟨l, hl, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [show l = ((⟨l, hLW hl⟩ : W) : A) from rfl, hρ'W]
      exact (φ _).2
    · rw [Subgroup.mem_centralizer_singleton_iff, ← hρ'a, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp (hL.1 hl)]
  obtain ⟨hsG, heven, σ, hσx, hσ2, d, hdD, hdG, hsd⟩ : (s : Perm (Omega K)) ∉ coordinateG K ∧
      Even e ∧ ∃ σ : K ≃+* K, (∀ x, σ x = x ^ ℓ ^ (e / 2)) ∧ orderOf σ = 2 ∧
        ∃ d ∈ coordinateD K, (ℓ = 2 → d ∈ coordinateG K) ∧
          (s : Perm (Omega K)) = d * fieldExtension K σ * d⁻¹ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      obtain ⟨hsG, heven, σ, hσx, hσ2, d, hdG, hsd⟩ :=
        linear_two_even_involution_data he hK s hs2 hMle
      exact ⟨hsG, heven, σ, hσx, hσ2, d, coordinateG_le_D K hdG, fun _ => hdG, hsd⟩
    · obtain ⟨hsD, heven, σ, hσx, hσ2, d, hdD, hsd⟩ :=
        linear_two_odd_involution_data hℓp hℓ2 he hK s hs2 hMle
      exact ⟨fun h => hsD (coordinateG_le_D K h), heven, σ, hσx, hσ2, d, hdD,
        fun h => absurd h hℓ2, hsd⟩
  set g := e / 2 with hgdef
  have he2 : e = 2 * g := (Nat.two_mul_div_two_of_even heven).symm
  have hg : 1 ≤ g := by omega
  have hK2 : Nat.card K = ℓ ^ (2 * g) := by rw [← he2]; exact hK
  set k := fixedField K σ with hkdef
  obtain ⟨-, hjinj, -, hkcard, hpoint⟩ :=
    UnbalancedGS.quadratic_projective_linear_two_subfield_pointwise_centralizer hℓp hg hK2 σ hσx
      k (fun x => mem_fixedField_iff K σ x)
  have hDfix := CatalogueBLinearTwoFixed.subfieldCoordinateImage_eq_D_centralizer K σ hσ2
  have hEfix := field_involution_centralizer_E σ hσ2
  obtain ⟨hFnorm, hFinter⟩ := fieldPerm_normalizes_subfieldCoordinateImage σ hσ2
  have hGfix : coordinateG K ⊓ centralizer {fieldExtension K σ} =
      subfieldCoordinateImage K k ∧ subfieldCoordinateImage K k ≤ coordinateG K := by
    by_cases hℓ2 : ℓ = 2
    · have hK2' : Nat.card K = 2 ^ e := by rw [← hℓ2]; exact hK
      have hDG : coordinateD K = coordinateG K :=
        (LocalAnalysis.ComponentInitial.UnitaryHigher.even_linear_two_involution_normal_forms he
          hK2').1
      rw [hDfix, hDG]
      exact ⟨rfl, inf_le_left⟩
    · have := Fintype.ofFinite K
      have hchar : CharP K ℓ :=
        charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
      have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
      exact ⟨(CatalogueBLinearTwoFixed.subfieldCoordinateImage_eq_G_centralizer K hodd σ
        hσ2).symm, CatalogueBLinearTwoFixed.subfieldCoordinateImage_le_G K hodd σ hσ2⟩
  have hdE : d ∈ coordinateE K := coordinateD_le_E K hdD
  have hconjN : ∀ {N : Subgroup (Perm (Omega K))}, N ≤ coordinateE K →
      ((N.subgroupOf (coordinateE K)).Normal) → conjSub d N = N := by
    intro N hNE hN
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have h := hN.conj_mem ⟨x, hNE hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨d, hdE⟩
      exact Subgroup.mem_subgroupOf.mp h
    · intro x hx
      have h := hN.conj_mem ⟨x, hNE hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨d⁻¹, inv_mem hdE⟩
      have h' : d⁻¹ * x * d ∈ N := by
        have h'' := Subgroup.mem_subgroupOf.mp h
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using h''
      refine Subgroup.mem_map.mpr ⟨d⁻¹ * x * d, h', ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hconjG : conjSub d (coordinateG K) = coordinateG K :=
    hconjN ((coordinateG_le_D K).trans (coordinateD_le_E K)) (coordinateG_normal_in_E K)
  have hconjE : conjSub d (coordinateE K) = coordinateE K := by
    refine hconjN le_rfl ?_
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hconj_inf : ∀ X Y : Subgroup (Perm (Omega K)),
      conjSub d (X ⊓ Y) = conjSub d X ⊓ conjSub d Y := fun X Y =>
    Subgroup.map_inf_eq X Y _ (MulAut.conj d).injective
  have hCs : centralizer {(s : Perm (Omega K))} = conjSub d (centralizer {fieldExtension K σ}) :=
    by rw [hsd, conjSub, map_conj_centralizer_singleton]
  have hCWimage : (W ⊓ centralizer {a}).map ρ' = conjSub d (subfieldCoordinateImage K k) := by
    rw [Subgroup.map_inf_eq _ _ _ hinj', hWimage, map_centralizer_singleton_of_injective ρ' hinj',
      hρ'a, ← inf_assoc, inf_eq_left.mpr hGT, hCs, ← hconjG, ← hconj_inf, hGfix.1]
  have hCAimage : (centralizer {a}).map ρ' =
      ρ'.range ⊓ conjSub d (subfieldCoordinateImage K k ⊔ (fieldPerm K).range) := by
    rw [map_centralizer_singleton_of_injective ρ' hinj', hρ'a, hCs, ← hEfix, hconj_inf, hconjE,
      ← inf_assoc, inf_eq_left.mpr hTE]
  have hLcomp : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}) :=
    LocalAnalysis.ComponentInitial.isComponentOf_of_le hL hLCW inf_le_right
  have hMcomp : CFSG.Assembly.IsComponentOf M (conjSub d (subfieldCoordinateImage K k)) := by
    have h := isComponentOf_map_of_injective ρ' hinj' hLcomp
    rwa [hCWimage] at h
  set M₀ := conjSub d⁻¹ M with hM₀def
  have hM₀comp : CFSG.Assembly.IsComponentOf M₀ (subfieldCoordinateImage K k) := by
    have h : CFSG.Assembly.IsComponentOf (conjSub d⁻¹ M)
        (conjSub d⁻¹ (conjSub d (subfieldCoordinateImage K k))) :=
      LocalAnalysis.ComponentInitial.isComponentOf_map_conj hMcomp d⁻¹
    rwa [conjSub_inv_conjSub] at h
  set j' : coordinateD k →* Perm (Omega K) := (coordinateD K).subtype.comp (subfieldD k) with hj'
  have hj'inj : Function.Injective j' := Subtype.val_injective.comp hjinj
  obtain ⟨hL₀, hL₀map⟩ := isComponent_comap_of_isComponentOf_range j' hj'inj hM₀comp
  have hk4 : 4 ≤ Nat.card k := by
    by_contra hk4
    have hsolv := coordinateD_isSolvable_of_card_le_three (k := k) (by omega)
    have : Group.IsPerfect (M₀.comap j') := hL₀.1.1
    have : Nontrivial (M₀.comap j') := CFSG.LocalCores.isQuasisimple_nontrivial hL₀.1
    have : Group.IsSolvable (M₀.comap j') := Group.isSolvable_of_isSolvable_injective
      (f := (M₀.comap j').subtype) Subtype.val_injective
    exact Group.IsPerfect.not_isSolvable (M₀.comap j') this
  have hq4 : 4 ≤ ℓ ^ g := hkcard ▸ hk4
  have hksimple : IsSimpleGroup (coordinateG k) := coordinateG_isSimpleGroup_of_four_le hk4
  set Gk' := (coordinateG k).subgroupOf (coordinateD k) with hGk'
  have hGksimple : IsSimpleGroup Gk' :=
    (Subgroup.subgroupOfEquivOfLe (coordinateG_le_D k)).isSimpleGroup
  have hL₀eq : M₀.comap j' = Gk' :=
    isComponent_eq_of_simple_normal _ (coordinateDG_isMulCommutative k) hGksimple hL₀
  have hM₀eq : M₀ = Gk'.map j' := by rw [← hL₀map, hL₀eq]
  have hLimage : M = conjSub d (subfieldGImage k) := by
    change M = conjSub d (Gk'.map j')
    rw [← hM₀eq, hM₀def, conjSub_conjSub_inv]
  let e1 : L ≃* M := L.equivMapOfInjective ρ' hinj'
  let e2 : M ≃* M₀ :=
    M.equivMapOfInjective (MulAut.conj d⁻¹).toMonoidHom (MulAut.conj d⁻¹).injective
  let e3 : M₀ ≃* Gk'.map j' := MulEquiv.subgroupCongr hM₀eq
  let e4 : Gk'.map j' ≃* Gk' := (Gk'.equivMapOfInjective j' hj'inj).symm
  let e5 : Gk' ≃* coordinateG k := Subgroup.subgroupOfEquivOfLe (coordinateG_le_D k)
  let θ : L ≃* coordinateG k := e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have hθ : ∀ l : L, (subfieldD k ⟨θ l, coordinateG_le_D _ (θ l).2⟩ : Perm (Omega K)) =
      d⁻¹ * φ ⟨l, hLW l.2⟩ * d := by
    intro l
    have h2 := congrArg Subtype.val ((Gk'.equivMapOfInjective j' hj'inj).apply_symm_apply
      (e3 (e2 (e1 l))))
    rw [Subgroup.coe_equivMapOfInjective_apply] at h2
    have h3 : (⟨θ l, coordinateG_le_D _ (θ l).2⟩ : coordinateD k) =
        ((e4 (e3 (e2 (e1 l))) : Gk') : coordinateD k) := Subtype.ext rfl
    rw [h3]
    change j' _ = _
    rw [h2]
    change d⁻¹ * ρ' l * d⁻¹⁻¹ = _
    rw [inv_inv]
    exact congrArg (fun x => d⁻¹ * x * d) (hρ'W ⟨l, hLW l.2⟩)
  have hpoint' : centralizer (subfieldGImage k : Set (Perm (Omega K))) ⊓ coordinateE K =
      zpowers (fieldExtension K σ) := hpoint
  have hcent : centralizer (L : Set A) = zpowers a := by
    apply Subgroup.map_injective hinj'
    have h1 : ρ'.range ⊓ conjSub d (centralizer (subfieldGImage k : Set (Perm (Omega K)))) =
        ρ'.range ⊓ conjSub d (centralizer (subfieldGImage k : Set (Perm (Omega K))) ⊓
          coordinateE K) := by
      rw [hconj_inf, hconjE, inf_comm (conjSub d _) (coordinateE K), ← inf_assoc,
        inf_eq_left.mpr hTE]
    have hzs : conjSub d (zpowers (fieldExtension K σ)) = zpowers (s : Perm (Omega K)) := by
      rw [conjSub, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hsd]
    rw [map_centralizer_of_injective ρ' hinj', ← hMdef, hLimage, ← conjSub_centralizer,
      MonoidHom.map_zpowers, hρ'a, h1, hpoint', hzs]
    exact inf_eq_right.mpr (Subgroup.zpowers_le.mpr ⟨a, rfl⟩)
  have houter' : MulAut.conjNormal a ∉ (MulAut.conj : W →* MulAut W).range := by
    rintro ⟨w, hw⟩
    apply hsG
    rw [houter a w hw.symm]
    exact (φ w).2
  have hLsimple : IsSimpleGroup L := θ.isSimpleGroup
  have hLnonab : ∃ x y : L, x * y ≠ y * x := by
    by_contra h
    exact false_of_perfect_commute (M := L) fun x hx y hy => congrArg Subtype.val
      (not_not.mp fun hne => h ⟨⟨x, hx⟩, ⟨y, hy⟩, hne⟩)
  have hZL : center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center L) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hLnonab
      have hx : x ∈ center L := h ▸ Subgroup.mem_top x
      exact hxy (Subgroup.mem_center_iff.mp hx y).symm
  have hstated : StatedClassicalModel L .PSL 2 ℓ g := by
    refine ⟨⟨hℓp, hg, le_rfl, ?_, ?_⟩, k, inferInstance, inferInstance, hkcard,
      ⟨θ.trans ((pslEquivCoordinateG k).symm.trans
        (projectiveSpecialLinearGroupEquivStatedProj 2 k))⟩⟩
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
  have hassembly : Assembly.ComponentType.ClassicalModel L .PSL 2 ℓ g := by
    refine ⟨⟨hℓp, hg, le_rfl, ?_⟩, ⟨θ.trans ((pslEquivCoordinateG k).symm.trans
      ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
        (CFSG.ClassicalModels.finiteFieldEquivGaloisField k ℓ g hg hkcard) (Fin 2)).trans
        ((projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField ℓ g)).trans
          (ClassicalModelStatedBridge.pslModelEquiv 2 ℓ g).symm)))⟩⟩
    rintro ⟨-, h | h⟩ <;> omega
  have hodd_clause : ℓ ≠ 2 → coordinateG K ⊓ centralizer {fieldExtension K σ} =
      subfieldCoordinateImage K k ∧ subfieldCoordinateImage K k ≤ coordinateG K ∧
      Nonempty (CFSG.GorensteinWalter.PGL2 k ≃*
        ↥(coordinateG K ⊓ centralizer {fieldExtension K σ})) := by
    intro hℓ2
    have := Fintype.ofFinite K
    have hchar : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
    exact ⟨hGfix.1, hGfix.2, ⟨(pglEquivCoordinateD k).trans
      (CatalogueBLinearTwoFixed.subfieldCoordinateEquivGCentralizer K hodd σ hσ2)⟩⟩
  have heven_clause : ℓ = 2 → coordinateD k = coordinateG k := by
    intro hℓ2
    have := Fintype.ofFinite k
    have : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := g)
      (by rw [← Nat.card_eq_fintype_card, hkcard, hℓ2])
    exact LocalAnalysis.ComponentInitial.UnitaryHigher.coordinateD_eq_G
  have hK16 : 16 ≤ Nat.card K := by
    rw [hK2, pow_mul']
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (ℓ ^ g) ^ 2 := Nat.pow_le_pow_left hq4 2
  exact ⟨heven, hq4, σ, hσx, hσ2, hkcard, ρ, hinj, hρW, huniq, hGT, d, hdD, hdG, hjinj, hsd,
    hCWimage, hLimage, hCAimage, hFnorm, hFinter, fun τ => fieldPerm_acts_by_restriction σ hσx τ,
    hLsimple, hLnonab, hZL, hstated, hassembly, ⟨θ, hθ⟩, hcent, houter', hodd_clause,
    heven_clause, by omega, by omega⟩

end Main

end CFSG.ComponentClassification.SymmetricLocal
