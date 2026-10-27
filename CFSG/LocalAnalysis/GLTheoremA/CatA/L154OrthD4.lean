module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace omegaGroup mem_omegaGroup)

section Twist

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def orthCoordFieldMap (σ : K ≃+* K) : (ι → K) ≃+ (ι → K) where
  toFun v i := σ (v i)
  invFun v i := σ.symm (v i)
  left_inv v := funext fun i => σ.symm_apply_apply (v i)
  right_inv v := funext fun i => σ.apply_symm_apply (v i)
  map_add' v w := funext fun i => map_add σ (v i) (w i)

theorem orthCoordFieldMap_apply (σ : K ≃+* K) (v : ι → K) (i : ι) :
    orthCoordFieldMap σ v i = σ (v i) := rfl

theorem orthCoordFieldMap_symm_apply (σ : K ≃+* K) (v : ι → K) (i : ι) :
    (orthCoordFieldMap σ).symm v i = σ.symm (v i) := rfl

theorem orthCoordFieldMap_symm_smul (σ : K ≃+* K) (c : K) (v : ι → K) :
    (orthCoordFieldMap σ).symm (c • v) = σ.symm c • (orthCoordFieldMap σ).symm v :=
  funext fun i => map_mul σ.symm c (v i)

@[expose] noncomputable def orthTwist (σ : K ≃+* K) : MulAut ((ι → K) ≃ₗ[K] (ι → K)) :=
  MulAut.congr (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) (glFieldAut ι K σ)

theorem orthTwist_toLinEquiv (σ : K ≃+* K) (A : GL ι K) :
    orthTwist σ (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A) =
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K (glFieldAut ι K σ A) := by
  show CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K ((glFieldAut ι K σ)
    ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A))) = _
  rw [MulEquiv.symm_apply_apply]

theorem orth_coe_glFieldAut (σ : K ≃+* K) (A : GL ι K) :
    ((glFieldAut ι K σ A : GL ι K) : Matrix ι ι K) = (A : Matrix ι ι K).map σ := rfl

theorem orthTwist_apply (σ : K ≃+* K) (X : (ι → K) ≃ₗ[K] (ι → K)) (v : ι → K) :
    orthTwist σ X v = orthCoordFieldMap σ (X ((orthCoordFieldMap σ).symm v)) := by
  obtain ⟨A, rfl⟩ := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective X
  rw [orthTwist_toLinEquiv, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, orth_coe_glFieldAut]
  funext i
  rw [orthCoordFieldMap_apply, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.map_apply, map_mul, orthCoordFieldMap_symm_apply, RingEquiv.apply_symm_apply]

theorem orthTwist_mul (σ τ : K ≃+* K) (X : (ι → K) ≃ₗ[K] (ι → K)) :
    orthTwist (σ * τ) X = orthTwist σ (orthTwist τ X) := by
  rw [orthTwist, orthTwist, orthTwist, map_mul, map_mul, MulAut.mul_apply]

theorem orthTwist_one (X : (ι → K) ≃ₗ[K] (ι → K)) : orthTwist (1 : K ≃+* K) X = X := by
  rw [orthTwist, map_one, map_one, MulAut.one_apply]

theorem orthTwist_three {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) (X : (ι → K) ≃ₗ[K] (ι → K)) :
    orthTwist σ (orthTwist σ (orthTwist σ X)) = X := by
  rw [← orthTwist_mul, ← orthTwist_mul, show σ * σ * σ = σ ^ 3 by rw [pow_succ, pow_two], hσ3,
    orthTwist_one]

theorem orth_toLinEquiv_of_map (σ : K ≃+* K) {A A' : GL ι K}
    (h : (A' : Matrix ι ι K) = (A : Matrix ι ι K).map σ) :
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A' =
      orthTwist σ (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K A) := by
  rw [orthTwist_toLinEquiv]
  congr 1
  exact Units.ext h

theorem finrank_commSpace_orthTwist [Finite K] (σ : K ≃+* K) (X : (ι → K) ≃ₗ[K] (ι → K)) :
    Module.finrank K (commSpace (orthTwist σ X)) = Module.finrank K (commSpace X) := by
  have hiff : ∀ a : ι → K, a ∈ commSpace (orthTwist σ X) ↔ (orthCoordFieldMap σ).symm a ∈ commSpace X := by
    intro a
    rw [mem_commSpace, mem_commSpace]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨(orthCoordFieldMap σ).symm v, ?_⟩
      rw [orthTwist_apply, map_sub, AddEquiv.symm_apply_apply]
    · rintro ⟨v, hv⟩
      refine ⟨orthCoordFieldMap σ v, ?_⟩
      rw [orthTwist_apply, AddEquiv.symm_apply_apply, ← map_sub, hv, AddEquiv.apply_symm_apply]
  have hcard : Nat.card (commSpace (orthTwist σ X)) = Nat.card (commSpace X) :=
    Nat.card_congr ((orthCoordFieldMap σ).symm.toEquiv.subtypeEquiv hiff)
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(commSpace (orthTwist σ X))),
    Module.natCard_eq_pow_finrank (K := K) (V := ↥(commSpace X))] at hcard
  exact Nat.pow_right_injective (Finite.one_lt_card (α := K)) hcard

end Twist

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace omegaGroup mem_omegaGroup)
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply polar_quadPlus)
open Polynomial QuadraticMap

section PlusTwist

variable {K : Type} [Field K] {n : ℕ}

theorem quadPlus_orthCoordFieldMap (σ : K ≃+* K) (v : Fin n ⊕ Fin n → K) :
    quadPlus n K (orthCoordFieldMap σ v) = σ (quadPlus n K v) := by
  rw [quadPlus_apply, quadPlus_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [orthCoordFieldMap_apply, orthCoordFieldMap_apply, map_mul]

theorem quadPlus_orthCoordFieldMap_symm (σ : K ≃+* K) (v : Fin n ⊕ Fin n → K) :
    quadPlus n K ((orthCoordFieldMap σ).symm v) = σ.symm (quadPlus n K v) := by
  rw [quadPlus_apply, quadPlus_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [orthCoordFieldMap_symm_apply, orthCoordFieldMap_symm_apply, map_mul]

theorem orthTwist_mem_orthogonalGroup (σ : K ≃+* K) {X : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hX : X ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)) :
    orthTwist σ X ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hX ⊢
  intro v
  rw [orthTwist_apply, quadPlus_orthCoordFieldMap, hX, quadPlus_orthCoordFieldMap_symm,
    RingEquiv.apply_symm_apply]

theorem orth_quadPlus_single (j : Fin n ⊕ Fin n) : quadPlus n K (Pi.single j 1) = 0 := by
  rw [quadPlus_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases j with j | j <;> simp [Pi.single_apply]

theorem orth_polar_quadPlus_single (i : Fin n) :
    polar (quadPlus n K) (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr i) 1) = 1 := by
  rw [polar_quadPlus, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

end PlusTwist

section FixedSemilinear

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  {x : (Fin d → K) ≃ₗ[K] (Fin d → K)}

theorem orth_sub_mem_fixedSpace (hx : OddOrderIsometry Q p x) {k : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hk : k ∈ supportedBlock Q x (X - 1)) (v : Fin d → K) : k v - v ∈ fixedSpace x := by
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
  have hkr : k r = r := (mem_supportedBlock.mp hk).2 r hr
  have hkw : k w ∈ fixedSpace x := mem_fixedSpace_of_apply (supportedBlock_le_centralizer _ hk) hw
  rw [map_add, hkr, add_sub_add_right_eq_sub]
  exact Submodule.sub_mem _ hkw hw

theorem orth_semilinear_mem_fixedSpace (hx : OddOrderIsometry Q p x) (g : coordinateSemilinearGroup d K)
    (hstab : ∀ ω ∈ supportedFixedDerived Q x, orthSemiConj g ω ∈ supportedFixedDerived Q x)
    {e f : Fin d → K} (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) (heW : e ∈ fixedSpace x)
    (hfW : f ∈ fixedSpace x) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    coordinateSemilinearMap g e ∈ fixedSpace x := by
  obtain ⟨μ, hμ0, hμ⟩ := orth_exists_pow_two_pow 1 t ht0
  set u : Kˣ := Units.mk0 μ hμ0 with hu
  have hh := orthTorus_sq_mem_supportedFixedDerived hx he hf hef heW hfW u
  have hut : ((u * u : Kˣ) : K) = t := by
    rw [Units.val_mul, hu, Units.val_mk0, ← pow_two]
    simpa using hμ
  have hhe : orthTorus he hf hef (u * u) e = t • e := by
    rw [orthTorus_apply, hef, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero he, hut, mul_one, mul_zero,
      zero_smul, add_zero, sub_smul, one_smul, add_sub_cancel]
  have hmem := orth_sub_mem_fixedSpace hx (supportedFixedDerived_le_supportedBlock (hstab _ hh))
    (coordinateSemilinearMap g e)
  rw [orthSemiConj_apply_map, hhe, coordinateSemilinearMap_smul] at hmem
  have hσt : g.right t - 1 ≠ 0 :=
    sub_ne_zero.2 fun h => ht1 (g.right.injective (h.trans (map_one g.right).symm))
  have h2 : (g.right t - 1) • coordinateSemilinearMap g e ∈ fixedSpace x := by
    rw [sub_smul, one_smul]
    exact hmem
  have h3 := Submodule.smul_mem _ (g.right t - 1)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ hσt, one_smul] at h3

theorem orth_semilinear_map_fixedSpace (hx : OddOrderIsometry Q p x) {n : ℕ}
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K)) (g : coordinateSemilinearGroup d K)
    (hstab : ∀ ω ∈ supportedFixedDerived Q x, orthSemiConj g ω ∈ supportedFixedDerived Q x)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ∀ w ∈ fixedSpace x, coordinateSemilinearMap g w ∈ fixedSpace x := by
  classical
  set b : Fin n ⊕ Fin n → Fin d → K := fun j => (ψ.symm (Pi.single j 1) : Fin d → K) with hb
  have hbW : ∀ j, b j ∈ fixedSpace x := fun j => (ψ.symm (Pi.single j 1)).2
  have hQb : ∀ j, Q (b j) = 0 := by
    intro j
    have h1 := ψ.symm.map_app (Pi.single j 1)
    rw [QuadraticMap.comp_apply, Submodule.subtype_apply] at h1
    rw [hb]
    simp only
    rw [h1, orth_quadPlus_single]
  have hpolar : ∀ i : Fin n, polar Q (b (Sum.inl i)) (b (Sum.inr i)) = 1 := by
    intro i
    have h1 : polar Q (b (Sum.inl i)) (b (Sum.inr i)) =
        polar (Q.comp (fixedSpace x).subtype) (ψ.symm (Pi.single (Sum.inl i) 1))
          (ψ.symm (Pi.single (Sum.inr i) 1)) := rfl
    have h2 : polar (Q.comp (fixedSpace x).subtype) (ψ.symm (Pi.single (Sum.inl i) 1))
        (ψ.symm (Pi.single (Sum.inr i) 1)) =
        polar (quadPlus n K) (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr i) 1) := by
      simp only [polar, ← map_add, ψ.symm.map_app]
    rw [h1, h2, orth_polar_quadPlus_single]
  have hΦb : ∀ j, coordinateSemilinearMap g (b j) ∈ fixedSpace x := by
    rintro (i | i)
    · exact orth_semilinear_mem_fixedSpace hx g hstab (hQb _) (hQb _) (hpolar i) (hbW _) (hbW _) ht0 ht1
    · exact orth_semilinear_mem_fixedSpace hx g hstab (hQb _) (hQb _)
        (by rw [polar_comm]; exact hpolar i) (hbW _) (hbW _) ht0 ht1
  intro w hw
  have hsymm : ∀ c : Fin n ⊕ Fin n → K, ψ.symm c = ∑ j, c j • ψ.symm (Pi.single j 1) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hdec : (⟨w, hw⟩ : fixedSpace x) = ∑ j, (ψ ⟨w, hw⟩ j) • ψ.symm (Pi.single j 1) := by
    rw [← hsymm, ψ.symm_apply_apply]
  have hw' : w = ∑ j, (ψ ⟨w, hw⟩ j) • b j := by
    have := congrArg (fun z : fixedSpace x => (z : Fin d → K)) hdec
    simpa [hb] using this
  rw [hw', map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [coordinateSemilinearMap_smul]
  exact Submodule.smul_mem _ _ (hΦb j)

theorem orth_semilinear_symm_map_fixedSpace (g : coordinateSemilinearGroup d K)
    (hΦW : ∀ w ∈ fixedSpace x, coordinateSemilinearMap g w ∈ fixedSpace x) :
    ∀ w ∈ fixedSpace x, (coordinateSemilinearMap g).symm w ∈ fixedSpace x := by
  have hinj : Function.Injective
      (fun w : fixedSpace x => (⟨coordinateSemilinearMap g w, hΦW w w.2⟩ : fixedSpace x)) :=
    fun a b h => Subtype.ext ((coordinateSemilinearMap g).injective (congrArg Subtype.val h))
  have hsurj := Finite.injective_iff_surjective.1 hinj
  intro w hw
  obtain ⟨w', hw'⟩ := hsurj ⟨w, hw⟩
  have h1 : coordinateSemilinearMap g w' = w := congrArg Subtype.val hw'
  rw [← h1, AddEquiv.symm_apply_apply]
  exact w'.2

end FixedSemilinear

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace omegaGroup mem_omegaGroup)
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply polar_quadPlus coe_quadPlus)
open Polynomial QuadraticMap

section Coord

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  {x : (Fin d → K) ≃ₗ[K] (Fin d → K)}

theorem orth_restrictFixed_mem (ω : ↥(supportedFixedDerived Q x)) :
    restrictFixed Q x ⟨ω, supportedFixedDerived_le_supportedBlock ω.2⟩ ∈
      orthDerived (Q.comp (fixedSpace x).subtype) := by
  obtain ⟨ω, k, hk, rfl⟩ := ω
  have h1 : (⟨((supportedBlock Q x (X - 1)).subtype k : (Fin d → K) ≃ₗ[K] (Fin d → K)),
      supportedFixedDerived_le_supportedBlock ⟨k, hk, rfl⟩⟩ : ↥(supportedBlock Q x (X - 1))) = k :=
    Subtype.ext rfl
  rw [h1]
  exact hk

@[expose] noncomputable def orthFixedRestrictHom :
    ↥(supportedFixedDerived Q x) →* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
  MonoidHom.codRestrict ((restrictFixed Q x).comp (Subgroup.inclusion supportedFixedDerived_le_supportedBlock))
    _ orth_restrictFixed_mem

theorem coe_orthFixedRestrictHom (ω : ↥(supportedFixedDerived Q x)) (w : fixedSpace x) :
    ((((orthFixedRestrictHom ω : orthDerived (Q.comp (fixedSpace x).subtype)) :
      fixedSpace x ≃ₗ[K] fixedSpace x) w : fixedSpace x) : Fin d → K) =
        (ω : (Fin d → K) ≃ₗ[K] (Fin d → K)) w :=
  coe_restrictFixed _ w

theorem orthFixedRestrictHom_bijective [FiniteDimensional K (Fin d → K)] (hx : OddOrderIsometry Q p x) :
    Function.Bijective (orthFixedRestrictHom (Q := Q) (x := x)) := by
  refine ⟨fun a b hab => ?_, fun φ => ?_⟩
  · have h1 : restrictFixed Q x ⟨a, supportedFixedDerived_le_supportedBlock a.2⟩ =
        restrictFixed Q x ⟨b, supportedFixedDerived_le_supportedBlock b.2⟩ := congrArg Subtype.val hab
    have h2 := restrictFixed_injective hx h1
    exact Subtype.ext (congrArg (fun z : ↥(supportedBlock Q x (X - 1)) => (z : (Fin d → K) ≃ₗ[K] (Fin d → K))) h2)
  · obtain ⟨g, hg⟩ := restrictFixed_surjective hx φ.1 (Subgroup.commutator_le_self _ φ.2)
    have hgF : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ supportedFixedDerived Q x :=
      ⟨g, Subgroup.mem_comap.2 (by rw [hg]; exact φ.2), rfl⟩
    exact ⟨⟨g, hgF⟩, Subtype.ext (by
      show restrictFixed Q x ⟨g, _⟩ = φ.1
      rw [← hg])⟩

@[expose] noncomputable def orthFixedRestrict [FiniteDimensional K (Fin d → K)] (hx : OddOrderIsometry Q p x) :
    ↥(supportedFixedDerived Q x) ≃* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
  MulEquiv.ofBijective orthFixedRestrictHom (orthFixedRestrictHom_bijective hx)

variable {n : ℕ}

@[expose] noncomputable def orthFixedCoord [FiniteDimensional K (Fin d → K)] (hx : OddOrderIsometry Q p x)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K)) :
    ↥(supportedFixedDerived Q x) ≃* ↥(orthDerived (quadPlus n K)) :=
  (orthFixedRestrict hx).trans (CFSG.RankThree.PartOne.orthDerivedEquiv ψ)

theorem orthFixedCoord_apply [FiniteDimensional K (Fin d → K)] (hx : OddOrderIsometry Q p x)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K)) (ω : ↥(supportedFixedDerived Q x))
    (v : Fin n ⊕ Fin n → K) :
    ((ψ.symm (((orthFixedCoord hx ψ ω : orthDerived (quadPlus n K)) :
      (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) v) : fixedSpace x) : Fin d → K) =
        (ω : (Fin d → K) ≃ₗ[K] (Fin d → K)) (ψ.symm v : Fin d → K) := by
  change ((ψ.symm (ψ (((orthFixedRestrictHom ω : orthDerived (Q.comp (fixedSpace x).subtype)) :
    fixedSpace x ≃ₗ[K] fixedSpace x) (ψ.symm v))) : fixedSpace x) : Fin d → K) = _
  rw [ψ.symm_apply_apply, coe_orthFixedRestrictHom]

end Coord

section SemiCoord

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {x : (Fin d → K) ≃ₗ[K] (Fin d → K)} {n : ℕ}

@[expose] def orthSemilinearFixed (g : coordinateSemilinearGroup d K)
    (hΦW : ∀ w ∈ fixedSpace x, coordinateSemilinearMap g w ∈ fixedSpace x)
    (hΦW' : ∀ w ∈ fixedSpace x, (coordinateSemilinearMap g).symm w ∈ fixedSpace x) :
    fixedSpace x ≃+ fixedSpace x where
  toFun w := ⟨coordinateSemilinearMap g (w : Fin d → K), hΦW w w.2⟩
  invFun w := ⟨(coordinateSemilinearMap g).symm (w : Fin d → K), hΦW' w w.2⟩
  left_inv w := Subtype.ext ((coordinateSemilinearMap g).symm_apply_apply (w : Fin d → K))
  right_inv w := Subtype.ext ((coordinateSemilinearMap g).apply_symm_apply (w : Fin d → K))
  map_add' a b := Subtype.ext (map_add (coordinateSemilinearMap g) (a : Fin d → K) (b : Fin d → K))

@[expose] def orthSemilinearCoord (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K))
    (g : coordinateSemilinearGroup d K)
    (hΦW : ∀ w ∈ fixedSpace x, coordinateSemilinearMap g w ∈ fixedSpace x)
    (hΦW' : ∀ w ∈ fixedSpace x, (coordinateSemilinearMap g).symm w ∈ fixedSpace x) :
    (Fin n ⊕ Fin n → K) ≃+ (Fin n ⊕ Fin n → K) :=
  (ψ.toLinearEquiv.toAddEquiv.symm.trans (orthSemilinearFixed g hΦW hΦW')).trans ψ.toLinearEquiv.toAddEquiv

variable (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K)) (g : coordinateSemilinearGroup d K)
  (hΦW : ∀ w ∈ fixedSpace x, coordinateSemilinearMap g w ∈ fixedSpace x)
  (hΦW' : ∀ w ∈ fixedSpace x, (coordinateSemilinearMap g).symm w ∈ fixedSpace x)

theorem orthSemilinearCoord_apply (v : Fin n ⊕ Fin n → K) :
    ((ψ.symm (orthSemilinearCoord ψ g hΦW hΦW' v) : fixedSpace x) : Fin d → K) =
      coordinateSemilinearMap g (ψ.symm v : Fin d → K) := by
  change ((ψ.symm (ψ (orthSemilinearFixed g hΦW hΦW' (ψ.symm v))) : fixedSpace x) : Fin d → K) = _
  rw [ψ.symm_apply_apply]
  rfl

theorem orthSemilinearCoord_symm_apply (v : Fin n ⊕ Fin n → K) :
    ((ψ.symm ((orthSemilinearCoord ψ g hΦW hΦW').symm v) : fixedSpace x) : Fin d → K) =
      (coordinateSemilinearMap g).symm (ψ.symm v : Fin d → K) := by
  change ((ψ.symm (ψ ((orthSemilinearFixed g hΦW hΦW').symm (ψ.symm v))) : fixedSpace x) : Fin d → K) = _
  rw [ψ.symm_apply_apply]
  rfl

theorem orthSemilinearCoord_smul (c : K) (v : Fin n ⊕ Fin n → K) :
    orthSemilinearCoord ψ g hΦW hΦW' (c • v) = g.right c • orthSemilinearCoord ψ g hΦW hΦW' v := by
  refine ψ.symm.injective (Subtype.ext ?_)
  show ((ψ.symm (orthSemilinearCoord ψ g hΦW hΦW' (c • v)) : fixedSpace x) : Fin d → K) =
    ((ψ.symm (g.right c • orthSemilinearCoord ψ g hΦW hΦW' v) : fixedSpace x) : Fin d → K)
  rw [orthSemilinearCoord_apply, map_smul, map_smul, Submodule.coe_smul, Submodule.coe_smul,
    orthSemilinearCoord_apply, coordinateSemilinearMap_smul]

end SemiCoord

section LinearPart

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def orthLinearPart (σ : K ≃+* K) (Φ' : (ι → K) ≃+ (ι → K))
    (hΦ' : ∀ (c : K) v, Φ' (c • v) = σ c • Φ' v) : (ι → K) ≃ₗ[K] (ι → K) where
  toFun v := Φ' ((orthCoordFieldMap σ).symm v)
  invFun v := orthCoordFieldMap σ (Φ'.symm v)
  map_add' v w := by rw [map_add, map_add]
  map_smul' c v := by
    rw [orthCoordFieldMap_symm_smul, hΦ', RingEquiv.apply_symm_apply, RingHom.id_apply]
  left_inv v := by
    change orthCoordFieldMap σ (Φ'.symm (Φ' ((orthCoordFieldMap σ).symm v))) = v
    rw [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
  right_inv v := by
    change Φ' ((orthCoordFieldMap σ).symm (orthCoordFieldMap σ (Φ'.symm v))) = v
    rw [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

theorem orthLinearPart_apply (σ : K ≃+* K) (Φ' : (ι → K) ≃+ (ι → K))
    (hΦ' : ∀ (c : K) v, Φ' (c • v) = σ c • Φ' v) (v : ι → K) :
    orthLinearPart σ Φ' hΦ' v = Φ' ((orthCoordFieldMap σ).symm v) := rfl

theorem orthLinearPart_symm_apply (σ : K ≃+* K) (Φ' : (ι → K) ≃+ (ι → K))
    (hΦ' : ∀ (c : K) v, Φ' (c • v) = σ c • Φ' v) (v : ι → K) :
    (orthLinearPart σ Φ' hΦ').symm v = orthCoordFieldMap σ (Φ'.symm v) := rfl

theorem orthLinearPart_conj (σ : K ≃+* K) (Φ' : (ι → K) ≃+ (ι → K))
    (hΦ' : ∀ (c : K) v, Φ' (c • v) = σ c • Φ' v) (X : (ι → K) ≃ₗ[K] (ι → K)) (v : ι → K) :
    (orthLinearPart σ Φ' hΦ' * orthTwist σ X * (orthLinearPart σ Φ' hΦ')⁻¹) v = Φ' (X (Φ'.symm v)) := by
  show orthLinearPart σ Φ' hΦ' (orthTwist σ X ((orthLinearPart σ Φ' hΦ').symm v)) = _
  rw [orthLinearPart_symm_apply, orthTwist_apply, AddEquiv.symm_apply_apply, orthLinearPart_apply,
    AddEquiv.symm_apply_apply]

end LinearPart

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace omegaGroup mem_omegaGroup)
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply polar_quadPlus coe_quadPlus)
open Polynomial QuadraticMap

section D4Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  {x : (Fin d → K) ≃ₗ[K] (Fin d → K)} {n : ℕ}

theorem orthFixedCoord_semiConj (hx : OddOrderIsometry Q p x)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K)) (g : coordinateSemilinearGroup d K)
    (hΦW : ∀ w ∈ fixedSpace x, coordinateSemilinearMap g w ∈ fixedSpace x)
    (hΦW' : ∀ w ∈ fixedSpace x, (coordinateSemilinearMap g).symm w ∈ fixedSpace x)
    (ω : ↥(supportedFixedDerived Q x)) (hΓω : orthSemiConj g ω ∈ supportedFixedDerived Q x) :
    ((orthFixedCoord hx ψ ⟨orthSemiConj g ω, hΓω⟩ : orthDerived (quadPlus n K)) :
      (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) =
      orthLinearPart g.right (orthSemilinearCoord ψ g hΦW hΦW') (orthSemilinearCoord_smul ψ g hΦW hΦW') *
        orthTwist g.right (orthFixedCoord hx ψ ω : orthDerived (quadPlus n K)) *
          (orthLinearPart g.right (orthSemilinearCoord ψ g hΦW hΦW')
            (orthSemilinearCoord_smul ψ g hΦW hΦW'))⁻¹ := by
  refine LinearEquiv.ext fun v => ?_
  rw [orthLinearPart_conj]
  refine ψ.symm.injective (Subtype.ext ?_)
  show ((ψ.symm (((orthFixedCoord hx ψ ⟨orthSemiConj g ω, hΓω⟩ : orthDerived (quadPlus n K)) :
      (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) v) : fixedSpace x) : Fin d → K) =
    ((ψ.symm (orthSemilinearCoord ψ g hΦW hΦW' (((orthFixedCoord hx ψ ω : orthDerived (quadPlus n K)) :
      (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) ((orthSemilinearCoord ψ g hΦW hΦW').symm v))) :
        fixedSpace x) : Fin d → K)
  rw [orthFixedCoord_apply, orthSemilinearCoord_apply, orthFixedCoord_apply, orthSemilinearCoord_symm_apply]
  exact orthSemiConj_apply g ω (ψ.symm v : Fin d → K)

theorem quadPlus_orthSemilinearCoord (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K))
    (g : coordinateSemilinearGroup d K) (hΦW : ∀ w ∈ fixedSpace x, coordinateSemilinearMap g w ∈ fixedSpace x)
    (hΦW' : ∀ w ∈ fixedSpace x, (coordinateSemilinearMap g).symm w ∈ fixedSpace x) {μ : K}
    (hμ : ∀ v, Q (coordinateSemilinearMap g v) = μ * g.right (Q v)) (v : Fin n ⊕ Fin n → K) :
    quadPlus n K (orthSemilinearCoord ψ g hΦW hΦW' v) = μ * g.right (quadPlus n K v) := by
  have h1 := ψ.symm.map_app (orthSemilinearCoord ψ g hΦW hΦW' v)
  have h2 := ψ.symm.map_app v
  rw [QuadraticMap.comp_apply, Submodule.subtype_apply, orthSemilinearCoord_apply] at h1
  rw [QuadraticMap.comp_apply, Submodule.subtype_apply] at h2
  rw [← h1, hμ, h2]

theorem quadPlus_orthLinearPart (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K))
    (g : coordinateSemilinearGroup d K) (hΦW : ∀ w ∈ fixedSpace x, coordinateSemilinearMap g w ∈ fixedSpace x)
    (hΦW' : ∀ w ∈ fixedSpace x, (coordinateSemilinearMap g).symm w ∈ fixedSpace x) {μ : K}
    (hμ : ∀ v, Q (coordinateSemilinearMap g v) = μ * g.right (Q v)) (v : Fin n ⊕ Fin n → K) :
    quadPlus n K (orthLinearPart g.right (orthSemilinearCoord ψ g hΦW hΦW')
      (orthSemilinearCoord_smul ψ g hΦW hΦW') v) = μ * quadPlus n K v := by
  rw [orthLinearPart_apply, quadPlus_orthSemilinearCoord ψ g hΦW hΦW' hμ, quadPlus_orthCoordFieldMap_symm,
    RingEquiv.apply_symm_apply]

theorem orth_smulOfUnit_comm {ι : Type} (u : Kˣ) (X : (ι → K) ≃ₗ[K] (ι → K)) :
    LinearEquiv.smulOfUnit u * X = X * LinearEquiv.smulOfUnit u :=
  LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    show (u : K) • X v = X ((u : K) • v)
    rw [map_smul]

theorem orth_conj_smulOfUnit {ι : Type} (u : Kˣ) (L X : (ι → K) ≃ₗ[K] (ι → K)) :
    (LinearEquiv.smulOfUnit u * L) * X * (LinearEquiv.smulOfUnit u * L)⁻¹ = L * X * L⁻¹ := by
  have h := orth_smulOfUnit_comm u (L * X * L⁻¹)
  calc (LinearEquiv.smulOfUnit u * L) * X * (LinearEquiv.smulOfUnit u * L)⁻¹ =
      (LinearEquiv.smulOfUnit u * (L * X * L⁻¹)) * (LinearEquiv.smulOfUnit u)⁻¹ := by group
    _ = L * X * L⁻¹ := by rw [h, mul_inv_cancel_right]

end D4Core

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace omegaGroup mem_omegaGroup)
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply polar_quadPlus coe_quadPlus)
open Polynomial QuadraticMap

section D4Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  {x : (Fin d → K) ≃ₗ[K] (Fin d → K)} {n : ℕ}

theorem orth_quadPlus_single_add_single (hn : 1 ≤ n) :
    quadPlus n K (Pi.single (Sum.inl ⟨0, by omega⟩) 1 + Pi.single (Sum.inr ⟨0, by omega⟩) 1) = 1 := by
  rw [QuadraticMap.map_add (quadPlus n K), orth_quadPlus_single, orth_quadPlus_single,
    orth_polar_quadPlus_single, zero_add, zero_add]

theorem orth_exists_omega_semiConj (hx : OddOrderIsometry Q p x) (hn : 3 ≤ n)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K)) (g : coordinateSemilinearGroup d K)
    (hg : g ∈ similarityPairs Q) (hσ : g.right ≠ 1) (hσ3 : g.right ^ 3 = 1)
    (hstab : ∀ ω ∈ supportedFixedDerived Q x, orthSemiConj g ω ∈ supportedFixedDerived Q x)
    (hΓ3 : ∀ ω ∈ supportedFixedDerived Q x, orthSemiConj g (orthSemiConj g (orthSemiConj g ω)) = ω) :
    ∃ Λ ∈ orthDerived (quadPlus n K), ∀ (ω : ↥(supportedFixedDerived Q x))
      (hΓω : orthSemiConj g ω ∈ supportedFixedDerived Q x),
      ((orthFixedCoord hx ψ ⟨orthSemiConj g ω, hΓω⟩ : orthDerived (quadPlus n K)) :
        (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) =
        Λ * orthTwist g.right (orthFixedCoord hx ψ ω : orthDerived (quadPlus n K)) * Λ⁻¹ := by
  classical
  set σ := g.right with hσdef
  obtain ⟨t, ht⟩ : ∃ t, σ t ≠ t := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (map_zero _)
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact ht (map_one _)
  have hK : 2 < Nat.card K := by
    haveI := Fintype.ofFinite K
    have h3 : ({0, 1, t} : Finset K).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [ht0.symm, (zero_ne_one (α := K))]),
        Finset.card_pair (Ne.symm ht1)]
    have := Finset.card_le_univ ({0, 1, t} : Finset K)
    rw [h3] at this
    rw [Nat.card_eq_fintype_card]
    omega
  have hΦW := orth_semilinear_map_fixedSpace hx ψ g hstab ht0 ht1
  have hΦW' := orth_semilinear_symm_map_fixedSpace g hΦW
  set L := orthLinearPart σ (orthSemilinearCoord ψ g hΦW hΦW') (orthSemilinearCoord_smul ψ g hΦW hΦW')
    with hL
  obtain ⟨μ, hμ⟩ := hg
  obtain ⟨l, hl0, hl⟩ := orth_exists_pow_two_pow 1 (μ : K) μ.ne_zero
  set u : Kˣ := (Units.mk0 l hl0)⁻¹ with hu
  set Λ : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) := LinearEquiv.smulOfUnit u * L with hΛ
  have hKI : ∀ (ω : ↥(supportedFixedDerived Q x)) (hΓω : orthSemiConj g ω ∈ supportedFixedDerived Q x),
      ((orthFixedCoord hx ψ ⟨orthSemiConj g ω, hΓω⟩ : orthDerived (quadPlus n K)) :
        (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) =
        Λ * orthTwist σ (orthFixedCoord hx ψ ω : orthDerived (quadPlus n K)) * Λ⁻¹ := by
    intro ω hΓω
    rw [hΛ, orth_conj_smulOfUnit]
    exact orthFixedCoord_semiConj hx ψ g hΦW hΦW' ω hΓω
  refine ⟨Λ, ?_, hKI⟩
  have hΛO : Λ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hΛ, LinearEquiv.mul_apply]
    show quadPlus n K ((u : K) • L v) = quadPlus n K v
    rw [QuadraticMap.map_smul, hL, quadPlus_orthLinearPart ψ g hΦW hΦW' hμ, smul_eq_mul, hu,
      Units.val_inv_eq_inv_val, Units.val_mk0, ← hl]
    have hl' : l ≠ 0 := hl0
    field_simp
    ring
  have htw1 : orthTwist σ Λ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    orthTwist_mem_orthogonalGroup σ hΛO
  have htw2 : orthTwist σ (orthTwist σ Λ) ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    orthTwist_mem_orthogonalGroup σ htw1
  set N := Λ * orthTwist σ Λ * orthTwist σ (orthTwist σ Λ) with hN
  have hNO : N ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) := mul_mem (mul_mem hΛO htw1) htw2
  have htw : ∀ A B : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K),
      orthTwist σ (A * B * A⁻¹) = orthTwist σ A * orthTwist σ B * (orthTwist σ A)⁻¹ := fun A B => by
    rw [map_mul, map_mul, map_inv]
  have hNc : ∀ Y ∈ orthDerived (quadPlus n K), N * Y * N⁻¹ = Y := by
    intro Y hY
    obtain ⟨ω, hω⟩ := (orthFixedCoord hx ψ).surjective ⟨Y, hY⟩
    set ω₁ : ↥(supportedFixedDerived Q x) := ⟨orthSemiConj g ω, hstab _ ω.2⟩ with hω₁
    set ω₂ : ↥(supportedFixedDerived Q x) := ⟨orthSemiConj g ω₁, hstab _ ω₁.2⟩ with hω₂
    have h3 : (⟨orthSemiConj g ω₂, hstab _ ω₂.2⟩ : ↥(supportedFixedDerived Q x)) = ω :=
      Subtype.ext (hΓ3 ω ω.2)
    have e1 := hKI ω (hstab _ ω.2)
    have e2 := hKI ω₁ (hstab _ ω₁.2)
    have e3 := hKI ω₂ (hstab _ ω₂.2)
    rw [h3] at e3
    have hYω : ((orthFixedCoord hx ψ ω : orthDerived (quadPlus n K)) :
        (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) = Y := congrArg Subtype.val hω
    rw [show (⟨orthSemiConj g ω₁, hstab _ ω₁.2⟩ : ↥(supportedFixedDerived Q x)) = ω₂ from rfl] at e2
    rw [show (⟨orthSemiConj g ω, hstab _ ω.2⟩ : ↥(supportedFixedDerived Q x)) = ω₁ from rfl] at e1
    rw [e2, htw, e1, htw, htw, orthTwist_three hσ3, hYω] at e3
    conv_rhs => rw [e3]
    rw [hN]
    group
  obtain ⟨hQn, hTn⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) hn
  have hdim : 3 ≤ Module.finrank K (Fin n ⊕ Fin n → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨hcent, -⟩ :=
    CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar hK
      (quadPlus n K) hQn hdim
  obtain ⟨c, hc⟩ := (hcent (N : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))).1 fun Y hY => by
    have h1 := hNc Y hY
    have h2 : N * Y = Y * N := mul_inv_eq_iff_eq_mul.mp h1
    exact congrArg (fun Z : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) =>
      (Z : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))) h2
  have hc1 : c = 1 := by
    set v₀ : Fin n ⊕ Fin n → K := Pi.single (Sum.inl ⟨0, by omega⟩) 1 + Pi.single (Sum.inr ⟨0, by omega⟩) 1
      with hv₀
    have h1 := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hNO) v₀
    have h2 : N v₀ = c • v₀ := by
      have := congrArg (fun F : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) => F v₀) hc
      simpa using this
    rw [h2, QuadraticMap.map_smul, hv₀, orth_quadPlus_single_add_single (by omega), smul_eq_mul, mul_one] at h1
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (c - 1) * (c - 1) = 0 := by linear_combination h1 - c * h22 + h22
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  have hN1 : N = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have := congrArg (fun F : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) => F v) hc
    simpa [hc1] using this
  have hD1 := CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQn (mul_mem hΛO htw1) htw2
  have hD2 := CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQn hΛO htw1
  rw [← hN, hN1, CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_one, hD2,
    finrank_commSpace_orthTwist, finrank_commSpace_orthTwist, finrank_commSpace_orthTwist] at hD1
  have hD : ((Module.finrank K (commSpace Λ) : ℕ) : ZMod 2) = 0 := by
    have h2 : ((Module.finrank K (commSpace Λ) : ℕ) : ZMod 2) + ((Module.finrank K (commSpace Λ) : ℕ) : ZMod 2) =
        0 := CharTwo.add_self_eq_zero _
    linear_combination -hD1 - h2
  have hΛΩ : Λ ∈ omegaGroup (quadPlus n K) hQn :=
    mem_omegaGroup.2 ⟨hΛO, (ZMod.natCast_eq_zero_iff_even).1 hD⟩
  exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQn hTn hΛΩ

end D4Omega

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open scoped commutatorElement

theorem orth_fieldOn_of_decomp {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ} (hp : p.Prime)
    {X J : Subgroup Ω} (hJ : GLAPComponent p X J) {y : Ω}
    (hy : y ∈ Subgroup.normalizer (J : Set Ω)) (hyp : y ^ p = 1) {G₀ : Type} [Group G₀]
    {J₀ : Subgroup G₀} (ρ : ↥J →* ↥J₀) (hρs : Function.Surjective ρ)
    (hρk : ρ.ker ≤ Subgroup.center ↥J) (Γ : ↥J₀ →* ↥J₀)
    (hΓ : ∀ (l : ↥J) (hl : y⁻¹ * (l : Ω) * y ∈ J), ρ ⟨_, hl⟩ = Γ (ρ l))
    (hno : ∀ L : G₀, ¬ ∀ ω : ↥J₀, ((Γ ω : ↥J₀) : G₀) = L * ω * L⁻¹)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htri : lab.tag ≠ .triD4)
    (hraw : CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ GGRawFieldConj p R I F ∧
      ∃ Θ₁ : ↥J₀ →* R, Function.Surjective Θ₁ ∧ Θ₁.ker ≤ Subgroup.center ↥J₀ ∧
        (∀ φ ∈ I, ∃ L : G₀, ∃ hL : ∀ ω ∈ J₀, L * ω * L⁻¹ ∈ J₀,
          ∀ ω : ↥J₀, φ (Θ₁ ω) = Θ₁ ⟨L * ω * L⁻¹, hL ω ω.2⟩) ∧
        ∃ u ∈ I, ∃ f ∈ F, ∀ ω : ↥J₀, (u * f) (Θ₁ ω) = Θ₁ (Γ ω)) :
    FieldOn p y J := by
  have hperfJ : commutator ↥J = ⊤ := orth_commutator_eq_top_of_glaPComponent hJ
  have hperf0 : commutator ↥J₀ = ⊤ := orth_commutator_eq_top_of_surjective hperfJ ρ hρs
  have hperfQ : commutator (PQuot p J) = ⊤ := (isQuasisimple_pQuot_of_glaPComponent hp hJ).1
  refine ⟨hy, hperfQ, lab, hlab, Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, hCB, Θ₁, hΘs, hΘk, hreal, u, hu, f, hf, huf⟩
  set Θ : ↥J →* R := Θ₁.comp ρ with hΘdef
  have hΘsurj : Function.Surjective Θ := hΘs.comp hρs
  have hΘker : Θ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    have h1 : ρ l ∈ Subgroup.center ↥J₀ := hΘk hl
    refine Y10GInnLin.mem_center_of_commutator_mem_center hperfJ fun j => hρk ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 h1 (ρ j)).symm
  obtain ⟨e, he⟩ := l154_exists_pSimple_equiv hp hJ hs Θ hΘsurj hΘker
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (J : Set Ω) := Subgroup.inv_mem _ hy
  have hmemJ : ∀ l : ↥J, y⁻¹ * (l : Ω) * y ∈ J := fun l => by
    have := (Subgroup.mem_normalizer_iff.1 hyinv (l : Ω)).1 l.2
    simpa using this
  have hα : MulAut.congr e (MI.indAut p J y hy) = u * f := by
    refine MulEquiv.ext fun r => ?_
    obtain ⟨l, rfl⟩ := hΘsurj r
    have e1 : e (QuotientGroup.mk (QuotientGroup.mk l)) = Θ l := he l
    have e2 : MI.indAut p J y hy (QuotientGroup.mk (QuotientGroup.mk l)) =
        QuotientGroup.mk (QuotientGroup.mk (⟨y⁻¹ * (l : Ω) * y, hmemJ l⟩ : ↥J)) :=
      MI.indAut_apply_mk hy ⟨l, ⟨y⁻¹ * (l : Ω) * y, hmemJ l⟩, rfl, rfl, rfl⟩
    have h1 : e.symm (Θ l) = QuotientGroup.mk (QuotientGroup.mk l) := by rw [← e1, MulEquiv.symm_apply_apply]
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, h1, e2, he]
    show Θ₁ (ρ ⟨y⁻¹ * (l : Ω) * y, hmemJ l⟩) = (u * f) (Θ₁ (ρ l))
    rw [hΓ l (hmemJ l), huf]
  have hnot : u * f ∉ I := by
    intro hI
    obtain ⟨L, hL, hLeq⟩ := hreal _ hI
    apply hno L
    have hdisp : ∀ ω : ↥J₀, Γ ω * (⟨L * ω * L⁻¹, hL ω ω.2⟩ : ↥J₀)⁻¹ ∈ Subgroup.center ↥J₀ := by
      intro ω
      apply hΘk
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hLeq, mul_inv_eq_one, huf]
    intro ω
    have key := K155X.hom_of_displacement hperf0 (J₀.subtype.comp Γ)
      ((MulAut.conj L).toMonoidHom.comp J₀.subtype)
      (fun v => v ∈ (Subgroup.center ↥J₀).map J₀.subtype)
      (by
        rintro v v' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hb a))
      (by
        rintro v ⟨a, ha, rfl⟩ g
        have h1 := Subgroup.mem_center_iff.1 ha ⟨L * g * L⁻¹, hL g g.2⟩
        exact (congrArg Subtype.val h1).symm)
      (fun g => ⟨_, hdisp g, rfl⟩) ω
    simpa [MulAut.conj_apply] using key
  have hpow : (u * f) ^ p = 1 := by
    rw [← hα, ← map_pow, l154_indAut_pow_eq_one hy hyp, map_one]
  obtain ⟨f', hf', u', hu', hord, heq⟩ := hCB hs hna u hu f (Subgroup.subset_closure hf) hnot hpow
  exact ⟨hs, hna, e, Or.inl htri, f', hf', u', hu', hord,
    (MI.induces_indRel_iff hy e).2 (by rw [← heq, hα])⟩

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open Polynomial QuadraticMap

section D4Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  {x : (Fin d → K) ≃ₗ[K] (Fin d → K)} {n : ℕ}

@[expose] noncomputable def orthFixedMatrix (hx : OddOrderIsometry Q p x)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K)) :
    ↥(supportedFixedDerived Q x) ≃* ↥(StatedOmega (StatedQuadPlus n K)) :=
  (orthFixedCoord hx ψ).trans (orthStatedOmegaEquiv (coe_quadPlus n K)).symm

theorem toLinEquiv_orthFixedMatrix (hx : OddOrderIsometry Q p x)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K)) (ω : ↥(supportedFixedDerived Q x)) :
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K
        ((orthFixedMatrix hx ψ ω : StatedOmega (StatedQuadPlus n K)) : GL (Fin n ⊕ Fin n) K) =
      ((orthFixedCoord hx ψ ω : orthDerived (quadPlus n K)) :
        (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
  congrArg Subtype.val ((orthStatedOmegaEquiv (coe_quadPlus n K)).apply_symm_apply (orthFixedCoord hx ψ ω))

theorem orth_d4_decomp (hx : OddOrderIsometry Q p x) (hn : 3 ≤ n)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K)) (g : coordinateSemilinearGroup d K)
    (hg : g ∈ similarityPairs Q) (hσ : g.right ≠ 1) (hσ3 : g.right ^ 3 = 1)
    (hstab : ∀ ω ∈ supportedFixedDerived Q x, orthSemiConj g ω ∈ supportedFixedDerived Q x)
    (hΓ3 : ∀ ω ∈ supportedFixedDerived Q x, orthSemiConj g (orthSemiConj g (orthSemiConj g ω)) = ω)
    (Γ : ↥(supportedFixedDerived Q x) →* ↥(supportedFixedDerived Q x))
    (hΓv : ∀ ω, ((Γ ω : ↥(supportedFixedDerived Q x)) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = orthSemiConj g ω) :
    ∃ u ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K n))),
      ∃ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K n))),
        ∀ ω : ↥(supportedFixedDerived Q x),
          (u * f) (LargeEvenProjMk _ (orthFixedMatrix hx ψ ω)) =
            LargeEvenProjMk _ (orthFixedMatrix hx ψ (Γ ω)) := by
  obtain ⟨Λ, hΛΩ, hKI⟩ := orth_exists_omega_semiConj hx hn ψ g hg hσ hσ3 hstab hΓ3
  set M : GL (Fin n ⊕ Fin n) K := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K).symm Λ
    with hMdef
  have hM : M ∈ StatedOmega (StatedQuadPlus n K) := by
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (coe_quadPlus n K), Subgroup.mem_comap,
      MulEquiv.coe_toMonoidHom, hMdef, MulEquiv.apply_symm_apply]
    exact hΛΩ
  have hm : 1 ≤ n := by omega
  refine ⟨MulAut.conj (LargeEvenProjMk _ ⟨M, hM⟩), ⟨_, rfl⟩,
    (MulAut.congr (RecipeFieldOmega.plusEquiv (K := K) hm)).symm (AutOm.fieldAutP n g.right),
    ⟨g.right, RecipeFieldOmega.graphAut_fieldAutP hm g.right⟩, fun ω => ?_⟩
  obtain ⟨h', hh'⟩ := RecipeFieldOmega.exists_map_mem_plus hm g.right (orthFixedMatrix hx ψ ω)
  rw [MulAut.mul_apply, RecipeFieldOmega.graphAut_fieldAutP hm g.right _ h' hh', MulAut.conj_apply,
    ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K).injective
  have hΓω : Γ ω = ⟨orthSemiConj g ω, hstab _ ω.2⟩ := Subtype.ext (hΓv ω)
  have hML : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K M = Λ := MulEquiv.apply_symm_apply _ _
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv,
    orth_toLinEquiv_of_map g.right hh', toLinEquiv_orthFixedMatrix, toLinEquiv_orthFixedMatrix, hΓω, hKI]
  show CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K M * _ *
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K M)⁻¹ = _
  rw [hML]

theorem orth_isQuasisimple_fixed_plus (hx : OddOrderIsometry Q p x) (hn : 3 ≤ n)
    (ψ : (Q.comp (fixedSpace x).subtype).IsometryEquiv (quadPlus n K)) :
    CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) := by
  obtain ⟨-, T, hT3, hTs⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) hn
  refine hx.isQuasisimple_supportedFixedDerived ⟨T.map ψ.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hT3
  · rintro _ ⟨t, ht, rfl⟩
    have h1 := ψ.symm.map_app t
    change (Q.comp (fixedSpace x).subtype) (ψ.symm t) = 0
    rw [h1]
    exact hTs t ht

end D4Matrix

section D4Final

theorem orthD4Fact_holds : OrthD4Fact := by
  intro K _ _ _ d Q hQ x hx hψ g hg hσ hσ3 Ω _ _ X J hJ y hy hy3 ρ hρs hρk hρy
  obtain ⟨ψ⟩ := hψ
  obtain ⟨Γ, hΓv, hΓρ⟩ := orth_exists_action hy ρ hρs g hρy
  have hstab : ∀ ω ∈ supportedFixedDerived Q x, orthSemiConj g ω ∈ supportedFixedDerived Q x := by
    intro ω hω
    rw [← hΓv ⟨ω, hω⟩]
    exact (Γ ⟨ω, hω⟩).2
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (J : Set Ω) := Subgroup.inv_mem _ hy
  have hmemJ : ∀ l : ↥J, y⁻¹ * (l : Ω) * y ∈ J := fun l => by
    have := (Subgroup.mem_normalizer_iff.1 hyinv (l : Ω)).1 l.2
    simpa using this
  have hΓ3 : ∀ ω ∈ supportedFixedDerived Q x,
      orthSemiConj g (orthSemiConj g (orthSemiConj g ω)) = ω := by
    intro ω hω
    obtain ⟨l, hl⟩ := hρs ⟨ω, hω⟩
    set l₁ : ↥J := ⟨y⁻¹ * (l : Ω) * y, hmemJ l⟩ with hl₁
    set l₂ : ↥J := ⟨y⁻¹ * (l₁ : Ω) * y, hmemJ l₁⟩ with hl₂
    set l₃ : ↥J := ⟨y⁻¹ * (l₂ : Ω) * y, hmemJ l₂⟩ with hl₃
    have hyyy : y * y * y = 1 := by rw [← hy3, pow_three, mul_assoc]
    have h3 : l₃ = l := by
      apply Subtype.ext
      show y⁻¹ * (y⁻¹ * (y⁻¹ * (l : Ω) * y) * y) * y = l
      calc y⁻¹ * (y⁻¹ * (y⁻¹ * (l : Ω) * y) * y) * y = (y * y * y)⁻¹ * l * (y * y * y) := by group
        _ = l := by rw [hyyy]; group
    have e1 := hΓρ l (hmemJ l)
    have e2 := hΓρ l₁ (hmemJ l₁)
    have e3 := hΓρ l₂ (hmemJ l₂)
    rw [show (⟨y⁻¹ * (l₂ : Ω) * y, hmemJ l₂⟩ : ↥J) = l₃ from rfl, h3] at e3
    rw [show (⟨y⁻¹ * (l : Ω) * y, hmemJ l⟩ : ↥J) = l₁ from rfl] at e1
    rw [show (⟨y⁻¹ * (l₁ : Ω) * y, hmemJ l₁⟩ : ↥J) = l₂ from rfl] at e2
    rw [e2, e1, hl] at e3
    have e4 := congrArg (fun z : ↥(supportedFixedDerived Q x) => (z : (Fin d → K) ≃ₗ[K] (Fin d → K))) e3
    simp only at e4
    rw [hΓv, hΓv, hΓv] at e4
    exact e4.symm
  have hdim : Module.finrank K (fixedSpace x) = 2 * 4 := by
    rw [ψ.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hno := orth_no_real_of_obstruction Nat.prime_three (by norm_num) g hσ hσ3 Γ hΓv
    (orth_obstruction_fixed hx hQ (s := 4) (by norm_num) hdim)
  obtain ⟨f, hK⟩ : ∃ f : ℕ, Nat.card K = 2 ^ f := by
    haveI := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 2
    exact ⟨m, by rw [Nat.card_eq_fintype_card, hm]⟩
  have hf1 : 1 ≤ f := by
    by_contra hlt
    have h1 := Finite.one_lt_card (α := K)
    rw [hK, show f = 0 by omega, pow_zero] at h1
    exact lt_irrefl 1 h1
  have hq := orth_isQuasisimple_fixed_plus hx (by norm_num) ψ
  have hlab : LargeEvenInLambda2 ⟨.D, 4, f⟩ := by
    show 1 ≤ f ∧ 3 ≤ 4
    exact ⟨hf1, by norm_num⟩
  refine orth_fieldOn_of_decomp Nat.prime_three hJ hy hy3 ρ hρs hρk Γ hΓρ hno hlab
    (show LargeEvenLieTag.D ≠ .triD4 by decide) ?_
  unfold CFSG.Assembly.LargeEvenRawDatum
  simp only [show (4 : ℕ) ≠ 3 by decide, ↓reduceIte]
  unfold LargeEvenRecipeOmegaPlus
  haveI hsimp : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by norm_num)
  set e := orthFixedMatrix hx ψ with he
  set Θ₁ : ↥(supportedFixedDerived Q x) →* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)) :=
    (LargeEvenProjMk _).comp e.toMonoidHom with hΘ₁
  have hΘs : Function.Surjective Θ₁ := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hna := orth_exists_noncomm_of_surjective hq.1 Θ₁ hΘs
  obtain ⟨u, hu, f', hf', huf⟩ := orth_d4_decomp hx (by norm_num) ψ g hg hσ hσ3 hstab hΓ3 Γ hΓv
  refine ⟨K, inferInstance, inferInstance, hK, hsimp, hna,
    RecipeFieldOmega.ggRawFieldConj_omegaPlus (K := K) (m := 4) (by norm_num) Nat.prime_three (by norm_num),
    Θ₁, hΘs, orth_ker_mk'_comp_le_center e _ (orth_statedScalars_subgroupOf_le_center _), ?_, u, hu, f', hf',
    huf⟩
  intro φ hφ
  obtain ⟨r, rfl⟩ := hφ
  obtain ⟨ω₀, rfl⟩ := hΘs r
  refine ⟨(ω₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)), fun ω hω =>
    (supportedFixedDerived Q x).mul_mem ((supportedFixedDerived Q x).mul_mem ω₀.2 hω)
      ((supportedFixedDerived Q x).inv_mem ω₀.2), fun ω => ?_⟩
  have e1 : (⟨(ω₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)) * ω * (ω₀ : (Fin d → K) ≃ₗ[K] (Fin d → K))⁻¹,
      (supportedFixedDerived Q x).mul_mem ((supportedFixedDerived Q x).mul_mem ω₀.2 ω.2)
        ((supportedFixedDerived Q x).inv_mem ω₀.2)⟩ : ↥(supportedFixedDerived Q x)) = ω₀ * ω * ω₀⁻¹ := rfl
  rw [e1, MulAut.conj_apply, map_mul, map_mul, map_inv]

end D4Final

end CFSG.LocalAnalysis.GLTheoremA.K155XOr

namespace CFSG.LocalAnalysis.GLTheoremA.K155XOr

open CFSG.LocalAnalysis.GLTheoremA.K155X

section Final

theorem l154OmegaFld_orth : L154OmegaFld l154Orth :=
  l154OmegaFld_orth_of_d4 orthD4Fact_holds

theorem l154OmegaFld_twOrth : L154OmegaFld l154TwOrth :=
  l154OmegaFld_twOrth_of_d4 orthD4Fact_holds

end Final

end CFSG.LocalAnalysis.GLTheoremA.K155XOr
