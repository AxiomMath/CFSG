module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFlagRadicalCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataFaithful
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace OmegaRadical

variable {K : Type} [Field K] {d : ℕ}

@[expose] def flagRadical (Q : QuadraticForm K (Fin d → K)) (W : Submodule K (Fin d → K)) :
    Subgroup (matrixDerived Q) where
  carrier := {g | (∀ w ∈ W, matrixLinearEquiv g.val w = w) ∧
    (∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W, matrixLinearEquiv g.val x - x ∈ W) ∧
    ∀ x, matrixLinearEquiv g.val x - x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W}
  one_mem' := by
    refine ⟨fun w _ => Matrix.one_mulVec w, fun x _ => ?_, fun x => ?_⟩
    · change (1 : Matrix (Fin d) (Fin d) K) *ᵥ x - x ∈ W
      rw [Matrix.one_mulVec, sub_self]
      exact zero_mem _
    · change (1 : Matrix (Fin d) (Fin d) K) *ᵥ x - x ∈ _
      rw [Matrix.one_mulVec, sub_self]
      exact zero_mem _
  mul_mem' := by
    rintro g h ⟨g1, g2, g3⟩ ⟨h1, h2, h3⟩
    have hmul : ∀ x, matrixLinearEquiv (g * h).val x =
        matrixLinearEquiv g.val (matrixLinearEquiv h.val x) := fun x => by
      rw [Subgroup.coe_mul, matrixLinearEquiv_mul, LinearEquiv.mul_apply]
    have hsplit : ∀ x, matrixLinearEquiv (g * h).val x - x =
        (matrixLinearEquiv g.val (matrixLinearEquiv h.val x) - matrixLinearEquiv h.val x) +
          (matrixLinearEquiv h.val x - x) := fun x => by
      rw [hmul]
      abel
    refine ⟨fun w hw => by rw [hmul, h1 w hw, g1 w hw], fun x hx => ?_, fun x => ?_⟩
    · have hhx : matrixLinearEquiv h.val x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
        have := add_mem hx (h3 x)
        rwa [add_sub_cancel] at this
      rw [hsplit]
      exact add_mem (g2 _ hhx) (h2 x hx)
    · rw [hsplit]
      exact add_mem (g3 _) (h3 x)
  inv_mem' := by
    rintro g ⟨g1, g2, g3⟩
    have hinv : ∀ x, matrixLinearEquiv g.val (matrixLinearEquiv g⁻¹.val x) = x := fun x => by
      rw [← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, ← Subgroup.coe_mul,
        mul_inv_cancel, Subgroup.coe_one]
      exact Matrix.one_mulVec x
    have hsub : ∀ x, matrixLinearEquiv g⁻¹.val x - x =
        -(matrixLinearEquiv g.val (matrixLinearEquiv g⁻¹.val x) - matrixLinearEquiv g⁻¹.val x) :=
      fun x => by rw [hinv]; abel
    refine ⟨fun w hw => ?_, fun x hx => ?_, fun x => ?_⟩
    · exact (matrixLinearEquiv g.val).injective (by rw [hinv, g1 w hw])
    · have hy : matrixLinearEquiv g⁻¹.val x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
        have := sub_mem hx (g3 (matrixLinearEquiv g⁻¹.val x))
        rwa [hinv, sub_sub_cancel] at this
      rw [hsub]
      exact neg_mem (g2 _ hy)
    · rw [hsub]
      exact neg_mem (g3 _)

theorem mem_flagRadical_iff {Q : QuadraticForm K (Fin d → K)} {W : Submodule K (Fin d → K)}
    {g : matrixDerived Q} : g ∈ flagRadical Q W ↔ (∀ w ∈ W, matrixLinearEquiv g.val w = w) ∧
      (∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W,
        matrixLinearEquiv g.val x - x ∈ W) ∧
      ∀ x, matrixLinearEquiv g.val x - x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W :=
  Iff.rfl

@[expose] noncomputable def derivedKappa (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q →* MulAut (matrixProjectiveDerived Q) :=
  (matrixProjectiveConjugationHom Q).comp (matrixDerivedInclusion Q)

@[expose] noncomputable def flagRadicalImage (Q : QuadraticForm K (Fin d → K))
    (W : Submodule K (Fin d → K)) : Subgroup (MulAut (matrixProjectiveDerived Q)) :=
  (flagRadical Q W).map (derivedKappa Q)

@[expose] def FlagRadicalCentralizer (Q : QuadraticForm K (Fin d → K)) : Prop :=
  ∀ W : Submodule K (Fin d → K), (∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0) → 2 ≤ finrank K W →
    IsPGroup 2 (flagRadical Q W) ∧ (∀ g ∈ flagRadical Q W, g ^ 4 = 1) ∧
    IsPGroup 2 (flagRadicalImage Q W) ∧ (∀ α ∈ flagRadicalImage Q W, α ^ 4 = 1) ∧
    (∃ e : flagRadical Q W ≃* flagRadicalImage Q W,
      ∀ g, (e g : MulAut (matrixProjectiveDerived Q)) = derivedKappa Q g) ∧
    (∀ g : similarityPairs Q, (∀ v ∈ W, coordinateSemilinearMap g.val v ∈ W) →
      (∀ v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W,
        coordinateSemilinearMap g.val v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W) →
      matrixProjectiveConjugationHom Q g ∈
        Subgroup.normalizer (flagRadicalImage Q W : Set (MulAut (matrixProjectiveDerived Q)))) ∧
    IsPGroup 2 ↥(Subgroup.centralizer
      (flagRadicalImage Q W : Set (MulAut (matrixProjectiveDerived Q))) ⊓
        matrixProjectiveImage Q)

section Radical

variable {Q : QuadraticForm K (Fin d → K)} {W : Submodule K (Fin d → K)}

theorem matrixLinearIso_eq (A : GL (Fin d) K) : matrixLinearIso A = matrixLinearEquiv A :=
  rfl

theorem pow_four_eq_one_of_mem [CharP K 2] (hW : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0)
    {g : matrixDerived Q} (hg : g ∈ flagRadical Q W) : g ^ 4 = 1 := by
  obtain ⟨g1, g2, -⟩ := hg
  have hiso : ∀ v, Q (matrixLinearEquiv g.val v) = Q v :=
    (mem_matrixIsometries_iff Q g.val).mp (matrixDerived_le_isometries Q g.2)
  have hTB : ∀ x y, polar Q ((matrixLinearEquiv g.val).toAddEquiv x)
      ((matrixLinearEquiv g.val).toAddEquiv y) = polar Q x y := fun x y => by
    change polar Q (matrixLinearEquiv g.val x) (matrixLinearEquiv g.val y) = _
    rw [polar, polar, ← map_add, hiso, hiso, hiso]
  have h4 := FlagRadical.pow_four_of_flag (Z := W) hW hTB (fun z hz => g1 z hz) g2
  apply Subtype.ext
  apply matrixLinearIso.injective
  apply LinearEquiv.ext
  intro v
  rw [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
  change ((matrixLinearEquiv g.val) ^ 4) v = v
  rw [pow_succ, pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply]
  exact h4 v

theorem eichler_mem_flagRadical (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ = elementaryGroup Q)
    (hW : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0) {w u : Fin d → K} (hwW : w ∈ W) (hw : Q w = 0)
    (hu : u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W) :
    ∃ g ∈ flagRadical Q W, ∀ v, matrixLinearEquiv g.val v = eichler Q w u v := by
  have hmemL : ∀ x, x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W ↔
      ∀ w' ∈ W, polar Q w' x = 0 := fun x => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact Iff.rfl
  have hwu : polar Q w u = 0 := (hmemL u).1 hu w hwW
  have hA : matrixLinearIso.symm (eichler Q w u) ∈ matrixDerived Q := by
    rw [CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.mem_matrixDerived_iff,
      MulEquiv.apply_symm_apply, hE]
    exact eichler_mem_elementaryGroup Q w u
  have happ : ∀ v, matrixLinearEquiv (matrixLinearIso.symm (eichler Q w u)) v =
      eichler Q w u v := fun v => by
    rw [← matrixLinearIso_eq, MulEquiv.apply_symm_apply]
  refine ⟨⟨_, hA⟩, ⟨fun w' hw' => ?_, fun x hx => ?_, fun x => ?_⟩, happ⟩
  · change matrixLinearEquiv (matrixLinearIso.symm (eichler Q w u)) w' = w'
    rw [happ, eichler_apply hw hwu, polar_comm Q w' w, hW w hwW w' hw', (hmemL u).1 hu w' hw']
    simp
  · change matrixLinearEquiv (matrixLinearIso.symm (eichler Q w u)) x - x ∈ W
    rw [happ, eichler_apply hw hwu, polar_comm Q x w, (hmemL x).1 hx w hwW]
    simp only [zero_smul, add_zero, mul_zero, sub_sub_cancel_left, neg_mem_iff]
    exact W.smul_mem _ hwW
  · change matrixLinearEquiv (matrixLinearIso.symm (eichler Q w u)) x - x ∈ _
    rw [happ, eichler_apply hw hwu,
      show x + polar Q x w • u - (polar Q x u + Q u * polar Q x w) • w - x =
        polar Q x w • u - (polar Q x u + Q u * polar Q x w) • w by abel]
    have hwL : w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W :=
      (hmemL w).2 fun w' hw' => hW w' hw' w hwW
    exact sub_mem (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hwL)

end Radical

theorem symm_mem_of_forall_mem {F : Type*} [Field F] [Finite F] {V : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (T : V ≃+ V) {S : Submodule F V}
    (hS : ∀ v ∈ S, T v ∈ S) {v : V} (hv : v ∈ S) : T.symm v ∈ S := by
  have : Finite S := Module.finite_of_finite F
  let f : S → S := fun s => ⟨T s, hS s s.2⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (T.injective (congrArg Subtype.val h))
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.mp hf) ⟨v, hv⟩
  have h2 : T s = v := congrArg Subtype.val hs
  rw [← h2, T.symm_apply_apply]
  exact s.2

section Regular

variable [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}
  (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)

omit [Finite K] [CharP K 2] in
include hQ hT in
theorem six_le : 6 ≤ d := by
  obtain ⟨T, hT3, hTs⟩ := hT
  have hle : T ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) T := fun x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => by
      change polarBilin Q y x = 0
      rw [polarBilin_apply_apply, polar, hTs _ (T.add_mem hy hx), hTs y hy, hTs x hx]
      simp
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ, hT3, Module.finrank_fin_fun] at h1
  have h2 := Submodule.finrank_le T
  rw [hT3, Module.finrank_fin_fun] at h2
  omega

omit [Finite K] in
include hQ hT hE in
theorem derivedKappa_injective : Function.Injective (derivedKappa Q) := by
  have hd : 1 ≤ d := by have := six_le hQ hT; omega
  rw [injective_iff_map_eq_one]
  intro A hA
  have hmem : matrixDerivedInclusion Q A ∈ unitMultiplierPairs Q := fun v => by
    rw [matrixDerivedInclusion_val, coordinateSemilinearMap_inl]
    exact (mem_matrixIsometries_iff Q A.val).mp (matrixDerived_le_isometries Q A.2) v
  have h1 := eq_one_of_kappa_eq_one Q hQ hT hE hd hmem hA
  exact matrixDerivedInclusion_injective Q (h1.trans (map_one _).symm)

include hQ hT hE in
theorem flagRadicalCentralizer_of_regular : FlagRadicalCentralizer Q := by
  have hd : 1 ≤ d := by have := six_le hQ hT; omega
  have hd6 := six_le hQ hT
  intro W hW hW2
  have hinj := derivedKappa_injective hQ hT hE
  have h4 : ∀ g ∈ flagRadical Q W, g ^ 4 = 1 := fun g hg => pow_four_eq_one_of_mem hW hg
  have hR4 : ∀ α ∈ flagRadicalImage Q W, α ^ 4 = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, h4 g hg, map_one]
  have hconj : ∀ x : similarityPairs Q, (∀ v ∈ W, coordinateSemilinearMap x.val v ∈ W) →
      (∀ v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W,
        coordinateSemilinearMap x.val v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W) →
      ∀ y ∈ flagRadicalImage Q W, matrixProjectiveConjugationHom Q x * y *
        (matrixProjectiveConjugationHom Q x)⁻¹ ∈ flagRadicalImage Q W := by
    intro x hxW hxL y hy
    obtain ⟨g, ⟨g1, g2, g3⟩, rfl⟩ := hy
    set T := coordinateSemilinearMap x.val with hTdef
    have hTW' : ∀ v ∈ W, T.symm v ∈ W := fun v hv => symm_mem_of_forall_mem T hxW hv
    have hTL' : ∀ v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W,
        T.symm v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W := fun v hv =>
      symm_mem_of_forall_mem T hxL hv
    have happ : ∀ v, matrixLinearEquiv (matrixDerivedConjugation Q x g).val v =
        T (matrixLinearEquiv g.val (T.symm v)) := fun v =>
      matrixConjugation_vector x.val g.val v
    have hsub : ∀ v, matrixLinearEquiv (matrixDerivedConjugation Q x g).val v - v =
        T (matrixLinearEquiv g.val (T.symm v) - T.symm v) := fun v => by
      rw [happ, map_sub, T.apply_symm_apply]
    refine ⟨matrixDerivedConjugation Q x g, ⟨fun w hw => ?_, fun v hv => ?_, fun v => ?_⟩, ?_⟩
    · rw [happ, g1 _ (hTW' w hw), T.apply_symm_apply]
    · rw [hsub]
      exact hxW _ (g2 _ (hTL' v hv))
    · rw [hsub]
      exact hxL _ (g3 _)
    · change matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q
        (matrixDerivedConjugation Q x g)) = _
      rw [matrixDerivedInclusion_conjugation, map_mul, map_mul, map_inv]
      rfl
  refine ⟨fun g => ⟨2, Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact h4 g g.2)⟩, h4, fun α => ⟨2, Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hR4 α α.2)⟩, hR4,
    ⟨Subgroup.equivMapOfInjective (flagRadical Q W) (derivedKappa Q) hinj, fun g => rfl⟩,
    fun x hxW hxL => ?_, ?_⟩
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxW' : ∀ v ∈ W, coordinateSemilinearMap x⁻¹.val v ∈ W := fun v hv => by
      change coordinateSemilinearMap x.val⁻¹ v ∈ W
      rw [coordinateSemilinearMap_inv]
      exact symm_mem_of_forall_mem _ hxW hv
    have hxL' : ∀ v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W,
        coordinateSemilinearMap x⁻¹.val v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W :=
      fun v hv => by
        change coordinateSemilinearMap x.val⁻¹ v ∈ _
        rw [coordinateSemilinearMap_inv]
        exact symm_mem_of_forall_mem _ hxL hv
    refine ⟨hconj x hxW hxL y, fun hy => ?_⟩
    have h := hconj x⁻¹ hxW' hxL' _ hy
    rw [map_inv, inv_inv] at h
    simpa [mul_assoc] using h
  ·
    intro α
    obtain ⟨hαC, hαE⟩ := Subgroup.mem_inf.mp α.2
    have hαE' : (α : MulAut (matrixProjectiveDerived Q)) ∈ (unitKappa Q).range := by
      rw [range_unitKappa Q]
      exact hαE
    obtain ⟨x, hx⟩ := hαE'
    set T := coordinateSemilinearMap x.1.val with hTdef
    have hTs : ∀ (a : K) v, T (a • v) = x.1.val.right a • T v := fun a v =>
      coordinateSemilinearMap_smul x.1.val a v
    have hTQ : ∀ v, Q (T v) = x.1.val.right (Q v) := (mem_unitMultiplierPairs_iff Q x.1).mp x.2
    have hcomm : ∀ g ∈ flagRadical Q W, ∀ v,
        T (matrixLinearEquiv g.val v) = matrixLinearEquiv g.val (T v) := by
      intro g hg v
      have hgm : derivedKappa Q g ∈ flagRadicalImage Q W := ⟨g, hg, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hαC _ hgm
      have hinc : matrixDerivedInclusion Q g ∈ unitMultiplierPairs Q := fun v => by
        rw [matrixDerivedInclusion_val, coordinateSemilinearMap_inl]
        exact (mem_matrixIsometries_iff Q g.val).mp (matrixDerived_le_isometries Q g.2) v
      have h2 : matrixProjectiveConjugationHom Q
          ((matrixDerivedInclusion Q g * x.1) * (x.1 * matrixDerivedInclusion Q g)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul]
        change derivedKappa Q g * unitKappa Q x * (unitKappa Q x * derivedKappa Q g)⁻¹ = 1
        rw [hx, h1, mul_inv_cancel]
      have h3 := eq_one_of_kappa_eq_one Q hQ hT hE hd
        (mul_mem (mul_mem hinc x.2) (inv_mem (mul_mem x.2 hinc))) h2
      have h4 : matrixDerivedInclusion Q g * x.1 = x.1 * matrixDerivedInclusion Q g :=
        mul_inv_eq_one.mp h3
      have h5 := congrArg (fun y : similarityPairs Q => coordinateSemilinearMap y.val v) h4
      simp only [Subgroup.coe_mul, coordinateSemilinearMap_mul, matrixDerivedInclusion_val,
        coordinateSemilinearMap_inl] at h5
      exact h5.symm
    have hc : ∀ w ∈ W, Q w = 0 → ∀ u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W,
        ∀ v, T (eichler Q w u v) = eichler Q w u (T v) := by
      intro w hwW hw u hu v
      obtain ⟨g, hg, hgv⟩ := eichler_mem_flagRadical hE hW hwW hw hu
      rw [← hgv, ← hgv]
      exact hcomm g hg v
    obtain ⟨-, hT4⟩ := FlagRadical.semilinear_commute_eichler hQ hW hW2
      (by rw [Module.finrank_fin_fun]; exact hd6) hTs hTQ hc
    have hmap4 : ∀ v, coordinateSemilinearMap (x.1.val ^ 4) v = v := fun v => by
      rw [pow_succ, pow_succ, pow_succ, pow_one, coordinateSemilinearMap_mul,
        coordinateSemilinearMap_mul, coordinateSemilinearMap_mul]
      exact hT4 v
    have hx4 : x.1.val ^ 4 = 1 := by
      apply coordinateSemilinearHom_injective hd
      change Multiplicative.ofAdd (coordinateSemilinearMap (x.1.val ^ 4)) =
        Multiplicative.ofAdd (coordinateSemilinearMap 1)
      congr 1
      exact AddEquiv.ext fun v => by rw [hmap4, coordinateSemilinearMap_one]
    have hx4' : x ^ 4 = 1 := Subtype.ext (Subtype.ext hx4)
    refine ⟨2, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hx]
    change (unitKappa Q x) ^ 4 = 1
    rw [← map_pow, hx4', map_one]

end Regular

end OmegaRadical

open OmegaRadical in
theorem even_orthogonal_isotropic_flag_radical_centralizer (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ)
    (h : StatedClassicalModel G t n 2 f) :
    match t with
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
          FlagRadicalCentralizer (coordinateQuadPlus n K)
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
          FlagRadicalCentralizer (coordinateQuadMinus n K hn b c)
    | _ => False := by
  rcases ht with rfl | rfl
  · obtain ⟨-, hf, hn⟩ := h.1
    intro K _ _ hK _
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadPlus n K (by omega)
    exact flagRadicalCentralizer_of_regular hreg.1 hreg.2
      (commutator_coordinateQuadPlus n K (by omega))
  · obtain ⟨-, hf, hn⟩ := h.1
    intro hn1 K _ _ hK b c hirr _
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    exact flagRadicalCentralizer_of_regular hreg.1 hreg.2
      (commutator_coordinateQuadMinus n K b c hn hirr)

end CFSG.ComponentClassification.UnbalancedCatalog
