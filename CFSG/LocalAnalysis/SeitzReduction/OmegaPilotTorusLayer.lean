module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPerp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv minusIndexEquiv coordinateQuadPlus coordinateQuadMinus coordinateQuadPlus_apply
    coordinateQuadMinus_apply coordinatePlusIsometry coordinateMinusIsometry
    coordinatePlusWitnessEquiv coordinateMinusWitnessEquiv regular_coordinateQuadPlus
    regular_coordinateQuadMinus)
open CFSG.LieType.Universal.Spin (quadPlus quadMinus quadPlus_apply quadMinus_apply)

section PerpCoord

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {a b : ι} {ι' : Type*}

@[expose] noncomputable def perpCoordEquiv (j : ι' → ι) (hj : Function.Injective j)
    (hja : ∀ x, j x ≠ a) (hjb : ∀ x, j x ≠ b) (hjs : ∀ i, i ≠ a → i ≠ b → ∃ x, j x = i) :
    perpSub K a b ≃ₗ[K] (ι' → K) where
  toFun u x := (u : ι → K) (j x)
  invFun w := ⟨Function.extend j w 0, mem_perpSub.mpr
    ⟨Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => hja x hx),
      Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => hjb x hx)⟩⟩
  map_add' u v := rfl
  map_smul' c u := rfl
  left_inv u := by
    apply Subtype.ext
    funext i
    change Function.extend j (fun x => (u : ι → K) (j x)) 0 i = (u : ι → K) i
    by_cases hi : ∃ x, j x = i
    · obtain ⟨x, rfl⟩ := hi
      exact hj.extend_apply _ _ x
    · rw [Function.extend_apply' _ _ _ hi]
      by_cases hia : i = a
      · subst hia
        exact u.2.1.symm
      · by_cases hib : i = b
        · subst hib
          exact u.2.2.symm
        · exact absurd (hjs i hia hib) hi
  right_inv w := funext fun x => hj.extend_apply w 0 x

@[expose] noncomputable def perpIsometry {Q : QuadraticForm K (ι → K)}
    {Q' : QuadraticForm K (ι' → K)} (j : ι' → ι) (hj : Function.Injective j)
    (hja : ∀ x, j x ≠ a) (hjb : ∀ x, j x ≠ b) (hjs : ∀ i, i ≠ a → i ≠ b → ∃ x, j x = i)
    (hQ' : ∀ w, Q (Function.extend j w 0) = Q' w) :
    (Q.comp (perpSub K a b).subtype).IsometryEquiv Q' where
  toLinearEquiv := perpCoordEquiv j hj hja hjb hjs
  map_app' u := by
    have hu : Function.extend j (fun x => (u : ι → K) (j x)) 0 = (u : ι → K) :=
      congrArg Subtype.val ((perpCoordEquiv (K := K) j hj hja hjb hjs).symm_apply_apply u)
    change Q' (fun x => (u : ι → K) (j x)) = Q u
    rw [← hQ', hu]

end PerpCoord

section Regular

variable {K : Type*} [Field K] {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
  [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}

theorem nondegenerate_of_isometryEquiv (e : Q.IsometryEquiv Q')
    (hQ' : (polarBilin Q').Nondegenerate) : (polarBilin Q).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun x hx => ?_
  have key : ∀ y, polar Q' (e x) y = 0 := fun y => by
    obtain ⟨y', rfl⟩ := e.toLinearEquiv.surjective y
    rw [← hx y']
    change polar Q' (e x) (e y') = polar Q x y'
    simp only [polar, ← map_add, e.map_app]
  have h0 : e x = 0 := hQ'.1 (e x) fun y => by
    rw [polarBilin_apply_apply]
    exact key y
  exact e.toLinearEquiv.injective (h0.trans (map_zero e.toLinearEquiv).symm)

theorem exists_threeSingular_of_isometryEquiv (e : Q.IsometryEquiv Q')
    (hT : ∃ T : Submodule K V', finrank K T = 3 ∧ ∀ x ∈ T, Q' x = 0) :
    ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  obtain ⟨T', hT', hT's⟩ := hT
  refine ⟨T'.map e.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hT'
  · rintro _ ⟨y, hy, rfl⟩
    change Q (e.symm y) = 0
    rw [e.symm.map_app]
    exact hT's y hy

end Regular

section Avoid

variable {M N : ℕ}

@[expose] def avoid (hMN : M + 1 = N) (k : Fin N) (x : Fin M) : Fin N :=
  Fin.cast hMN ((Fin.cast hMN.symm k).succAbove x)

theorem avoid_injective (hMN : M + 1 = N) (k : Fin N) : Function.Injective (avoid hMN k) := by
  subst hMN
  intro x y hxy
  simp only [avoid, Fin.cast_eq_self] at hxy
  exact Fin.succAbove_right_injective hxy

theorem avoid_ne (hMN : M + 1 = N) (k : Fin N) (x : Fin M) : avoid hMN k x ≠ k := by
  subst hMN
  simp [avoid]

theorem exists_avoid_eq (hMN : M + 1 = N) {k i : Fin N} (hik : i ≠ k) :
    ∃ x, avoid hMN k x = i := by
  subst hMN
  simpa [avoid] using Fin.exists_succAbove_eq hik

theorem sum_avoid {R : Type*} [AddCommMonoid R] (hMN : M + 1 = N) (k : Fin N)
    (f : Fin N → R) : ∑ i, f i = f k + ∑ x, f (avoid hMN k x) := by
  subst hMN
  simpa [avoid] using Fin.sum_univ_succAbove f k

end Avoid

section LieModel

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def orthDerivedCongr {V V' : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {R : QuadraticForm K V} {R' : QuadraticForm K V'}
    (e : R.IsometryEquiv R') : orthDerived R ≃* orthDerived R' :=
  ((orthDerived R).equivMapOfInjective (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom
    (LinearEquiv.autCongr e.toLinearEquiv).injective).trans
    (MulEquiv.subgroupCongr
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.derivedOrthogonal_map_isometry
        e))

theorem lieModel_of_mulEquiv_orthDerived_plus {G : Type} [Group G] {m f : ℕ} (hm : 4 ≤ m)
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (φ : G ≃* orthDerived (coordinateQuadPlus m K)) :
    CFSG.Blueprint.LieModel G .POmegaPlus m 2 f := by
  have hne := (isHypCoord_coordinateQuadPlus (K := K) (⟨0, by omega⟩ : Fin m)).exists_ne_zero
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, hf, hm⟩, K, inferInstance, inferInstance, hK,
    ⟨φ.trans ((MulEquiv.ofBijective (projHom _) ⟨projHom_injective hne, projHom_surjective _⟩).trans
      (coordinatePlusWitnessEquiv K (MulEquiv.refl _)).symm)⟩⟩

theorem lieModel_of_mulEquiv_orthDerived_minus {G : Type} [Group G] {m f : ℕ} (hm : 4 ≤ m)
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (φ : G ≃* orthDerived (coordinateQuadMinus m K (by omega) b c)) :
    CFSG.Blueprint.LieModel G .POmegaMinus m 2 f := by
  have hne := (isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ m) b c
    (⟨0, by omega⟩ : Fin (m - 1))).exists_ne_zero
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, hf, hm⟩, K, inferInstance, inferInstance, hK, b, c,
    hirr, ⟨φ.trans ((MulEquiv.ofBijective (projHom _)
      ⟨projHom_injective hne, projHom_surjective _⟩).trans
      (coordinateMinusWitnessEquiv K (by omega) b c (MulEquiv.refl _)).symm)⟩⟩

end LieModel

section Plus

variable {K : Type*} [Field K] {n : ℕ}

@[expose] noncomputable def plusPerpCoord (hn : 1 ≤ n) (k : Fin n) (x : Fin (2 * (n - 1))) :
    Fin (2 * n) :=
  plusIndexEquiv n (Sum.map (avoid (by omega) k) (avoid (by omega) k)
    ((plusIndexEquiv (n - 1)).symm x))

theorem plusPerpCoord_injective (hn : 1 ≤ n) (k : Fin n) :
    Function.Injective (plusPerpCoord hn k) := by
  intro x y hxy
  have h1 := (plusIndexEquiv n).injective hxy
  have h2 := (Sum.map_injective.mpr ⟨avoid_injective _ k, avoid_injective _ k⟩) h1
  exact (plusIndexEquiv (n - 1)).symm.injective h2

theorem plusPerpCoord_ne_left (hn : 1 ≤ n) (k : Fin n) (x : Fin (2 * (n - 1))) :
    plusPerpCoord hn k x ≠ plusIndexEquiv n (.inl k) := by
  intro h
  have h1 := (plusIndexEquiv n).injective h
  rcases hy : (plusIndexEquiv (n - 1)).symm x with y | y <;>
    simp only [hy, Sum.map_inl, Sum.map_inr] at h1
  · exact avoid_ne _ k y (Sum.inl_injective h1)
  · exact Sum.inr_ne_inl h1

theorem plusPerpCoord_ne_right (hn : 1 ≤ n) (k : Fin n) (x : Fin (2 * (n - 1))) :
    plusPerpCoord hn k x ≠ plusIndexEquiv n (.inr k) := by
  intro h
  have h1 := (plusIndexEquiv n).injective h
  rcases hy : (plusIndexEquiv (n - 1)).symm x with y | y <;>
    simp only [hy, Sum.map_inl, Sum.map_inr] at h1
  · exact Sum.inl_ne_inr h1
  · exact avoid_ne _ k y (Sum.inr_injective h1)

theorem exists_plusPerpCoord_eq (hn : 1 ≤ n) (k : Fin n) {i : Fin (2 * n)}
    (hia : i ≠ plusIndexEquiv n (.inl k)) (hib : i ≠ plusIndexEquiv n (.inr k)) :
    ∃ x, plusPerpCoord hn k x = i := by
  rcases hs : (plusIndexEquiv n).symm i with i₀ | i₀
  · have hi₀ : i₀ ≠ k := by
      rintro rfl
      exact hia (by rw [← hs, Equiv.apply_symm_apply])
    obtain ⟨y, hy⟩ := exists_avoid_eq (M := n - 1) (by omega) hi₀
    refine ⟨plusIndexEquiv (n - 1) (.inl y), ?_⟩
    simp only [plusPerpCoord, Equiv.symm_apply_apply, Sum.map_inl, hy, ← hs,
      Equiv.apply_symm_apply]
  · have hi₀ : i₀ ≠ k := by
      rintro rfl
      exact hib (by rw [← hs, Equiv.apply_symm_apply])
    obtain ⟨y, hy⟩ := exists_avoid_eq (M := n - 1) (by omega) hi₀
    refine ⟨plusIndexEquiv (n - 1) (.inr y), ?_⟩
    simp only [plusPerpCoord, Equiv.symm_apply_apply, Sum.map_inr, hy, ← hs,
      Equiv.apply_symm_apply]

theorem coordinateQuadPlus_extend (hn : 1 ≤ n) (k : Fin n) (w : Fin (2 * (n - 1)) → K) :
    coordinateQuadPlus n K (Function.extend (plusPerpCoord hn k) w 0) =
      coordinateQuadPlus (n - 1) K w := by
  have hinj := plusPerpCoord_injective hn k
  have hval : ∀ s : Fin (n - 1) ⊕ Fin (n - 1),
      Function.extend (plusPerpCoord hn k) w 0
        (plusIndexEquiv n (Sum.map (avoid (by omega) k) (avoid (by omega) k) s)) =
        w (plusIndexEquiv (n - 1) s) := by
    intro s
    have : plusIndexEquiv n (Sum.map (avoid (by omega) k) (avoid (by omega) k) s) =
        plusPerpCoord hn k (plusIndexEquiv (n - 1) s) := by
      simp [plusPerpCoord]
    rw [this, hinj.extend_apply]
  have hzero : Function.extend (plusPerpCoord hn k) w 0 (plusIndexEquiv n (.inl k)) = 0 :=
    Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => plusPerpCoord_ne_left hn k x hx
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply, sum_avoid (by omega : n - 1 + 1 = n) k,
    hzero, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 := hval (.inl x)
  have h2 := hval (.inr x)
  simp only [Sum.map_inl, Sum.map_inr] at h1 h2
  rw [h1, h2]

@[expose] noncomputable def plusPerpIsometry (hn : 1 ≤ n) (k : Fin n) :
    ((coordinateQuadPlus n K).comp
      (perpSub K (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))).subtype).IsometryEquiv
      (coordinateQuadPlus (n - 1) K) :=
  perpIsometry (plusPerpCoord hn k) (plusPerpCoord_injective hn k) (plusPerpCoord_ne_left hn k)
    (plusPerpCoord_ne_right hn k) (fun _ hia hib => exists_plusPerpCoord_eq hn k hia hib)
    (coordinateQuadPlus_extend hn k)

end Plus

section PlusMain

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem regular_plusPerp (hn : 4 ≤ n) (k : Fin n) :
    (polarBilin ((coordinateQuadPlus n K).comp
      (perpSub K (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))).subtype)).Nondegenerate ∧
    ∃ T : Submodule K (perpSub K (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))),
      finrank K T = 3 ∧ ∀ x ∈ T, (coordinateQuadPlus n K).comp
        (perpSub K (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))).subtype x = 0 := by
  have hreg := regular_coordinateQuadPlus (n - 1) K (by omega)
  have e := plusPerpIsometry (K := K) (by omega : 1 ≤ n) k
  exact ⟨nondegenerate_of_isometryEquiv e hreg.1, exists_threeSingular_of_isometryEquiv e hreg.2⟩

theorem centralizer_pairTorus (hq : 4 ≤ Nat.card K) (k : Fin n) :
    centralizer (pairTorus (K := K) k : Set (matrixProjectiveDerived (coordinateQuadPlus n K))) =
      pairTorus k ⊔ pairPerp k :=
  (isHypCoord_coordinateQuadPlus k).centralizer_pairTorusOf hq

theorem inSubgroup_layer_centralizer_pairTorus (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) (k : Fin n) :
    inSubgroup layer (centralizer
      (pairTorus (K := K) k : Set (matrixProjectiveDerived (coordinateQuadPlus n K)))) =
      pairPerp k := by
  obtain ⟨hR, hT⟩ := regular_plusPerp (K := K) hn k
  exact (isHypCoord_coordinateQuadPlus k).inSubgroup_layer_centralizer_pairTorusOf hq
    (regular_coordinateQuadPlus n K (by omega)).1 hR hT

@[expose] noncomputable def pairPerpEquiv (hn : 4 ≤ n) (k : Fin n) :
    pairPerp (K := K) k ≃* orthDerived (coordinateQuadPlus (n - 1) K) :=
  ((isHypCoord_coordinateQuadPlus k).pairPerpOfEquiv
    (regular_coordinateQuadPlus n K (by omega)).1 (regular_plusPerp hn k).1
    (regular_plusPerp hn k).2).trans (orthDerivedCongr (plusPerpIsometry (by omega) k))

theorem lieModel_pairPerp {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) (k : Fin n) :
    CFSG.Blueprint.LieModel (pairPerp (K := K) (n := n) k) .POmegaPlus (n - 1) 2 f :=
  lieModel_of_mulEquiv_orthDerived_plus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hK) hK
    (pairPerpEquiv (by omega) k)

end PlusMain

section Minus

variable {K : Type*} [Field K] {n : ℕ}

@[expose] noncomputable def minusPerpCoord (hn : 2 ≤ n) (k : Fin (n - 1))
    (x : Fin (2 * (n - 1))) : Fin (2 * n) :=
  minusIndexEquiv n (by omega) (Sum.map (avoid (by omega) k) (Sum.map (avoid (by omega) k) id)
    ((minusIndexEquiv (n - 1) (by omega)).symm x))

theorem minusPerpCoord_injective (hn : 2 ≤ n) (k : Fin (n - 1)) :
    Function.Injective (minusPerpCoord hn k) := by
  intro x y hxy
  have h1 := (minusIndexEquiv n (by omega)).injective hxy
  have h2 := (Sum.map_injective.mpr ⟨avoid_injective _ k,
    Sum.map_injective.mpr ⟨avoid_injective _ k, Function.injective_id⟩⟩) h1
  exact (minusIndexEquiv (n - 1) (by omega)).symm.injective h2

theorem minusPerpCoord_ne_left (hn : 2 ≤ n) (k : Fin (n - 1)) (x : Fin (2 * (n - 1))) :
    minusPerpCoord hn k x ≠ minusIndexEquiv n (by omega) (.inl k) := by
  intro h
  have h1 := (minusIndexEquiv n (by omega)).injective h
  rcases hy : (minusIndexEquiv (n - 1) (by omega)).symm x with y | y | y <;>
    simp only [hy, Sum.map_inl, Sum.map_inr] at h1
  · exact avoid_ne _ k y (Sum.inl_injective h1)
  · exact Sum.inr_ne_inl h1
  · exact Sum.inr_ne_inl h1

theorem minusPerpCoord_ne_right (hn : 2 ≤ n) (k : Fin (n - 1)) (x : Fin (2 * (n - 1))) :
    minusPerpCoord hn k x ≠ minusIndexEquiv n (by omega) (.inr (.inl k)) := by
  intro h
  have h1 := (minusIndexEquiv n (by omega)).injective h
  rcases hy : (minusIndexEquiv (n - 1) (by omega)).symm x with y | y | y <;>
    simp only [hy, Sum.map_inl, Sum.map_inr] at h1
  · exact Sum.inl_ne_inr h1
  · exact avoid_ne _ k y (Sum.inl_injective (Sum.inr_injective h1))
  · exact Sum.inr_ne_inl (Sum.inr_injective h1)

theorem exists_minusPerpCoord_eq (hn : 2 ≤ n) (k : Fin (n - 1)) {i : Fin (2 * n)}
    (hia : i ≠ minusIndexEquiv n (by omega) (.inl k))
    (hib : i ≠ minusIndexEquiv n (by omega) (.inr (.inl k))) :
    ∃ x, minusPerpCoord hn k x = i := by
  rcases hs : (minusIndexEquiv n (by omega)).symm i with i₀ | i₀ | t
  · have hi₀ : i₀ ≠ k := by
      rintro rfl
      exact hia (by rw [← hs, Equiv.apply_symm_apply])
    obtain ⟨y, hy⟩ := exists_avoid_eq (M := n - 1 - 1) (by omega) hi₀
    refine ⟨minusIndexEquiv (n - 1) (by omega) (.inl y), ?_⟩
    simp only [minusPerpCoord, Equiv.symm_apply_apply, Sum.map_inl, hy, ← hs,
      Equiv.apply_symm_apply]
  · have hi₀ : i₀ ≠ k := by
      rintro rfl
      exact hib (by rw [← hs, Equiv.apply_symm_apply])
    obtain ⟨y, hy⟩ := exists_avoid_eq (M := n - 1 - 1) (by omega) hi₀
    refine ⟨minusIndexEquiv (n - 1) (by omega) (.inr (.inl y)), ?_⟩
    simp only [minusPerpCoord, Equiv.symm_apply_apply, Sum.map_inl, Sum.map_inr, hy, ← hs,
      Equiv.apply_symm_apply]
  · refine ⟨minusIndexEquiv (n - 1) (by omega) (.inr (.inr t)), ?_⟩
    simp only [minusPerpCoord, Equiv.symm_apply_apply, Sum.map_inr, id_eq, ← hs,
      Equiv.apply_symm_apply]

theorem coordinateQuadMinus_extend (hn : 2 ≤ n) (b c : K) (k : Fin (n - 1))
    (w : Fin (2 * (n - 1)) → K) :
    coordinateQuadMinus n K (by omega) b c (Function.extend (minusPerpCoord hn k) w 0) =
      coordinateQuadMinus (n - 1) K (by omega) b c w := by
  have hinj := minusPerpCoord_injective hn k
  have hval : ∀ s : Fin (n - 1 - 1) ⊕ Fin (n - 1 - 1) ⊕ Fin 2,
      Function.extend (minusPerpCoord hn k) w 0
        (minusIndexEquiv n (by omega)
          (Sum.map (avoid (by omega) k) (Sum.map (avoid (by omega) k) id) s)) =
        w (minusIndexEquiv (n - 1) (by omega) s) := by
    intro s
    have : minusIndexEquiv n (by omega)
        (Sum.map (avoid (by omega) k) (Sum.map (avoid (by omega) k) id) s) =
        minusPerpCoord hn k (minusIndexEquiv (n - 1) (by omega) s) := by
      simp [minusPerpCoord]
    rw [this, hinj.extend_apply]
  have hzero : Function.extend (minusPerpCoord hn k) w 0
      (minusIndexEquiv n (by omega) (.inl k)) = 0 :=
    Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => minusPerpCoord_ne_left hn k x hx
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply,
    sum_avoid (by omega : n - 1 - 1 + 1 = n - 1) k, hzero, zero_mul, zero_add]
  have h0 := hval (.inr (.inr 0))
  have h1 := hval (.inr (.inr 1))
  simp only [Sum.map_inr, id_eq] at h0 h1
  rw [h0, h1]
  congr 3
  refine Finset.sum_congr rfl fun x _ => ?_
  have hl := hval (.inl x)
  have hr := hval (.inr (.inl x))
  simp only [Sum.map_inl, Sum.map_inr] at hl hr
  rw [hl, hr]

@[expose] noncomputable def minusPerpIsometry (hn : 2 ≤ n) (b c : K) (k : Fin (n - 1)) :
    ((coordinateQuadMinus n K (by omega) b c).comp
      (perpSub K (minusIndexEquiv n (by omega) (.inl k))
        (minusIndexEquiv n (by omega) (.inr (.inl k)))).subtype).IsometryEquiv
      (coordinateQuadMinus (n - 1) K (by omega) b c) :=
  perpIsometry (minusPerpCoord hn k) (minusPerpCoord_injective hn k)
    (minusPerpCoord_ne_left hn k) (minusPerpCoord_ne_right hn k)
    (fun _ hia hib => exists_minusPerpCoord_eq hn k hia hib) (coordinateQuadMinus_extend hn b c k)

end Minus

section MinusMain

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [CharP K 2] in
theorem regular_minusPerp (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : Fin (n - 1)) :
    (polarBilin ((coordinateQuadMinus n K (by omega) b c).comp
      (perpSub K (minusIndexEquiv n (by omega) (.inl k))
        (minusIndexEquiv n (by omega) (.inr (.inl k)))).subtype)).Nondegenerate ∧
    ∃ T : Submodule K (perpSub K (minusIndexEquiv n (by omega) (.inl k))
        (minusIndexEquiv n (by omega) (.inr (.inl k)))),
      finrank K T = 3 ∧ ∀ x ∈ T, (coordinateQuadMinus n K (by omega) b c).comp
        (perpSub K (minusIndexEquiv n (by omega) (.inl k))
          (minusIndexEquiv n (by omega) (.inr (.inl k)))).subtype x = 0 := by
  have hreg := regular_coordinateQuadMinus (n - 1) K b c (by omega) hirr
  have e := minusPerpIsometry (K := K) (by omega : 2 ≤ n) b c k
  exact ⟨nondegenerate_of_isometryEquiv e hreg.1, exists_threeSingular_of_isometryEquiv e hreg.2⟩

theorem centralizer_minusPairTorus (hq : 4 ≤ Nat.card K) (hn : 1 ≤ n) (b c : K)
    (k : Fin (n - 1)) :
    centralizer (minusPairTorus hn b c k :
      Set (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) =
      minusPairTorus hn b c k ⊔ minusPairPerp hn b c k :=
  (isHypCoord_coordinateQuadMinus hn b c k).centralizer_pairTorusOf hq

theorem inSubgroup_layer_centralizer_minusPairTorus (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    inSubgroup layer (centralizer (minusPairTorus (K := K) (by omega) b c k :
      Set (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)))) =
      minusPairPerp (by omega) b c k := by
  obtain ⟨hR, hT⟩ := regular_minusPerp hn hirr k
  exact (isHypCoord_coordinateQuadMinus _ b c k).inSubgroup_layer_centralizer_pairTorusOf hq
    (regular_coordinateQuadMinus n K b c (by omega) hirr).1 hR hT

@[expose] noncomputable def minusPairPerpEquiv (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    minusPairPerp (K := K) (by omega) b c k ≃*
      orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c) :=
  ((isHypCoord_coordinateQuadMinus _ b c k).pairPerpOfEquiv
    (regular_coordinateQuadMinus n K b c (by omega) hirr).1 (regular_minusPerp hn hirr k).1
    (regular_minusPerp hn hirr k).2).trans (orthDerivedCongr (minusPerpIsometry (by omega) b c k))

theorem lieModel_minusPairPerp {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    CFSG.Blueprint.LieModel (minusPairPerp (K := K) (by omega : 1 ≤ n) b c k) .POmegaMinus
      (n - 1) 2 f :=
  lieModel_of_mulEquiv_orthDerived_minus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hK) hK
    hirr (minusPairPerpEquiv hn hirr k)

end MinusMain

section TorusFacts

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin d}

@[expose] noncomputable def IsHypCoord.pairTorusOfEquiv (h : IsHypCoord Q a b) :
    pairTorusOf Q a b ≃* Kˣ :=
  ((((torusLin (K := K) a b).range.subgroupOf (orthDerived Q)).equivMapOfInjective (projHom Q)
    (projHom_injective h.exists_ne_zero)).symm.trans
    (Subgroup.subgroupOfEquivOfLe h.range_torusLin_le)).trans
    (MonoidHom.ofInjective (torusLin_injective (K := K) a b)).symm

theorem IsHypCoord.isCyclic_pairTorusOf (h : IsHypCoord Q a b) : IsCyclic (pairTorusOf Q a b) :=
  isCyclic_of_surjective h.pairTorusOfEquiv.symm.toMonoidHom h.pairTorusOfEquiv.symm.surjective

theorem odd_card_pairTorusOf {f : ℕ} (h : IsHypCoord Q a b) (hK : Nat.card K = 2 ^ f) :
    Odd (Nat.card (pairTorusOf Q a b)) := by
  rw [card_pairTorusOf h, hK]
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one

variable {n : ℕ}

theorem isCyclic_pairTorus (k : Fin n) : IsCyclic (pairTorus (K := K) k) :=
  (isHypCoord_coordinateQuadPlus k).isCyclic_pairTorusOf

theorem odd_card_pairTorus {f : ℕ} (hK : Nat.card K = 2 ^ f) (k : Fin n) :
    Odd (Nat.card (pairTorus (K := K) k)) :=
  odd_card_pairTorusOf (isHypCoord_coordinateQuadPlus k) hK

theorem isCyclic_minusPairTorus (hn : 1 ≤ n) (b c : K) (k : Fin (n - 1)) :
    IsCyclic (minusPairTorus hn b c k) :=
  (isHypCoord_coordinateQuadMinus hn b c k).isCyclic_pairTorusOf

theorem odd_card_minusPairTorus {f : ℕ} (hK : Nat.card K = 2 ^ f) (hn : 1 ≤ n) (b c : K)
    (k : Fin (n - 1)) : Odd (Nat.card (minusPairTorus hn b c k)) :=
  odd_card_pairTorusOf (isHypCoord_coordinateQuadMinus hn b c k) hK

end TorusFacts

end CFSG.SeitzReduction.OmegaPilot
