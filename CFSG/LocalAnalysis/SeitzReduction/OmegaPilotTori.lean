module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap
open scoped commutatorElement
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveProjection matrixDerived matrixDerivedScalars)

section HypCoord

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

structure IsHypCoord (Q : QuadraticForm K (ι → K)) (a b : ι) : Prop where
  ne : a ≠ b
  map_left : Q (Pi.single a 1) = 0
  map_right : Q (Pi.single b 1) = 0
  polar_left : ∀ v, polar Q (Pi.single a 1) v = v b
  polar_right : ∀ v, polar Q (Pi.single b 1) v = v a

variable {Q : QuadraticForm K (ι → K)} {a b : ι}

theorem IsHypCoord.map_add_smul (h : IsHypCoord Q a b) (x y : K) {p : ι → K} (hpa : p a = 0)
    (hpb : p b = 0) :
    Q (x • Pi.single a 1 + y • Pi.single b 1 + p) = x * y + Q p := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_add (⇑Q) (x • _), QuadraticMap.map_smul,
    QuadraticMap.map_smul, h.map_left, h.map_right, polar_add_left, polar_smul_left,
    polar_smul_left, polar_smul_left, h.polar_left, h.polar_left, h.polar_right, hpa, hpb]
  simp

@[expose] def perpPart (a b : ι) (v : ι → K) : ι → K :=
  v - v a • Pi.single a 1 - v b • Pi.single b 1

theorem perpPart_apply_left (hab : a ≠ b) (v : ι → K) : perpPart a b v a = 0 := by
  simp [perpPart, hab]

theorem perpPart_apply_right (hab : a ≠ b) (v : ι → K) : perpPart a b v b = 0 := by
  simp [perpPart, hab.symm]

theorem perpPart_apply_of_ne {i : ι} (hia : i ≠ a) (hib : i ≠ b) (v : ι → K) :
    perpPart a b v i = v i := by
  simp [perpPart, hia, hib]

theorem eq_add_perpPart (a b : ι) (v : ι → K) :
    v = v a • Pi.single a 1 + v b • Pi.single b 1 + perpPart a b v := by
  simp [perpPart]

theorem IsHypCoord.apply_eq (h : IsHypCoord Q a b) (v : ι → K) :
    Q v = v a * v b + Q (perpPart a b v) := by
  conv_lhs => rw [eq_add_perpPart a b v]
  exact h.map_add_smul _ _ (perpPart_apply_left h.ne v) (perpPart_apply_right h.ne v)

theorem IsHypCoord.map_single_add (h : IsHypCoord Q a b) :
    Q (Pi.single a 1 + Pi.single b 1) = 1 := by
  have := h.map_add_smul 1 1 (p := 0) rfl rfl
  simpa using this

end HypCoord

section Torus

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

@[expose] def torusEntry (a b : ι) (c : Kˣ) (i : ι) : Kˣ :=
  if i = a then c else if i = b then c⁻¹ else 1

theorem torusEntry_mul (a b : ι) (c c' : Kˣ) (i : ι) :
    torusEntry a b (c * c') i = torusEntry a b c i * torusEntry a b c' i := by
  unfold torusEntry
  split_ifs <;> simp [mul_comm]

theorem torusEntry_one (a b : ι) (i : ι) : torusEntry a b (1 : Kˣ) i = 1 := by
  unfold torusEntry
  split_ifs <;> simp

@[expose] noncomputable def torusLin (a b : ι) : Kˣ →* ((ι → K) ≃ₗ[K] (ι → K)) where
  toFun c := LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfUnit (torusEntry a b c i)
  map_one' := by
    ext v i
    change ((torusEntry a b 1 i : Kˣ) : K) * v i = v i
    rw [torusEntry_one, Units.val_one, one_mul]
  map_mul' c c' := by
    ext v i
    change ((torusEntry a b (c * c') i : Kˣ) : K) * v i =
      (torusEntry a b c i : K) * ((torusEntry a b c' i : K) * v i)
    rw [torusEntry_mul, Units.val_mul, mul_assoc]

theorem torusLin_apply (a b : ι) (c : Kˣ) (v : ι → K) (i : ι) :
    torusLin a b c v i = (torusEntry a b c i : K) * v i := rfl

theorem torusLin_apply_left (a b : ι) (c : Kˣ) (v : ι → K) : torusLin a b c v a = c * v a := by
  simp [torusLin_apply, torusEntry]

theorem torusLin_apply_right {a b : ι} (hab : a ≠ b) (c : Kˣ) (v : ι → K) :
    torusLin a b c v b = (c⁻¹ : Kˣ) * v b := by
  simp [torusLin_apply, torusEntry, hab.symm]

theorem torusLin_apply_of_ne {a b i : ι} (hia : i ≠ a) (hib : i ≠ b) (c : Kˣ) (v : ι → K) :
    torusLin a b c v i = v i := by
  simp [torusLin_apply, torusEntry, hia, hib]

theorem torusLin_single_left {a b : ι} (hab : a ≠ b) (c : Kˣ) :
    torusLin a b c (Pi.single a 1) = (c : K) • Pi.single a 1 := by
  ext i
  by_cases hia : i = a
  · subst hia
    simp [torusLin_apply_left]
  · by_cases hib : i = b
    · subst hib
      simp [torusLin_apply_right hab, hia]
    · simp [torusLin_apply_of_ne hia hib, hia]

theorem torusLin_single_right {a b : ι} (hab : a ≠ b) (c : Kˣ) :
    torusLin a b c (Pi.single b 1) = ((c⁻¹ : Kˣ) : K) • Pi.single b 1 := by
  ext i
  by_cases hib : i = b
  · subst hib
    simp [torusLin_apply_right hab]
  · by_cases hia : i = a
    · subst hia
      simp [torusLin_apply_left, hib]
    · simp [torusLin_apply_of_ne hia hib, hib]

theorem torusLin_injective (a b : ι) : Function.Injective (torusLin (K := K) a b) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have h := congrFun (LinearEquiv.congr_fun hc (Pi.single a 1)) a
  rw [torusLin_apply_left] at h
  simpa using h

@[expose] noncomputable def swapLin (a b : ι) : (ι → K) ≃ₗ[K] (ι → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.swap a b)

theorem swapLin_apply (a b : ι) (v : ι → K) (i : ι) :
    swapLin a b v i = v (Equiv.swap a b i) := rfl

theorem swapLin_mul_torusLin {a b : ι} (hab : a ≠ b) (d : Kˣ) :
    swapLin (K := K) a b * torusLin a b d = torusLin a b d⁻¹ * swapLin a b := by
  ext v i
  simp only [LinearEquiv.mul_apply, swapLin_apply, torusLin_apply]
  congr 1
  unfold torusEntry
  by_cases hia : i = a
  · subst hia
    simp [Equiv.swap_apply_left, Ne.symm hab]
  · by_cases hib : i = b
    · subst hib
      simp [Equiv.swap_apply_right, hia]
    · simp [Equiv.swap_apply_of_ne_of_ne hia hib, hia, hib]

theorem swapLin_mul_swapLin (a b : ι) : swapLin (K := K) a b * swapLin a b = 1 := by
  ext v i
  simp [swapLin_apply]

theorem commutatorElement_swapLin_torusLin {a b : ι} (hab : a ≠ b) (d : Kˣ) :
    ⁅swapLin (K := K) a b, torusLin a b d⁆ = torusLin a b (d⁻¹ * d⁻¹) := by
  have hs : (swapLin (K := K) a b)⁻¹ = swapLin a b :=
    inv_eq_of_mul_eq_one_right (swapLin_mul_swapLin a b)
  rw [commutatorElement_def, swapLin_mul_torusLin hab, mul_assoc (torusLin a b d⁻¹), hs,
    swapLin_mul_swapLin, mul_one, ← map_inv, ← map_mul]

variable {Q : QuadraticForm K (ι → K)} {a b : ι}

theorem perpPart_torusLin (h : IsHypCoord Q a b) (c : Kˣ) (v : ι → K) :
    perpPart a b (torusLin a b c v) = perpPart a b v := by
  ext i
  by_cases hia : i = a
  · subst hia
    rw [perpPart_apply_left h.ne, perpPart_apply_left h.ne]
  · by_cases hib : i = b
    · subst hib
      rw [perpPart_apply_right h.ne, perpPart_apply_right h.ne]
    · rw [perpPart_apply_of_ne hia hib, perpPart_apply_of_ne hia hib, torusLin_apply_of_ne hia hib]

theorem perpPart_swapLin (h : IsHypCoord Q a b) (v : ι → K) :
    perpPart a b (swapLin a b v) = perpPart a b v := by
  ext i
  by_cases hia : i = a
  · subst hia
    rw [perpPart_apply_left h.ne, perpPart_apply_left h.ne]
  · by_cases hib : i = b
    · subst hib
      rw [perpPart_apply_right h.ne, perpPart_apply_right h.ne]
    · rw [perpPart_apply_of_ne hia hib, perpPart_apply_of_ne hia hib, swapLin_apply,
        Equiv.swap_apply_of_ne_of_ne hia hib]

theorem IsHypCoord.torusLin_mem_orthogonalGroup (h : IsHypCoord Q a b) (c : Kˣ) :
    torusLin a b c ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [h.apply_eq, h.apply_eq v, perpPart_torusLin h, torusLin_apply_left,
    torusLin_apply_right h.ne]
  congr 1
  have : ((c⁻¹ : Kˣ) : K) * (c : K) = 1 := by simp
  linear_combination (v a * v b) * this

theorem IsHypCoord.swapLin_mem_orthogonalGroup (h : IsHypCoord Q a b) :
    swapLin a b ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [h.apply_eq, h.apply_eq v, perpPart_swapLin h, swapLin_apply, swapLin_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]

theorem IsHypCoord.torusLin_mem_orthDerived [Finite K] [CharP K 2] (h : IsHypCoord Q a b)
    (c : Kˣ) : torusLin a b c ∈ orthDerived Q := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' ((c⁻¹ : Kˣ) : K)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  set d : Kˣ := Units.mk0 r hr0
  have hd : d⁻¹ * d⁻¹ = c := by
    have hdd : d * d = c⁻¹ := Units.ext (by simp [d, hr])
    rw [← mul_inv, hdd, inv_inv]
  rw [← hd, ← commutatorElement_swapLin_torusLin h.ne]
  exact Subgroup.commutator_mem_commutator h.swapLin_mem_orthogonalGroup
    (h.torusLin_mem_orthogonalGroup d)

end Torus

section Proj

variable {K : Type*} [Field K]

@[expose] def stabSub {ι : Type*} [DecidableEq ι] (a b : ι) :
    Subgroup ((ι → K) ≃ₗ[K] (ι → K)) where
  carrier := {g | g (Pi.single a 1) = Pi.single a 1 ∧ g (Pi.single b 1) = Pi.single b 1}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    rintro g g' ⟨hga, hgb⟩ ⟨hga', hgb'⟩
    exact ⟨by rw [LinearEquiv.mul_apply, hga', hga], by rw [LinearEquiv.mul_apply, hgb', hgb]⟩
  inv_mem' := by
    rintro g ⟨hga, hgb⟩
    refine ⟨?_, ?_⟩
    · calc g⁻¹ (Pi.single a 1) = g⁻¹ (g (Pi.single a 1)) := by rw [hga]
        _ = Pi.single a 1 := g.symm_apply_apply _
    · calc g⁻¹ (Pi.single b 1) = g⁻¹ (g (Pi.single b 1)) := by rw [hgb]
        _ = Pi.single b 1 := g.symm_apply_apply _

theorem mem_stabSub {ι : Type*} [DecidableEq ι] {a b : ι} {g : (ι → K) ≃ₗ[K] (ι → K)} :
    g ∈ stabSub a b ↔ g (Pi.single a 1) = Pi.single a 1 ∧ g (Pi.single b 1) = Pi.single b 1 :=
  Iff.rfl

variable {d : ℕ}

@[expose] noncomputable def derivedEquiv (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q ≃* orthDerived Q :=
  ((matrixDerived Q).equivMapOfInjective
    CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso.toMonoidHom
    CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso.injective).trans
    (MulEquiv.subgroupCongr
      (CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.matrixDerived_map Q))

theorem coe_derivedEquiv (Q : QuadraticForm K (Fin d → K)) (A : matrixDerived Q) :
    ((derivedEquiv Q A : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso A.1 := rfl

@[expose] noncomputable def projHom (Q : QuadraticForm K (Fin d → K)) :
    orthDerived Q →* matrixProjectiveDerived Q :=
  (matrixProjectiveProjection Q).comp (derivedEquiv Q).symm.toMonoidHom

theorem projHom_surjective (Q : QuadraticForm K (Fin d → K)) :
    Function.Surjective (projHom Q) :=
  (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveProjection_surjective
    Q).comp (derivedEquiv Q).symm.surjective

theorem eq_one_of_mul_self_eq_one [CharP K 2] {c : K} (h : c * c = 1) : c = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h0 : (c - 1) ^ 2 = 0 := by linear_combination h + (1 - c) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)

theorem projHom_injective [CharP K 2] {Q : QuadraticForm K (Fin d → K)} (hQ : ∃ v, Q v ≠ 0) :
    Function.Injective (projHom Q) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  set A := (derivedEquiv Q).symm g with hA
  have hA1 : A ∈ matrixDerivedScalars Q := (QuotientGroup.eq_one_iff A).mp hg
  obtain ⟨c, hc⟩ :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.mem_matrixDerivedScalars_iff
      Q A).mp hA1
  have hiso := (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.mem_matrixIsometries_iff
    Q A.val).mp
    (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived_le_isometries Q A.2)
  obtain ⟨v, hv⟩ := hQ
  have h1 := hiso v
  rw [← hc, CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearEquiv_apply]
    at h1
  have hsv : (Matrix.GeneralLinearGroup.scalar (Fin d) c).val.mulVec v = (c : K) • v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [hsv, QuadraticMap.map_smul, smul_eq_mul] at h1
  have hc1 : (c : K) * c = 1 := by
    have := mul_right_cancel₀ hv (h1.trans (one_mul _).symm)
    exact this
  have hc' : c = 1 := Units.ext (eq_one_of_mul_self_eq_one hc1)
  have hA' : A = 1 := by
    apply Subtype.ext
    rw [← hc, hc', map_one]
    rfl
  rw [← (derivedEquiv Q).apply_symm_apply g, ← hA, hA', map_one]

variable (Q : QuadraticForm K (Fin d → K)) (a b : Fin d)

@[expose] noncomputable def pairTorusOf : Subgroup (matrixProjectiveDerived Q) :=
  ((torusLin (K := K) a b).range.subgroupOf (orthDerived Q)).map (projHom Q)

@[expose] noncomputable def pairPerpOf : Subgroup (matrixProjectiveDerived Q) :=
  ((stabSub (K := K) a b).subgroupOf (orthDerived Q)).map (projHom Q)

variable {Q a b}

theorem IsHypCoord.exists_ne_zero (h : IsHypCoord Q a b) : ∃ v, Q v ≠ 0 :=
  ⟨_, by rw [h.map_single_add]; exact one_ne_zero⟩

theorem IsHypCoord.range_torusLin_le [Finite K] [CharP K 2] (h : IsHypCoord Q a b) :
    (torusLin (K := K) a b).range ≤ orthDerived Q := by
  rintro _ ⟨c, rfl⟩
  exact h.torusLin_mem_orthDerived c

theorem card_pairTorusOf [Finite K] [CharP K 2] (h : IsHypCoord Q a b) :
    Nat.card (pairTorusOf Q a b) = Nat.card K - 1 := by
  rw [pairTorusOf, Subgroup.card_map_of_injective (projHom_injective h.exists_ne_zero),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.range_torusLin_le).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective (torusLin_injective (K := K) a b)).toEquiv]
  exact Nat.card_units K

end Proj

section Coordinates

variable {K : Type*} [Field K]

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (reindexQuadraticForm reindexQuadraticForm_apply plusIndexEquiv minusIndexEquiv
    coordinateQuadPlus coordinateQuadMinus)
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

theorem pi_single_comp_equiv {ι : Type*} [DecidableEq ι] {d : ℕ} (e : ι ≃ Fin d) (a : ι) :
    (fun i => (Pi.single (e a) (1 : K) : Fin d → K) (e i)) = Pi.single a 1 := by
  funext i
  simp [Pi.single_apply, e.injective.eq_iff]

theorem IsHypCoord.reindex {ι : Type*} [DecidableEq ι] {d : ℕ} {Q₀ : QuadraticForm K (ι → K)}
    {a b : ι} (h : IsHypCoord Q₀ a b) (e : ι ≃ Fin d) :
    IsHypCoord (reindexQuadraticForm e Q₀) (e a) (e b) where
  ne := e.injective.ne h.ne
  map_left := by rw [reindexQuadraticForm_apply, pi_single_comp_equiv]; exact h.map_left
  map_right := by rw [reindexQuadraticForm_apply, pi_single_comp_equiv]; exact h.map_right
  polar_left v := by
    have hp : polar (reindexQuadraticForm e Q₀) (Pi.single (e a) 1) v =
        polar Q₀ (fun i => (Pi.single (e a) (1 : K) : Fin d → K) (e i)) (fun i => v (e i)) := rfl
    rw [hp, pi_single_comp_equiv, h.polar_left]
  polar_right v := by
    have hp : polar (reindexQuadraticForm e Q₀) (Pi.single (e b) 1) v =
        polar Q₀ (fun i => (Pi.single (e b) (1 : K) : Fin d → K) (e i)) (fun i => v (e i)) := rfl
    rw [hp, pi_single_comp_equiv, h.polar_right]

theorem isHypCoord_quadPlus {n : ℕ} (k : Fin n) :
    IsHypCoord (quadPlus n K) (Sum.inl k) (Sum.inr k) where
  ne := Sum.inl_ne_inr
  map_left := CFSG.ClassicalGroups.Orthogonal.quadPlus_single _
  map_right := CFSG.ClassicalGroups.Orthogonal.quadPlus_single _
  polar_left := CFSG.ClassicalGroups.Orthogonal.polar_single_inl_quadPlus k
  polar_right := CFSG.ClassicalGroups.Orthogonal.polar_single_inr_quadPlus k

theorem isHypCoord_quadMinus {n : ℕ} (b c : K) (k : Fin (n - 1)) :
    IsHypCoord (quadMinus n K b c) (Sum.inl k) (Sum.inr (Sum.inl k)) where
  ne := Sum.inl_ne_inr
  map_left := CFSG.ClassicalGroups.Orthogonal.quadMinus_single_inl k
  map_right := CFSG.ClassicalGroups.Orthogonal.quadMinus_single_inr k
  polar_left := CFSG.ClassicalGroups.Orthogonal.polar_single_inl_quadMinus k
  polar_right := CFSG.ClassicalGroups.Orthogonal.polar_single_inr_quadMinus k

variable {n : ℕ}

theorem isHypCoord_coordinateQuadPlus (k : Fin n) :
    IsHypCoord (coordinateQuadPlus n K) (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k)) :=
  (isHypCoord_quadPlus k).reindex (plusIndexEquiv n)

theorem isHypCoord_coordinateQuadMinus (hn : 1 ≤ n) (b c : K) (k : Fin (n - 1)) :
    IsHypCoord (coordinateQuadMinus n K hn b c) (minusIndexEquiv n hn (.inl k))
      (minusIndexEquiv n hn (.inr (.inl k))) :=
  (isHypCoord_quadMinus b c k).reindex (minusIndexEquiv n hn)

@[expose] noncomputable def pairTorus (k : Fin n) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  pairTorusOf (coordinateQuadPlus n K) (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))

@[expose] noncomputable def pairPerp (k : Fin n) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  pairPerpOf (coordinateQuadPlus n K) (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))

@[expose] noncomputable def minusPairTorus (hn : 1 ≤ n) (b c : K) (k : Fin (n - 1)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  pairTorusOf (coordinateQuadMinus n K hn b c) (minusIndexEquiv n hn (.inl k))
    (minusIndexEquiv n hn (.inr (.inl k)))

@[expose] noncomputable def minusPairPerp (hn : 1 ≤ n) (b c : K) (k : Fin (n - 1)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  pairPerpOf (coordinateQuadMinus n K hn b c) (minusIndexEquiv n hn (.inl k))
    (minusIndexEquiv n hn (.inr (.inl k)))

theorem card_pairTorus [Finite K] [CharP K 2] (k : Fin n) :
    Nat.card (pairTorus (K := K) k) = Nat.card K - 1 :=
  card_pairTorusOf (isHypCoord_coordinateQuadPlus k)

theorem card_minusPairTorus [Finite K] [CharP K 2] (hn : 1 ≤ n) (b c : K) (k : Fin (n - 1)) :
    Nat.card (minusPairTorus hn b c k) = Nat.card K - 1 :=
  card_pairTorusOf (isHypCoord_coordinateQuadMinus hn b c k)

end Coordinates

end CFSG.SeitzReduction.OmegaPilot
