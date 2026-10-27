module

public import CFSG.LieType.Chevalley.A2CommutatorInfinitesimal
public import CFSG.GroupActions.NilpotentExpCommutator
public import CFSG.LieType.Steinberg.Adjoint.BaseChange
public import Mathlib.Algebra.MvPolynomial.Eval

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.GroupActions CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

variable {τ : Tag}

section Rat

variable {K : Type*} [CommRing K] [Algebra ℚ K]

theorem xOp_eq_truncExp
    (i : Fin τ.rank) (c : K) : xOp τ K i c = truncExp 4 (infE τ K i) c :=
  xOp_eq_sum_infE_pow i c

theorem yOp_eq_truncExp
    (i : Fin τ.rank) (c : K) : yOp τ K i c = truncExp 4 (infF τ K i) c :=
  yOp_eq_sum_infF_pow i c

theorem truncExp_weylElt_conj
    (i : Fin τ.rank) (X : Module.End K (RootModule τ K)) (z : K) :
    truncExp 4 ((weylElt τ K i 1 : Module.End K (RootModule τ K)) * X *
        (weylElt τ K i (-1) : Module.End K (RootModule τ K))) z =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) * truncExp 4 X z *
        (weylElt τ K i (-1) : Module.End K (RootModule τ K)) := by
  rw [← weylElt_inv]
  exact truncExp_conj 4 _ X z

theorem xOp_commutator_rat
    {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) (c d : K) :
    xOp τ K i c * xOp τ K j d * xOp τ K i (-c) * xOp τ K j (-d) =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) * xOp τ K j (c * d) *
        (weylElt τ K i (-1) : Module.End K (RootModule τ K)) := by
  obtain ⟨h1, -, h3, h4, -, -, h7, -⟩ := a2_infinitesimal_relations τ K i j hij hji
  rw [xOp_eq_truncExp, xOp_eq_truncExp, xOp_eq_truncExp, xOp_eq_truncExp, xOp_eq_truncExp,
    truncExp_commutator (infE_pow_eq_zero i le_rfl) (infE_pow_eq_zero j le_rfl) h7 h3 h4, h1,
    truncExp_weylElt_conj]

theorem yOp_commutator_rat
    {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) (c d : K) :
    yOp τ K i c * yOp τ K j d * yOp τ K i (-c) * yOp τ K j (-d) =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) * yOp τ K j (-(c * d)) *
        (weylElt τ K i (-1) : Module.End K (RootModule τ K)) := by
  obtain ⟨-, -, -, -, h5, h6, -, h8⟩ := a2_infinitesimal_relations τ K i j hij hji
  rw [yOp_eq_truncExp, yOp_eq_truncExp, yOp_eq_truncExp, yOp_eq_truncExp, yOp_eq_truncExp,
    truncExp_commutator (infF_pow_eq_zero i le_rfl) (infF_pow_eq_zero j le_rfl) h8 h5 h6,
    infF_bracket_eq_neg_one_smul hij hji, truncExp_smul, truncExp_weylElt_conj, neg_one_mul]

end Rat

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem baseChange_weylElt_neg_one
    (i : Fin τ.rank) :
    BaseChange f (weylElt τ R i (-1) : Module.End R (RootModule τ R))
      (weylElt τ S i (-1) : Module.End S (RootModule τ S)) := by
  have h := BaseChange.units_inv (BaseChange.weylElt_one (τ := τ) (f := f) i)
  rwa [weylElt_inv, weylElt_inv] at h

theorem baseChange_xOp_commutator
    (i j : Fin τ.rank) (c d : R) :
    BaseChange f (xOp τ R i c * xOp τ R j d * xOp τ R i (-c) * xOp τ R j (-d))
      (xOp τ S i (f c) * xOp τ S j (f d) * xOp τ S i (-f c) * xOp τ S j (-f d)) := by
  have h3 := BaseChange.xOp (τ := τ) (f := f) i (-c)
  have h4 := BaseChange.xOp (τ := τ) (f := f) j (-d)
  rw [map_neg] at h3 h4
  exact (((BaseChange.xOp i c).mul (BaseChange.xOp j d)).mul h3).mul h4

theorem baseChange_yOp_commutator
    (i j : Fin τ.rank) (c d : R) :
    BaseChange f (yOp τ R i c * yOp τ R j d * yOp τ R i (-c) * yOp τ R j (-d))
      (yOp τ S i (f c) * yOp τ S j (f d) * yOp τ S i (-f c) * yOp τ S j (-f d)) := by
  have h3 := BaseChange.yOp (τ := τ) (f := f) i (-c)
  have h4 := BaseChange.yOp (τ := τ) (f := f) j (-d)
  rw [map_neg] at h3 h4
  exact (((BaseChange.yOp i c).mul (BaseChange.yOp j d)).mul h3).mul h4

theorem baseChange_weylElt_conj
    {X : Module.End R (RootModule τ R)}
    {Y : Module.End S (RootModule τ S)} (h : BaseChange f X Y) (i : Fin τ.rank) :
    BaseChange f ((weylElt τ R i 1 : Module.End R (RootModule τ R)) * X *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)))
      ((weylElt τ S i 1 : Module.End S (RootModule τ S)) * Y *
        (weylElt τ S i (-1) : Module.End S (RootModule τ S))) :=
  ((BaseChange.weylElt_one i).mul h).mul (baseChange_weylElt_neg_one f i)

end BaseChange

open MvPolynomial

theorem baseChange_eq_of_rat
    {A₀ B₀ : Module.End (MvPolynomial (Fin 2) ℤ) (RootModule τ (MvPolynomial (Fin 2) ℤ))}
    {A B : Module.End (MvPolynomial (Fin 2) ℚ) (RootModule τ (MvPolynomial (Fin 2) ℚ))}
    (hA : BaseChange (map (Int.castRingHom ℚ)) A₀ A)
    (hB : BaseChange (map (Int.castRingHom ℚ)) B₀ B) (h : A = B) {R : Type*} [CommRing R]
    (g : MvPolynomial (Fin 2) ℤ →+* R) {A' B' : Module.End R (RootModule τ R)}
    (hA' : BaseChange g A₀ A') (hB' : BaseChange g B₀ B') :
    A' = B' := by
  have h₀ : A₀ = B₀ :=
    BaseChange.eq_of_injective (map_injective _ Int.cast_injective) hA (h ▸ hB)
  exact hA'.unique (h₀ ▸ hB')

theorem xOp_commutator
    (R : Type*) [CommRing R] {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) (c d : R) :
    xOp τ R i c * xOp τ R j d * xOp τ R i (-c) * xOp τ R j (-d) =
      (weylElt τ R i 1 : Module.End R (RootModule τ R)) * xOp τ R j (c * d) *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)) := by
  set f₀ : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℚ := map (Int.castRingHom ℚ)
  have hl₀ := baseChange_xOp_commutator (τ := τ) f₀ i j (X 0) (X 1)
  have hr₀ := baseChange_weylElt_conj f₀ (BaseChange.xOp (τ := τ) (f := f₀) j (X 0 * X 1)) i
  rw [map_X, map_X] at hl₀
  rw [map_mul, map_X, map_X] at hr₀
  set g : MvPolynomial (Fin 2) ℤ →+* R := eval₂Hom (Int.castRingHom R) ![c, d]
  have hg0 : g (X 0) = c := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = d := eval₂Hom_X' _ _ _
  have hl := baseChange_xOp_commutator (τ := τ) g i j (X 0) (X 1)
  have hr := baseChange_weylElt_conj _ (BaseChange.xOp (τ := τ) (f := g) j (X 0 * X 1)) i
  rw [hg0, hg1] at hl
  rw [map_mul, hg0, hg1] at hr
  exact baseChange_eq_of_rat hl₀ hr₀ (xOp_commutator_rat hij hji _ _) g hl hr

theorem yOp_commutator
    (R : Type*) [CommRing R] {i j : Fin τ.rank} (hij : τ.cartan i j = -1)
    (hji : τ.cartan j i = -1) (c d : R) :
    yOp τ R i c * yOp τ R j d * yOp τ R i (-c) * yOp τ R j (-d) =
      (weylElt τ R i 1 : Module.End R (RootModule τ R)) * yOp τ R j (-(c * d)) *
        (weylElt τ R i (-1) : Module.End R (RootModule τ R)) := by
  set f₀ : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℚ := map (Int.castRingHom ℚ)
  have hl₀ := baseChange_yOp_commutator (τ := τ) f₀ i j (X 0) (X 1)
  have hr₀ := baseChange_weylElt_conj f₀ (BaseChange.yOp (τ := τ) (f := f₀) j (-(X 0 * X 1))) i
  rw [map_X, map_X] at hl₀
  rw [map_neg, map_mul, map_X, map_X] at hr₀
  set g : MvPolynomial (Fin 2) ℤ →+* R := eval₂Hom (Int.castRingHom R) ![c, d]
  have hg0 : g (X 0) = c := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = d := eval₂Hom_X' _ _ _
  have hl := baseChange_yOp_commutator (τ := τ) g i j (X 0) (X 1)
  have hr := baseChange_weylElt_conj _ (BaseChange.yOp (τ := τ) (f := g) j (-(X 0 * X 1))) i
  rw [hg0, hg1] at hl
  rw [map_neg, map_mul, hg0, hg1] at hr
  exact baseChange_eq_of_rat hl₀ hr₀ (yOp_commutator_rat hij hji _ _) g hl hr

variable (τ) in
theorem a2_simple_root_commutator
    (R : Type*) [CommRing R] (i j : Fin τ.rank)
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) (c d : R) :
    xUnit τ R i c * xUnit τ R j d * xUnit τ R i (-c) * xUnit τ R j (-d) =
        weylElt τ R i 1 * xUnit τ R j (c * d) * weylElt τ R i (-1) ∧
      yUnit τ R i c * yUnit τ R j d * yUnit τ R i (-c) * yUnit τ R j (-d) =
        weylElt τ R i 1 * yUnit τ R j (-(c * d)) * weylElt τ R i (-1) :=
  ⟨Units.ext (xOp_commutator R hij hji c d), Units.ext (yOp_commutator R hij hji c d)⟩

theorem a2_simple_root_commutatorElement
    (R : Type*) [CommRing R] {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) (c d : R) :
    ⁅xUnit τ R i c, xUnit τ R j d⁆ =
        weylElt τ R i 1 * xUnit τ R j (c * d) * (weylElt τ R i 1)⁻¹ ∧
      ⁅yUnit τ R i c, yUnit τ R j d⁆ =
        weylElt τ R i 1 * yUnit τ R j (-(c * d)) * (weylElt τ R i 1)⁻¹ := by
  have hx : ∀ (k : Fin τ.rank) (e : R), (xUnit τ R k e)⁻¹ = xUnit τ R k (-e) :=
    fun _ _ => Units.ext rfl
  have hy : ∀ (k : Fin τ.rank) (e : R), (yUnit τ R k e)⁻¹ = yUnit τ R k (-e) :=
    fun _ _ => Units.ext rfl
  rw [commutatorElement_def, commutatorElement_def, hx, hx, hy, hy, weylElt_inv]
  exact a2_simple_root_commutator τ R i j hij hji c d

end CFSG.LieType.Chevalley
