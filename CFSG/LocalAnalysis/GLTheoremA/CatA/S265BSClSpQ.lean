module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClQuad
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.Quad

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks (fixedByEnd mem_fixedByEnd)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux (card_two_charP)

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

omit [Finite F] [FiniteDimensional F V] in
private theorem exists_quadraticForm_polar_eq (hF : Nat.card F = 2) {f : LinearMap.BilinForm F V}
    (halt : f.IsAlt) {d : V ≃ₗ[F] V} (hd3 : d ^ 3 = 1) (hd : fixedByEnd d = ⊥)
    (hdf : ∀ u v, f (d u) (d v) = f u v) :
    ∃ Q : QuadraticForm F V, (∀ v, Q v = f v (d v)) ∧ ∀ x y, polar Q x y = f x y := by
  haveI := card_two_charP hF
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hww : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul F x, h2, zero_smul]
  have hneg : ∀ x : V, -x = x := fun x => neg_eq_of_add_eq_zero_right (hww x)
  have hd3' : ∀ y, d (d (d y)) = y := fun y => by
    have h := LinearEquiv.congr_fun hd3 y
    simpa [pow_succ] using h
  have hd2 : ∀ v, d (d v) + d v + v = 0 := fun v => by
    have hw : d (d (d v) + d v + v) = d (d v) + d v + v := by
      rw [map_add, map_add, hd3' v]
      abel
    have hmem : d (d v) + d v + v ∈ fixedByEnd d := mem_fixedByEnd.2 hw
    rw [hd] at hmem
    exact (Submodule.mem_bot F).1 hmem
  have hsym : ∀ x y, f y x = f x y := fun x y => by
    rw [← halt.neg_eq x y]
    exact neg_eq_of_add_eq_zero_right (by rw [← two_mul, h2, zero_mul])
  refine ⟨LinearMap.BilinMap.toQuadraticMap (f.compl₂ (d : V →ₗ[F] V)), fun v => rfl,
    fun x y => ?_⟩
  rw [LinearMap.BilinMap.polar_toQuadraticMap]
  show f x (d y) + f y (d x) = f x y
  rw [(hsym (d x) y).trans (hdf (d x) y).symm, ← LinearMap.map_add₂]
  have h3 : x + d (d x) = d x := by
    have : x + d (d x) + d x = 0 := by rw [← hd2 x]; abel
    rw [eq_neg_of_add_eq_zero_left this, hneg]
  rw [h3]
  exact hdf x y

theorem glaPLayer_inf_ne_bot_of_symplectic (hF : Nat.card F = 2) (hV : finrank F V = 10)
    {f : LinearMap.BilinForm F V} (halt : f.IsAlt) (hnd : f.Nondegenerate)
    {d e : V ≃ₗ[F] V} (hd3 : d ^ 3 = 1) (he3 : e ^ 3 = 1) (hde : d * e = e * d)
    (hdf : ∀ u v, f (d u) (d v) = f u v) (hef : ∀ u v, f (e u) (e v) = f u v)
    (hd : fixedByEnd d = ⊥) (he : finrank F ↥(fixedByEnd e) = 8)
    {X : Subgroup (V ≃ₗ[F] V)} (hX : ∀ g : V ≃ₗ[F] V, (∀ u v, f (g u) (g v) = f u v) → g ∈ X)
    (hXf : ∀ g ∈ X, ∀ u v, f (g u) (g v) = f u v) :
    GLAPLayer 3 (X ⊓ Subgroup.centralizer ({d} : Set (V ≃ₗ[F] V)) ⊓
      Subgroup.centralizer ({e} : Set (V ≃ₗ[F] V))) ≠ ⊥ := by
  obtain ⟨Q, hQv, hQp⟩ := exists_quadraticForm_polar_eq hF halt hd3 hd hdf
  have hQinv : ∀ g : V ≃ₗ[F] V, (∀ u v, f (g u) (g v) = f u v) → g * d = d * g →
      ∀ v, Q (g v) = Q v := fun g hg hgd v => by
    have h : g (d v) = d (g v) := LinearEquiv.congr_fun hgd v
    rw [hQv, hQv, ← h, hg]
  have hpol : polarBilin Q = f := LinearMap.ext₂ fun x y => by rw [polarBilin_apply_apply, hQp]
  refine glaPLayer_inf_ne_bot_of_quadratic hF hV (by rw [hpol]; exact hnd) hd3 he3 hde
    (hQinv d hdf rfl) (hQinv e hef hde.symm) hd he (fun a _ _ _ j hj => ?_)
    fun g hg hgd _ => hQinv g (hXf g hg) hgd
  have hjQ := (mem_isometryCentralizer.1
    (specialBlock_le_isometryCentralizer (Q := Q) (x := a) (cyc3 F) hj)).1
  refine hX j fun u v => ?_
  rw [← hQp, ← hQp]
  show Q (j u + j v) - Q (j u) - Q (j v) = Q (u + v) - Q u - Q v
  rw [← map_add j, hjQ, hjQ, hjQ]

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
