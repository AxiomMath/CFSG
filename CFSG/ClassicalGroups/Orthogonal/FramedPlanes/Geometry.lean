module

public import CFSG.ClassicalGroups.Orthogonal.FramedPlanes.Hull
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.ClassicalGroups.Orthogonal.FramedPlanes

open Module QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

structure FrameVert (Q : QuadraticForm F V) (ν : F) (n : ℕ) where
  typ : Fin n
  u : V
  w : V
  Q_u : Q u = 1
  Q_w : Q w = ν
  polar_u_w : polar Q u w = 1

variable {Q : QuadraticForm F V} {ν : F} {n : ℕ}

namespace FrameVert

theorem ext {x y : FrameVert Q ν n} (htyp : x.typ = y.typ) (hu : x.u = y.u) (hw : x.w = y.w) :
    x = y := by
  obtain ⟨_, _, _, _, _, _⟩ := x
  obtain ⟨_, _, _, _, _, _⟩ := y
  cases htyp
  cases hu
  cases hw
  rfl

abbrev plane (x : FrameVert Q ν n) : Submodule F V :=
  Submodule.span F {x.u, x.w}

@[expose] def Orth (x y : FrameVert Q ν n) : Prop :=
  polar Q x.u y.u = 0 ∧ polar Q x.u y.w = 0 ∧ polar Q x.w y.u = 0 ∧ polar Q x.w y.w = 0

theorem orth_comm {x y : FrameVert Q ν n} : x.Orth y ↔ y.Orth x := by
  rw [Orth, Orth, polar_comm Q y.u x.u, polar_comm Q y.u x.w, polar_comm Q y.w x.u,
    polar_comm Q y.w x.w]
  exact ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₃, h₂, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₃, h₂, h₄⟩⟩

theorem mem_orthogonal_plane_iff (x : FrameVert Q ν n) (v : V) :
    v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) x.plane ↔
      polar Q x.u v = 0 ∧ polar Q x.w v = 0 := by
  rw [FrameVert.plane, LinearMap.BilinForm.mem_orthogonal_span_pair_iff,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]

theorem orth_iff_plane_le_orthogonal {x y : FrameVert Q ν n} :
    x.Orth y ↔ y.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) x.plane := by
  rw [Orth]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    rw [FrameVert.plane, Submodule.span_le, Set.insert_subset_iff,
      Set.singleton_subset_iff]
    exact ⟨(mem_orthogonal_plane_iff x y.u).2 ⟨h₁, h₃⟩,
      (mem_orthogonal_plane_iff x y.w).2 ⟨h₂, h₄⟩⟩
  · intro h
    rw [FrameVert.plane, Submodule.span_le, Set.insert_subset_iff,
      Set.singleton_subset_iff] at h
    obtain ⟨a, c⟩ := (mem_orthogonal_plane_iff x y.u).1 h.1
    obtain ⟨b, d⟩ := (mem_orthogonal_plane_iff x y.w).1 h.2
    exact ⟨a, b, c, d⟩

private lemma polar_self_eq_zero_of_char_two [CharP F 2] (v : V) : polar Q v v = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [← two_mul, h2, zero_mul]

theorem finrank_plane [CharP F 2] (x : FrameVert Q ν n) : finrank F x.plane = 2 := by
  have hu0 : x.u ≠ 0 := by
    intro h0
    have h1 := x.Q_u
    rw [h0, QuadraticMap.map_zero] at h1
    exact zero_ne_one h1
  have hlin : LinearIndependent F ![x.u, x.w] := by
    rw [LinearIndependent.pair_iff' hu0]
    intro a ha
    have h1 : polar Q x.u (a • x.u) = polar Q x.u x.w := by rw [ha]
    rw [QuadraticMap.polar_smul_right, polar_self_eq_zero_of_char_two, smul_zero,
      x.polar_u_w] at h1
    exact zero_ne_one h1
  have hspan : finrank F (Submodule.span F {x.u, x.w}) = 2 := by
    rw [← Matrix.range_cons_cons_empty x.u x.w ![], finrank_span_eq_card hlin, Fintype.card_fin]
  exact hspan

theorem hullDim_plane [CharP F 2] [Module.Finite F V] (x : FrameVert Q ν n) :
    hullDim Q x.plane = 2 :=
  hullDim_span_pair (by rw [x.polar_u_w]; exact one_ne_zero)

end FrameVert

@[expose] def frameGraph (Q : QuadraticForm F V) (ν : F) (n : ℕ) :
    SimpleGraph (FrameVert Q ν n) where
  Adj x y := x.typ ≠ y.typ ∧ x.Orth y
  symm := ⟨fun _ _ h => ⟨h.1.symm, FrameVert.orth_comm.1 h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem frameGraph_adj_iff {x y : FrameVert Q ν n} :
    (frameGraph Q ν n).Adj x y ↔ x.typ ≠ y.typ ∧ x.Orth y :=
  Iff.rfl

private lemma orthDerived_le_orthogonalGroup (Q : QuadraticForm F V) :
    orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
  Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem Q_apply_of_mem_orthDerived {g : V ≃ₗ[F] V} (hg : g ∈ orthDerived Q) (v : V) :
    Q (g v) = Q v :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (orthDerived_le_orthogonalGroup Q hg) v

theorem polar_apply_of_mem_orthDerived {g : V ≃ₗ[F] V} (hg : g ∈ orthDerived Q) (v w : V) :
    polar Q (g v) (g w) = polar Q v w :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
    (orthDerived_le_orthogonalGroup Q hg) v w

instance : SMul ↥(orthDerived Q) (FrameVert Q ν n) where
  smul g x :=
    { typ := x.typ
      u := (g : V ≃ₗ[F] V) x.u
      w := (g : V ≃ₗ[F] V) x.w
      Q_u := by rw [Q_apply_of_mem_orthDerived g.2, x.Q_u]
      Q_w := by rw [Q_apply_of_mem_orthDerived g.2, x.Q_w]
      polar_u_w := by rw [polar_apply_of_mem_orthDerived g.2, x.polar_u_w] }

@[simp] theorem typ_smul (g : ↥(orthDerived Q)) (x : FrameVert Q ν n) : (g • x).typ = x.typ :=
  rfl

@[simp] theorem u_smul (g : ↥(orthDerived Q)) (x : FrameVert Q ν n) :
    (g • x).u = (g : V ≃ₗ[F] V) x.u :=
  rfl

@[simp] theorem w_smul (g : ↥(orthDerived Q)) (x : FrameVert Q ν n) :
    (g • x).w = (g : V ≃ₗ[F] V) x.w :=
  rfl

instance : MulAction ↥(orthDerived Q) (FrameVert Q ν n) where
  one_smul _ := FrameVert.ext rfl rfl rfl
  mul_smul _ _ _ := FrameVert.ext rfl rfl rfl

theorem frameGraph_adj_smul (g : ↥(orthDerived Q)) {x y : FrameVert Q ν n}
    (h : (frameGraph Q ν n).Adj x y) : (frameGraph Q ν n).Adj (g • x) (g • y) := by
  rw [frameGraph_adj_iff] at h ⊢
  refine ⟨by simpa only [typ_smul] using h.1, ?_⟩
  rw [FrameVert.Orth] at h ⊢
  rcases h with ⟨_, h₁, h₂, h₃, h₄⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simpa only [u_smul, w_smul] using
      (polar_apply_of_mem_orthDerived g.2 _ _).trans (by assumption)

theorem mem_stabilizer_iff {g : ↥(orthDerived Q)} {x : FrameVert Q ν n} :
    g ∈ MulAction.stabilizer ↥(orthDerived Q) x ↔
      (g : V ≃ₗ[F] V) x.u = x.u ∧ (g : V ≃ₗ[F] V) x.w = x.w := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact ⟨by simpa only [u_smul] using congrArg FrameVert.u h,
      by simpa only [w_smul] using congrArg FrameVert.w h⟩
  · rintro ⟨hu, hw⟩
    exact FrameVert.ext (typ_smul g x) (by simpa only [u_smul] using hu)
      (by simpa only [w_smul] using hw)

end CFSG.ClassicalGroups.Orthogonal.FramedPlanes
