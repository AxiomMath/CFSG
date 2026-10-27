module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.Basic

import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

open _root_.QuadraticMap
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup mem_omegaGroup)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section General

variable {n : ℕ}

theorem Q_apply_of_mem_Om {g : V n ≃ₗ[ZMod 2] V n} (hg : g ∈ Om n) (v : V n) :
    Q n (g v) = Q n v :=
  map_of_mem (mem_omegaGroup.1 hg).1 v

theorem polar_apply_of_mem_Om {g : V n ≃ₗ[ZMod 2] V n} (hg : g ∈ Om n) (v w : V n) :
    polar (Q n) (g v) (g w) = polar (Q n) v w :=
  polar_map_of_mem (mem_omegaGroup.1 hg).1 v w

variable (n) in
theorem finrank_V : Module.finrank (ZMod 2) (V n) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  omega

theorem polar_single_inl_inr (i : Fin n) :
    polar (Q n) (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr i) 1) = 1 := by
  rw [polar_Q, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem polar_single_single_of_planeOf_ne {k k' : Fin n ⊕ Fin n} (h : planeOf k ≠ planeOf k') :
    polar (Q n) (Pi.single k 1) (Pi.single k' 1) = 0 := by
  rw [polar_Q]
  rcases k with a | a <;> rcases k' with b | b <;>
    simp only [planeOf, Sum.elim_inl, Sum.elim_inr] at h
  · refine Finset.sum_eq_zero fun j _ => ?_
    simp [Pi.single_apply]
  · refine Finset.sum_eq_zero fun j _ => ?_
    by_cases ha : a = j <;> by_cases hb : b = j <;> simp_all
  · refine Finset.sum_eq_zero fun j _ => ?_
    by_cases ha : a = j <;> by_cases hb : b = j <;> simp_all
  · refine Finset.sum_eq_zero fun j _ => ?_
    simp [Pi.single_apply]

end General

structure FrameVert where
  typ : Fin 5
  u : V 6
  w : V 6
  Q_u : Q 6 u = 1
  Q_w : Q 6 w = 1
  polar_u_w : polar (Q 6) u w = 1

namespace FrameVert

theorem ext {x y : FrameVert} (htyp : x.typ = y.typ) (hu : x.u = y.u) (hw : x.w = y.w) :
    x = y := by
  obtain ⟨_, _, _, _, _, _⟩ := x
  obtain ⟨_, _, _, _, _, _⟩ := y
  cases htyp
  cases hu
  cases hw
  rfl

abbrev plane (x : FrameVert) : Submodule (ZMod 2) (V 6) :=
  Submodule.span (ZMod 2) {x.u, x.w}

@[expose] def Orth (x y : FrameVert) : Prop :=
  polar (Q 6) x.u y.u = 0 ∧ polar (Q 6) x.u y.w = 0 ∧ polar (Q 6) x.w y.u = 0 ∧
    polar (Q 6) x.w y.w = 0

theorem orth_comm {x y : FrameVert} : x.Orth y ↔ y.Orth x := by
  rw [Orth, Orth, polar_comm (Q 6) y.u x.u, polar_comm (Q 6) y.u x.w, polar_comm (Q 6) y.w x.u,
    polar_comm (Q 6) y.w x.w]
  exact ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₃, h₂, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₃, h₂, h₄⟩⟩

theorem mem_orthogonal_plane_iff (x : FrameVert) (v : V 6) :
    v ∈ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) x.plane ↔
      polar (Q 6) x.u v = 0 ∧ polar (Q 6) x.w v = 0 := by
  rw [FrameVert.plane, LinearMap.BilinForm.mem_orthogonal_span_pair_iff,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]

theorem orth_iff_plane_le_orthogonal {x y : FrameVert} :
    x.Orth y ↔ y.plane ≤ LinearMap.BilinForm.orthogonal (polarBilin (Q 6)) x.plane := by
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

end FrameVert

@[expose] def frameGraph : SimpleGraph FrameVert where
  Adj x y := x.typ ≠ y.typ ∧ x.Orth y
  symm := ⟨fun _ _ h => ⟨h.1.symm, FrameVert.orth_comm.1 h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem frameGraph_adj_iff {x y : FrameVert} :
    frameGraph.Adj x y ↔ x.typ ≠ y.typ ∧ x.Orth y :=
  Iff.rfl

instance : SMul ↥(Om 6) FrameVert where
  smul g x :=
    { typ := x.typ
      u := (g : V 6 ≃ₗ[ZMod 2] V 6) x.u
      w := (g : V 6 ≃ₗ[ZMod 2] V 6) x.w
      Q_u := by rw [Q_apply_of_mem_Om g.2, x.Q_u]
      Q_w := by rw [Q_apply_of_mem_Om g.2, x.Q_w]
      polar_u_w := by rw [polar_apply_of_mem_Om g.2, x.polar_u_w] }

@[simp] theorem typ_smul (g : ↥(Om 6)) (x : FrameVert) : (g • x).typ = x.typ := rfl

@[simp] theorem u_smul (g : ↥(Om 6)) (x : FrameVert) :
    (g • x).u = (g : V 6 ≃ₗ[ZMod 2] V 6) x.u := rfl

@[simp] theorem w_smul (g : ↥(Om 6)) (x : FrameVert) :
    (g • x).w = (g : V 6 ≃ₗ[ZMod 2] V 6) x.w := rfl

instance : MulAction ↥(Om 6) FrameVert where
  one_smul _ := FrameVert.ext rfl rfl rfl
  mul_smul _ _ _ := FrameVert.ext rfl rfl rfl

theorem frameGraph_adj_smul (g : ↥(Om 6)) {x y : FrameVert} (h : frameGraph.Adj x y) :
    frameGraph.Adj (g • x) (g • y) := by
  rw [frameGraph_adj_iff] at h ⊢
  refine ⟨by simpa using h.1, ?_⟩
  rw [FrameVert.Orth] at h ⊢
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h.2
  simp only [u_smul, w_smul]
  rw [polar_apply_of_mem_Om g.2, polar_apply_of_mem_Om g.2,
    polar_apply_of_mem_Om g.2, polar_apply_of_mem_Om g.2]
  exact ⟨h₁, h₂, h₃, h₄⟩

@[expose] def stdVert (j : Fin 5) (i : Fin 6) : FrameVert where
  typ := j
  u := Pi.single (Sum.inl i) 1
  w := Pi.single (Sum.inr i) 1
  Q_u := Q_single 6 _
  Q_w := Q_single 6 _
  polar_u_w := polar_single_inl_inr i

@[simp] theorem typ_stdVert (j : Fin 5) (i : Fin 6) : (stdVert j i).typ = j := rfl

theorem frameGraph_adj_stdVert {j j' : Fin 5} {i i' : Fin 6} (hj : j ≠ j') (hi : i ≠ i') :
    frameGraph.Adj (stdVert j i) (stdVert j' i') := by
  rw [frameGraph_adj_iff]
  refine ⟨hj, ?_⟩
  rw [FrameVert.Orth]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [stdVert] using polar_single_single_of_planeOf_ne (n := 6)
      (k := Sum.inl i) (k' := Sum.inl i') (by simpa [planeOf] using hi)
  · simpa [stdVert] using polar_single_single_of_planeOf_ne (n := 6)
      (k := Sum.inl i) (k' := Sum.inr i') (by simpa [planeOf] using hi)
  · simpa [stdVert] using polar_single_single_of_planeOf_ne (n := 6)
      (k := Sum.inr i) (k' := Sum.inl i') (by simpa [planeOf] using hi)
  · simpa [stdVert] using polar_single_single_of_planeOf_ne (n := 6)
      (k := Sum.inr i) (k' := Sum.inr i') (by simpa [planeOf] using hi)

private lemma single_mem_planeSpan_of_planeOf_eq {i : Fin 6} {k : Fin 6 ⊕ Fin 6}
    (hk : planeOf k = i) : (Pi.single k 1 : V 6) ∈ planeSpan 6 {i} := by
  rw [mem_planeSpan]
  intro l hl
  by_cases hlk : l = k
  · subst hlk
    exact absurd (by simpa using hk) hl
  · simp [hlk]

private lemma eq_smul_single_add_of_mem_planeSpan {i : Fin 6} {v : V 6}
    (hv : v ∈ planeSpan 6 {i}) :
    v = v (Sum.inl i) • (Pi.single (Sum.inl i) 1 : V 6) +
      v (Sum.inr i) • (Pi.single (Sum.inr i) 1 : V 6) := by
  funext k
  rcases k with a | a
  · by_cases ha : a = i
    · simp [ha]
    · have h0 : v (Sum.inl a) = 0 :=
        (mem_planeSpan.mp hv) _ (by simp [planeOf, ha])
      simp [ha, h0]
  · by_cases ha : a = i
    · simp [ha]
    · have h0 : v (Sum.inr a) = 0 :=
        (mem_planeSpan.mp hv) _ (by simp [planeOf, ha])
      simp [ha, h0]

theorem mem_stabilizer_stdVert_iff {j : Fin 5} {i : Fin 6} {g : ↥(Om 6)} :
    g ∈ MulAction.stabilizer ↥(Om 6) (stdVert j i) ↔
      (g : V 6 ≃ₗ[ZMod 2] V 6) ∈ supp 6 {i}ᶜ := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have hu : (g : V 6 ≃ₗ[ZMod 2] V 6) (Pi.single (Sum.inl i) 1) =
        Pi.single (Sum.inl i) 1 := by
      simpa [stdVert] using congrArg FrameVert.u h
    have hw : (g : V 6 ≃ₗ[ZMod 2] V 6) (Pi.single (Sum.inr i) 1) =
        Pi.single (Sum.inr i) 1 := by
      simpa [stdVert] using congrArg FrameVert.w h
    rw [mem_supp]
    refine ⟨g.2, ?_⟩
    intro v hv
    rw [compl_compl] at hv
    rw [eq_smul_single_add_of_mem_planeSpan hv]
    rw [map_add, map_smul, map_smul, hu, hw]
  · intro h
    rw [mem_supp] at h
    have hfix : ∀ v ∈ planeSpan 6 {i}, (g : V 6 ≃ₗ[ZMod 2] V 6) v = v :=
      fun v hv => h.2 v (by simpa only [compl_compl] using hv)
    refine FrameVert.ext rfl ?_ ?_
    · simpa [stdVert] using
        hfix _ (single_mem_planeSpan_of_planeOf_eq (by simp [planeOf]))
    · simpa [stdVert] using
        hfix _ (single_mem_planeSpan_of_planeOf_eq (by simp [planeOf]))

end CFSG.ClassicalGroups.Orthogonal.SixPlane
