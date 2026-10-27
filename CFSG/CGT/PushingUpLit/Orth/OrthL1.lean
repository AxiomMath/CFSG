module

public import CFSG.CGT.PushingUpLit.Orth.OrthStd
public import CFSG.CGT.PushingUpLit.Orth.OrthSyl

public section

namespace CFSG.CGT.PushingUpLit.Orth

open Equiv

variable {G : Type*} [Group G] {M Q : Subgroup G}

theorem H5_add {u u' : Vec5} (hu : u 0 = u 1) (hu' : u' 0 = u' 1) : (u + u') 0 = (u + u') 1 := by
  simp [hu, hu']

namespace OrthCfg

variable (C : OrthCfg G M Q)

include C

noncomputable def psi (g : G) (u : Vec5) : Vec5 := C.vec (g * C.elt u * g⁻¹)

variable {C}

theorem conj_elt_mem_Q1 {g : G} (hg : g ∈ Subgroup.normalizer (C.Q1 : Set G)) {u : Vec5}
    (hu : u 0 = u 1) : g * C.elt u * g⁻¹ ∈ C.Q1 :=
  (Subgroup.mem_normalizer_iff.1 hg (C.elt u)).1 (C.mem_Q1_iff.2 ⟨u, hu, rfl⟩)

theorem elt_psi {g : G} (hg : g ∈ Subgroup.normalizer (C.Q1 : Set G)) {u : Vec5} (hu : u 0 = u 1) :
    C.elt (C.psi g u) = g * C.elt u * g⁻¹ :=
  C.elt_vec (C.Q1_le_Q (C.conj_elt_mem_Q1 hg hu))

theorem psi_coord {g : G} (hg : g ∈ Subgroup.normalizer (C.Q1 : Set G)) {u : Vec5}
    (hu : u 0 = u 1) : C.psi g u 0 = C.psi g u 1 := by
  obtain ⟨w, hw, hwe⟩ := C.mem_Q1_iff.1 (C.conj_elt_mem_Q1 hg hu)
  have : C.psi g u = w := by
    unfold psi
    rw [← hwe, C.vec_elt]
  rw [this]
  exact hw

theorem psi_add {g : G} (hg : g ∈ Subgroup.normalizer (C.Q1 : Set G)) {u u' : Vec5}
    (hu : u 0 = u 1) (hu' : u' 0 = u' 1) : C.psi g (u + u') = C.psi g u + C.psi g u' := by
  have hQ := C.Q1_le_Q (C.conj_elt_mem_Q1 hg hu)
  have hQ' := C.Q1_le_Q (C.conj_elt_mem_Q1 hg hu')
  unfold psi
  rw [← C.vec_mul hQ hQ', C.elt_add]
  congr 1
  group

theorem psi_ne_zero {g : G} (hg : g ∈ Subgroup.normalizer (C.Q1 : Set G)) {u : Vec5}
    (hu : u 0 = u 1) (hu0 : u ≠ 0) : C.psi g u ≠ 0 := by
  intro h
  have h1 := C.elt_psi hg hu
  rw [h, C.elt_zero] at h1
  apply C.elt_ne_one hu0
  calc C.elt u = g⁻¹ * (g * C.elt u * g⁻¹) * g := by group
    _ = 1 := by rw [← h1]; group

theorem normalizer_Q1_le [Finite G]
    (hrig : ∀ v : Vec5, Rigid v → Subgroup.centralizer ({C.elt v} : Set G) ≤ M) {g : G}
    (hg : g ∈ Subgroup.normalizer (C.Q1 : Set G)) : g ∈ M := by
  by_contra hgM
  have nr : ∀ u : Vec5, u 0 = u 1 → Rigid u → ¬ Rigid (C.psi g u) := by
    intro u hu hur hrr
    exact hgM (C.rig_fusion hrig hur hrr (C.elt_psi hg hu).symm)
  have hb1 : (![0, 0, 1, 0, 0] : Vec5) 0 = (![0, 0, 1, 0, 0] : Vec5) 1 := by decide
  have hb2 : (![0, 0, 0, 1, 0] : Vec5) 0 = (![0, 0, 0, 1, 0] : Vec5) 1 := by decide
  have hb3 : (![0, 0, 0, 0, 1] : Vec5) 0 = (![0, 0, 0, 0, 1] : Vec5) 1 := by decide
  have hb4 : (![1, 1, 1, 1, 0] : Vec5) 0 = (![1, 1, 1, 1, 0] : Vec5) 1 := by decide
  have hr1 : Rigid (![0, 0, 1, 0, 0] : Vec5) := by decide
  have hr2 : Rigid (![0, 0, 0, 1, 0] : Vec5) := by decide
  have hr3 : Rigid (![0, 0, 0, 0, 1] : Vec5) := by decide
  have hr4 : Rigid (![1, 1, 1, 1, 0] : Vec5) := by decide
  set b1 : Vec5 := ![0, 0, 1, 0, 0] with hb1d
  set b2 : Vec5 := ![0, 0, 0, 1, 0] with hb2d
  set b3 : Vec5 := ![0, 0, 0, 0, 1] with hb3d
  set b4 : Vec5 := ![1, 1, 1, 1, 0] with hb4d
  set x1 := C.psi g b1 with hx1d
  set x2 := C.psi g b2 with hx2d
  set x3 := C.psi g b3 with hx3d
  set x4 := C.psi g b4 with hx4d
  have hx1 : x1 ∈ nonrig5 :=
    mem_nonrig5 _ (C.psi_coord hg hb1) (C.psi_ne_zero hg hb1 (by decide)) (nr _ hb1 hr1)
  have hx2 : x2 ∈ nonrig5 :=
    mem_nonrig5 _ (C.psi_coord hg hb2) (C.psi_ne_zero hg hb2 (by decide)) (nr _ hb2 hr2)
  have hx3 : x3 ∈ nonrig5 :=
    mem_nonrig5 _ (C.psi_coord hg hb3) (C.psi_ne_zero hg hb3 (by decide)) (nr _ hb3 hr3)
  have hx4 : x4 ∈ nonrig5 :=
    mem_nonrig5 _ (C.psi_coord hg hb4) (C.psi_ne_zero hg hb4 (by decide)) (nr _ hb4 hr4)
  have h12 := H5_add hb1 hb2
  have h13 := H5_add hb1 hb3
  have h14 := H5_add hb1 hb4
  have h23 := H5_add hb2 hb3
  have h24 := H5_add hb2 hb4
  have h34 := H5_add hb3 hb4
  have h123 := H5_add h12 hb3
  have h124 := H5_add h12 hb4
  have h134 := H5_add h13 hb4
  have h234 := H5_add h23 hb4
  have h1234 := H5_add h123 hb4
  have s12 : x1 + x2 = C.psi g (b1 + b2) := (C.psi_add hg hb1 hb2).symm
  have s13 : x1 + x3 = C.psi g (b1 + b3) := (C.psi_add hg hb1 hb3).symm
  have s14 : x1 + x4 = C.psi g (b1 + b4) := (C.psi_add hg hb1 hb4).symm
  have s23 : x2 + x3 = C.psi g (b2 + b3) := (C.psi_add hg hb2 hb3).symm
  have s24 : x2 + x4 = C.psi g (b2 + b4) := (C.psi_add hg hb2 hb4).symm
  have s34 : x3 + x4 = C.psi g (b3 + b4) := (C.psi_add hg hb3 hb4).symm
  have s123 : x1 + x2 + x3 = C.psi g (b1 + b2 + b3) := by
    rw [s12]; exact (C.psi_add hg h12 hb3).symm
  have s124 : x1 + x2 + x4 = C.psi g (b1 + b2 + b4) := by
    rw [s12]; exact (C.psi_add hg h12 hb4).symm
  have s134 : x1 + x3 + x4 = C.psi g (b1 + b3 + b4) := by
    rw [s13]; exact (C.psi_add hg h13 hb4).symm
  have s234 : x2 + x3 + x4 = C.psi g (b2 + b3 + b4) := by
    rw [s23]; exact (C.psi_add hg h23 hb4).symm
  have s1234 : x1 + x2 + x3 + x4 = C.psi g (b1 + b2 + b3 + b4) := by
    rw [s123]; exact (C.psi_add hg h123 hb4).symm
  have hgood : good5 x1 x2 x3 x4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [s12]; exact C.psi_ne_zero hg h12 (by decide)
    · rw [s13]; exact C.psi_ne_zero hg h13 (by decide)
    · rw [s14]; exact C.psi_ne_zero hg h14 (by decide)
    · rw [s23]; exact C.psi_ne_zero hg h23 (by decide)
    · rw [s24]; exact C.psi_ne_zero hg h24 (by decide)
    · rw [s34]; exact C.psi_ne_zero hg h34 (by decide)
    · rw [s123]; exact C.psi_ne_zero hg h123 (by decide)
    · rw [s124]; exact C.psi_ne_zero hg h124 (by decide)
    · rw [s134]; exact C.psi_ne_zero hg h134 (by decide)
    · rw [s234]; exact C.psi_ne_zero hg h234 (by decide)
    · rw [s1234]; exact C.psi_ne_zero hg h1234 (by decide)
  have hhit := F1core x1 hx1 x2 hx2 x3 hx3 x4 hx4 hgood
  rcases hhit with h | h | h
  ·
    apply nr (b3 + b4) h34 (by decide)
    rw [← s34]; exact rigid_of_mem_lam5 _ h
  · apply nr (b1 + b3 + b4) h134 (by decide)
    rw [← s134]; exact rigid_of_mem_lam5 _ h
  · apply nr (b2 + b3 + b4) h234 (by decide)
    rw [← s234]; exact rigid_of_mem_lam5 _ h

end OrthCfg

end CFSG.CGT.PushingUpLit.Orth
