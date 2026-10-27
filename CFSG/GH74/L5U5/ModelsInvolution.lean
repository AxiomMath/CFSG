module

public import CFSG.GH74.L5U5.Models
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.GH74.L5U5

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
open scoped MatrixGroups

namespace ModelData

variable {F : Type} [Field F] (M : ModelData F)

@[expose] def J2 : Subgroup ↥M.K4 := (M.H2.map (blkL F)).subgroupOf M.K4

@[expose] def J4 : Subgroup ↥M.K4 := (M.H2.map (blkR F)).subgroupOf M.K4

variable {M}

theorem mem_J2 {g : ↥M.K4} : g ∈ M.J2 ↔ ∃ a ∈ M.H2, (g : GL (Fin 4) F) = blkL F a := by
  rw [J2, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, h.symm⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, h.symm⟩

theorem mem_J4 {g : ↥M.K4} : g ∈ M.J4 ↔ ∃ a ∈ M.H2, (g : GL (Fin 4) F) = blkR F a := by
  rw [J4, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, h.symm⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, h.symm⟩

theorem blkL_mem_J2 {a : GL (Fin 2) F} (ha : a ∈ M.H2) :
    (⟨blkL F a, M.blkL_mem_K4 ha⟩ : ↥M.K4) ∈ M.J2 :=
  mem_J2.2 ⟨a, ha, rfl⟩

theorem blkR_mem_J4 {a : GL (Fin 2) F} (ha : a ∈ M.H2) :
    (⟨blkR F a, M.blkR_mem_K4 ha⟩ : ↥M.K4) ∈ M.J4 :=
  mem_J4.2 ⟨a, ha, rfl⟩

variable (M)

theorem yK_mem_J2 : M.yK ∈ M.J2 := mem_J2.2 ⟨-1, M.neg_one_mem_H2, rfl⟩

theorem xyK_mem_J4 : M.xyK ∈ M.J4 := mem_J4.2 ⟨-1, M.neg_one_mem_H2, rfl⟩

theorem yK_mul_self : M.yK * M.yK = 1 := Subtype.ext yGL_mul_self

theorem xyK_mul_self : M.xyK * M.xyK = 1 := Subtype.ext xyGL_mul_self

theorem xK_mul_self : M.xK * M.xK = 1 := Subtype.ext xGL_mul_self

theorem xK_eq_yK_mul_xyK : M.xK = M.yK * M.xyK := Subtype.ext xGL_eq_yGL_mul_xyGL

theorem yK_mul_xyK_comm : M.yK * M.xyK = M.xyK * M.yK := Subtype.ext yGL_mul_xyGL_comm

theorem xK_mul_yK : M.xK * M.yK = M.xyK := Subtype.ext (by
  change xGL F * yGL F = xyGL F
  rw [xGL, yGL, xyGL, diagGL_mul]
  simp)

theorem xK_eq_yK_mul_xK_mul_yK : M.xK = M.yK * (M.xK * M.yK) := by
  rw [M.xK_mul_yK]
  exact M.xK_eq_yK_mul_xyK

theorem xK_mem_center : M.xK ∈ Subgroup.center ↥M.K4 := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (xGL_comm (g : GL (Fin 4) F)).symm

theorem neg_one_ne_one_gl2 (h2 : (2 : F) ≠ 0) : (-1 : GL (Fin 2) F) ≠ 1 := by
  intro h
  have h0 := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Units.val_neg, Units.val_one] at h0
  exact CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.neg_one_ne_one_matrix
    (ringChar_ne_two_of_two_ne_zero h2) h0

theorem yK_ne_one (h2 : (2 : F) ≠ 0) : M.yK ≠ 1 := by
  intro h
  have h1 : yGL F = 1 := congrArg Subtype.val h
  rw [yGL, ← diagGL_one] at h1
  exact neg_one_ne_one_gl2 h2 (diagGL_inj h1).1

theorem xyK_ne_one (h2 : (2 : F) ≠ 0) : M.xyK ≠ 1 := by
  intro h
  have h1 : xyGL F = 1 := congrArg Subtype.val h
  rw [xyGL, ← diagGL_one] at h1
  exact neg_one_ne_one_gl2 h2 (diagGL_inj h1).2

theorem yK_ne_xK (h2 : (2 : F) ≠ 0) : M.yK ≠ M.xK := by
  intro h
  have h1 : yGL F = xGL F := congrArg Subtype.val h
  rw [yGL, xGL] at h1
  exact neg_one_ne_one_gl2 h2 (diagGL_inj h1).2.symm

theorem orderOf_yK (h2 : (2 : F) ≠ 0) : orderOf M.yK = 2 :=
  orderOf_eq_prime (by rw [sq]; exact M.yK_mul_self) (M.yK_ne_one h2)

theorem orderOf_xyK (h2 : (2 : F) ≠ 0) : orderOf M.xyK = 2 :=
  orderOf_eq_prime (by rw [sq]; exact M.xyK_mul_self) (M.xyK_ne_one h2)

theorem orderOf_xK (h2 : (2 : F) ≠ 0) : orderOf M.xK = 2 :=
  orderOf_eq_prime (by rw [sq]; exact M.xK_mul_self)
    (fun h => xGL_ne_one h2 (congrArg Subtype.val h))

theorem blkL_comm_yGL (a : GL (Fin 2) F) : blkL F a * yGL F = yGL F * blkL F a := by
  rw [blkL_apply, yGL, diagGL_mul, diagGL_mul]
  simp only [mul_neg, neg_mul, mul_one, one_mul]

theorem blkR_comm_yGL (a : GL (Fin 2) F) : blkR F a * yGL F = yGL F * blkR F a := by
  rw [blkR_apply, yGL, diagGL_mul, diagGL_mul]
  simp only [mul_one, one_mul]

theorem blkR_comm_xyGL (a : GL (Fin 2) F) : blkR F a * xyGL F = xyGL F * blkR F a := by
  rw [blkR_apply, xyGL, diagGL_mul, diagGL_mul]
  simp only [mul_neg, neg_mul, mul_one, one_mul]

theorem blkL_comm_xyGL (a : GL (Fin 2) F) : blkL F a * xyGL F = xyGL F * blkL F a := by
  rw [blkL_apply, xyGL, diagGL_mul, diagGL_mul]
  simp only [mul_one, one_mul]

theorem J2_le_centralizer : M.J2 ≤ Subgroup.centralizer ({M.yK} : Set ↥M.K4) := by
  intro g hg
  obtain ⟨a, -, ha⟩ := mem_J2.1 hg
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact Subtype.ext (by
    change yGL F * (g : GL (Fin 4) F) = (g : GL (Fin 4) F) * yGL F
    rw [ha, blkL_comm_yGL])

theorem J4_le_centralizer : M.J4 ≤ Subgroup.centralizer ({M.yK} : Set ↥M.K4) := by
  intro g hg
  obtain ⟨a, -, ha⟩ := mem_J4.1 hg
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact Subtype.ext (by
    change yGL F * (g : GL (Fin 4) F) = (g : GL (Fin 4) F) * yGL F
    rw [ha, blkR_comm_yGL])

theorem J2_comm_J4 {g h : ↥M.K4} (hg : g ∈ M.J2) (hh : h ∈ M.J4) : g * h = h * g := by
  obtain ⟨a, -, ha⟩ := mem_J2.1 hg
  obtain ⟨b, -, hb⟩ := mem_J4.1 hh
  exact Subtype.ext (by
    change (g : GL (Fin 4) F) * (h : GL (Fin 4) F) = (h : GL (Fin 4) F) * (g : GL (Fin 4) F)
    rw [ha, hb, blkL_mul_blkR_comm])

theorem det_conj_gl2 (a' a : GL (Fin 2) F) :
    ((a' * a * a'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (a : Matrix (Fin 2) (Fin 2) F).det := by
  have h : (a' : Matrix (Fin 2) (Fin 2) F).det *
      ((a'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← det_mul, a'.mul_inv, det_one]
  simp only [Units.val_mul, det_mul]
  calc _ = ((a' : Matrix (Fin 2) (Fin 2) F).det *
        ((a'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det) *
        (a : Matrix (Fin 2) (Fin 2) F).det := by ring
    _ = _ := by rw [h, one_mul]

theorem conj_blkL_of_comm (h2 : (2 : F) ≠ 0) {g : GL (Fin 4) F} (hg : g ∈ M.K4)
    (hc : g * yGL F = yGL F * g) {a : GL (Fin 2) F} (ha : a ∈ M.H2) :
    ∃ c ∈ M.H2, g * blkL F a * g⁻¹ = blkL F c := by
  obtain ⟨a', b', rfl, ha', hb', -⟩ := M.exists_diagGL_of_comm h2 hg hc
  refine ⟨a' * a * a'⁻¹, ?_, ?_⟩
  · obtain ⟨h1, h2'⟩ := (M.mem_H2 a).1 ha
    exact (M.mem_H2 _).2 ⟨M.U2.mul_mem (M.U2.mul_mem ha' h1) (M.U2.inv_mem ha'),
      by rw [det_conj_gl2, h2']⟩
  · rw [blkL_apply, diagGL_inv, diagGL_mul, diagGL_mul, blkL_apply]
    simp

theorem conj_blkR_of_comm (h2 : (2 : F) ≠ 0) {g : GL (Fin 4) F} (hg : g ∈ M.K4)
    (hc : g * yGL F = yGL F * g) {a : GL (Fin 2) F} (ha : a ∈ M.H2) :
    ∃ c ∈ M.H2, g * blkR F a * g⁻¹ = blkR F c := by
  obtain ⟨a', b', rfl, ha', hb', -⟩ := M.exists_diagGL_of_comm h2 hg hc
  refine ⟨b' * a * b'⁻¹, ?_, ?_⟩
  · obtain ⟨h1, h2'⟩ := (M.mem_H2 a).1 ha
    exact (M.mem_H2 _).2 ⟨M.U2.mul_mem (M.U2.mul_mem hb' h1) (M.U2.inv_mem hb'),
      by rw [det_conj_gl2, h2']⟩
  · rw [blkR_apply, diagGL_inv, diagGL_mul, diagGL_mul, blkR_apply]
    simp

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] (C J : Subgroup G)
    (h : ∀ g ∈ C, ∀ j ∈ J, g * j * g⁻¹ ∈ J) : C ≤ Subgroup.normalizer (J : Set G) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro j
  constructor
  · intro hj
    exact h g hg j hj
  · intro hj
    have := h g⁻¹ (C.inv_mem hg) _ hj
    simpa [mul_assoc] using this

theorem centralizer_yK_le_normalizer_J2 (h2 : (2 : F) ≠ 0) :
    Subgroup.centralizer ({M.yK} : Set ↥M.K4) ≤ Subgroup.normalizer (M.J2 : Set ↥M.K4) := by
  refine le_normalizer_of_conj_mem _ _ fun g hg j hj => ?_
  rw [Subgroup.mem_centralizer_iff] at hg
  have hc : (g : GL (Fin 4) F) * yGL F = yGL F * (g : GL (Fin 4) F) :=
    (congrArg Subtype.val (hg M.yK (Set.mem_singleton _))).symm
  obtain ⟨a, ha, hja⟩ := mem_J2.1 hj
  obtain ⟨c, hcH, hconj⟩ := M.conj_blkL_of_comm h2 g.2 hc ha
  refine mem_J2.2 ⟨c, hcH, ?_⟩
  change (g : GL (Fin 4) F) * (j : GL (Fin 4) F) * (g : GL (Fin 4) F)⁻¹ = blkL F c
  rw [hja, hconj]

theorem centralizer_yK_le_normalizer_J4 (h2 : (2 : F) ≠ 0) :
    Subgroup.centralizer ({M.yK} : Set ↥M.K4) ≤ Subgroup.normalizer (M.J4 : Set ↥M.K4) := by
  refine le_normalizer_of_conj_mem _ _ fun g hg j hj => ?_
  rw [Subgroup.mem_centralizer_iff] at hg
  have hc : (g : GL (Fin 4) F) * yGL F = yGL F * (g : GL (Fin 4) F) :=
    (congrArg Subtype.val (hg M.yK (Set.mem_singleton _))).symm
  obtain ⟨a, ha, hja⟩ := mem_J4.1 hj
  obtain ⟨c, hcH, hconj⟩ := M.conj_blkR_of_comm h2 g.2 hc ha
  refine mem_J4.2 ⟨c, hcH, ?_⟩
  change (g : GL (Fin 4) F) * (j : GL (Fin 4) F) * (g : GL (Fin 4) F)⁻¹ = blkR F c
  rw [hja, hconj]

theorem centralizer_xyK_le_centralizer_yK :
    Subgroup.centralizer ({M.xyK} : Set ↥M.K4) ≤ Subgroup.centralizer ({M.yK} : Set ↥M.K4) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have h1 := hg M.xyK (Set.mem_singleton _)
  have hx : M.xK * g = g * M.xK := (Subgroup.mem_center_iff.1 M.xK_mem_center g).symm
  have hy : M.yK = M.xK * M.xyK := by
    rw [M.xK_eq_yK_mul_xyK, mul_assoc, M.xyK_mul_self, mul_one]
  calc M.yK * g = (M.xK * M.xyK) * g := by rw [← hy]
    _ = M.xK * (M.xyK * g) := mul_assoc _ _ _
    _ = M.xK * (g * M.xyK) := by rw [h1]
    _ = (M.xK * g) * M.xyK := (mul_assoc _ _ _).symm
    _ = (g * M.xK) * M.xyK := by rw [hx]
    _ = g * (M.xK * M.xyK) := mul_assoc _ _ _
    _ = g * M.yK := by rw [← hy]

theorem J4_le_centralizer_xyK : M.J4 ≤ Subgroup.centralizer ({M.xyK} : Set ↥M.K4) := by
  intro g hg
  obtain ⟨a, -, ha⟩ := mem_J4.1 hg
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact Subtype.ext (by
    change xyGL F * (g : GL (Fin 4) F) = (g : GL (Fin 4) F) * xyGL F
    rw [ha, blkR_comm_xyGL])

theorem centralizer_xyK_le_normalizer_J4 (h2 : (2 : F) ≠ 0) :
    Subgroup.centralizer ({M.xyK} : Set ↥M.K4) ≤ Subgroup.normalizer (M.J4 : Set ↥M.K4) :=
  M.centralizer_xyK_le_centralizer_yK.trans (M.centralizer_yK_le_normalizer_J4 h2)

theorem wK_mul_yK_mul_inv : M.wK * M.yK * M.wK⁻¹ = M.xyK := by
  apply Subtype.ext
  change swapGL F * yGL F * (swapGL F)⁻¹ = xyGL F
  exact swapGL_mul_yGL_mul_inv

theorem wK_mul_xyK_mul_inv : M.wK * M.xyK * M.wK⁻¹ = M.yK := by
  apply Subtype.ext
  change swapGL F * xyGL F * (swapGL F)⁻¹ = yGL F
  exact swapGL_mul_xyGL_mul_inv

theorem wK_conj_J2 : M.J2.map (MulAut.conj M.wK).toMonoidHom = M.J4 := by
  ext j
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, ha, hga⟩ := mem_J2.1 hg
    refine mem_J4.2 ⟨a, ha, ?_⟩
    change swapGL F * (g : GL (Fin 4) F) * (swapGL F)⁻¹ = blkR F a
    rw [hga, blkL_apply, swapGL_mul_diagGL_mul_inv, blkR_apply]
  · intro hj
    obtain ⟨a, ha, hja⟩ := mem_J4.1 hj
    refine ⟨⟨blkL F a, M.blkL_mem_K4 ha⟩, mem_J2.2 ⟨a, ha, rfl⟩, ?_⟩
    apply Subtype.ext
    change swapGL F * blkL F a * (swapGL F)⁻¹ = (j : GL (Fin 4) F)
    rw [hja, blkL_apply, swapGL_mul_diagGL_mul_inv, blkR_apply]

theorem map_blkL_H2_le_K4 : M.H2.map (blkL F) ≤ M.K4 := by
  rintro _ ⟨a, ha, rfl⟩
  exact M.blkL_mem_K4 ha

theorem map_blkR_H2_le_K4 : M.H2.map (blkR F) ≤ M.K4 := by
  rintro _ ⟨a, ha, rfl⟩
  exact M.blkR_mem_K4 ha

@[expose] noncomputable def J2EquivH2 : M.J2 ≃* M.H2 :=
  (Subgroup.subgroupOfEquivOfLe M.map_blkL_H2_le_K4).trans
    (M.H2.equivMapOfInjective (blkL F) blkL_injective).symm

@[expose] noncomputable def J4EquivH2 : M.J4 ≃* M.H2 :=
  (Subgroup.subgroupOfEquivOfLe M.map_blkR_H2_le_K4).trans
    (M.H2.equivMapOfInjective (blkR F) blkR_injective).symm

theorem isClassicalSL2_J2 (h2 : (2 : F) ≠ 0) {F' : Type} [Field F'] (e : SL(2, F') ≃* M.H2) :
    IsClassicalSL2 F' M.J2 M.yK where
  nonempty_mulEquiv := ⟨M.J2EquivH2.trans e.symm⟩
  mem := M.yK_mem_J2
  orderOf_eq_two := M.orderOf_yK h2
  le_centralizer := M.J2_le_centralizer
  centralizer_le_normalizer := M.centralizer_yK_le_normalizer_J2 h2

theorem isClassicalSL2_J4 (h2 : (2 : F) ≠ 0) {F' : Type} [Field F'] (e : SL(2, F') ≃* M.H2) :
    IsClassicalSL2 F' M.J4 M.xyK where
  nonempty_mulEquiv := ⟨M.J4EquivH2.trans e.symm⟩
  mem := M.xyK_mem_J4
  orderOf_eq_two := M.orderOf_xyK h2
  le_centralizer := M.J4_le_centralizer_xyK
  centralizer_le_normalizer := M.centralizer_xyK_le_normalizer_J4 h2

end ModelData

section Frame

structure IsFrame (F' : Type) [Field F'] {K : Type*} [Group K] (x y : K) (J₂ J₄ : Subgroup K) :
    Prop where
  orderOf_x : orderOf x = 2
  x_mem_center : x ∈ Subgroup.center K
  orderOf_y : orderOf y = 2
  y_ne_x : y ≠ x
  x_eq : x = y * (x * y)
  classical₂ : IsClassicalSL2 F' J₂ y
  classical₄ : IsClassicalSL2 F' J₄ (x * y)
  le_centralizer₄ : J₄ ≤ Subgroup.centralizer ({y} : Set K)
  comm : ∀ a ∈ J₂, ∀ b ∈ J₄, a * b = b * a
  exists_conj : ∃ g : K, g * y * g⁻¹ = x * y ∧ J₂.map (MulAut.conj g).toMonoidHom = J₄

theorem isClassicalSL2_map {F' : Type} [Field F'] {G G' : Type*} [Group G] [Group G']
    {J : Subgroup G} {d : G} (h : IsClassicalSL2 F' J d) (e : G ≃* G') :
    IsClassicalSL2 F' (J.map e.toMonoidHom) (e d) where
  nonempty_mulEquiv := by
    obtain ⟨φ⟩ := h.nonempty_mulEquiv
    exact ⟨(J.equivMapOfInjective e.toMonoidHom e.injective).symm.trans φ⟩
  mem := ⟨d, h.mem, rfl⟩
  orderOf_eq_two := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq_two
  le_centralizer := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have := Subgroup.mem_centralizer_iff.1 (h.le_centralizer hj) d (Set.mem_singleton _)
    change e d * e j = e j * e d
    rw [← map_mul, ← map_mul, this]
  centralizer_le_normalizer := by
    intro g' hg'
    obtain ⟨g, rfl⟩ := e.surjective g'
    have hg : g ∈ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hg' ⊢
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      apply e.injective
      rw [map_mul, map_mul]
      exact hg' (e z) (by simp)
    have hn := h.centralizer_le_normalizer hg
    rw [Subgroup.mem_set_normalizer_iff] at hn ⊢
    intro j'
    obtain ⟨j, rfl⟩ := e.surjective j'
    have := hn j
    constructor
    · rintro ⟨j0, hj0, hj0e⟩
      have hj : j0 = j := e.injective hj0e
      subst hj
      exact ⟨g * j0 * g⁻¹, this.1 hj0, by simp⟩
    · rintro ⟨j0, hj0, hj0e⟩
      have hj : j0 = g * j * g⁻¹ := e.injective (by simpa using hj0e)
      subst hj
      exact ⟨j, this.2 hj0, rfl⟩

variable {F : Type} [Field F]

theorem isFrame_of_model {K : Type*} [Group K] {F' : Type} [Field F'] (M : ModelData F)
    (h2 : (2 : F) ≠ 0) (e : K ≃* ↥M.K4) (e2 : SL(2, F') ≃* M.H2) :
    IsFrame F' (e.symm M.xK) (e.symm M.yK) (M.J2.map e.symm.toMonoidHom)
      (M.J4.map e.symm.toMonoidHom) where
  orderOf_x := by rw [MulEquiv.orderOf_eq]; exact M.orderOf_xK h2
  x_mem_center := by
    rw [← mem_center_iff_of_mulEquiv e, MulEquiv.apply_symm_apply]
    exact M.xK_mem_center
  orderOf_y := by rw [MulEquiv.orderOf_eq]; exact M.orderOf_yK h2
  y_ne_x := fun h => M.yK_ne_xK h2 (e.symm.injective h)
  x_eq := by
    rw [← map_mul, ← map_mul, ← M.xK_eq_yK_mul_xK_mul_yK]
  classical₂ := isClassicalSL2_map (M.isClassicalSL2_J2 h2 e2) e.symm
  classical₄ := by
    have := isClassicalSL2_map (M.isClassicalSL2_J4 h2 e2) e.symm
    rwa [← M.xK_mul_yK, map_mul] at this
  le_centralizer₄ := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have := Subgroup.mem_centralizer_iff.1 (M.J4_le_centralizer hj) M.yK (Set.mem_singleton _)
    change e.symm M.yK * e.symm j = e.symm j * e.symm M.yK
    rw [← map_mul, ← map_mul, this]
  comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, M.J2_comm_J4 ha hb]
  exists_conj := by
    refine ⟨e.symm M.wK, ?_, ?_⟩
    · rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, M.wK_mul_yK_mul_inv, ← M.xK_mul_yK, map_mul]
    · have hc : (MulAut.conj (e.symm M.wK)).toMonoidHom.comp e.symm.toMonoidHom =
          e.symm.toMonoidHom.comp (MulAut.conj M.wK).toMonoidHom := by
        ext z
        simp
      rw [Subgroup.map_map, hc, ← Subgroup.map_map, M.wK_conj_J2]

section Models

open CFSG.LieType.Steinberg

theorem exists_frame_lin {K : Type*} [Group K] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 4 = 3) (e : K ≃* StatedSL 4 F) :
    ∃ (x y : K) (J₂ J₄ : Subgroup K), IsFrame F x y J₂ J₄ :=
  ⟨_, _, _, _, isFrame_of_model (ModelData.lin F)
    (two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))) e (lin_sl2_equiv_H2 F)⟩

theorem exists_frame_uni {K : Type*} [Group K] {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (e : K ≃* StatedSU 4 q F) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (x y : K) (J₂ J₄ : Subgroup K),
      Nat.card F' = q ∧ IsFrame F' x y J₂ J₄ := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  obtain ⟨e2⟩ := nonempty_sl2_equiv_uni_H2 hF
  exact ⟨↥(fixedSubfield F p f), inferInstance, inferInstance, _, _, _, _, card_fixedSubfield hF,
    isFrame_of_model (ModelData.uni hF) (two_ne_zero_of_odd_card hodd) e e2⟩

variable {K : Type*} [Group K]

theorem IsSL4Model.exists_frame (h : IsSL4Model K) :
    ∃ (q : ℕ) (F' : Type) (_ : Field F') (_ : Finite F') (x y : K) (J₂ J₄ : Subgroup K),
      Nat.card F' = q ∧ Odd q ∧ IsFrame F' x y J₂ J₄ := by
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · obtain ⟨x, y, J₂, J₄, hfr⟩ := exists_frame_lin hF e
    exact ⟨Nat.card F, F, inferInstance, inferInstance, x, y, J₂, J₄, rfl,
      Nat.odd_iff.2 (by omega), hfr⟩
  · obtain ⟨F', _, _, x, y, J₂, J₄, hc, hfr⟩ := exists_frame_uni hF hq e
    exact ⟨q, F', inferInstance, inferInstance, x, y, J₂, J₄, hc, Nat.odd_iff.2 (by omega), hfr⟩

end Models

end Frame

end CFSG.GH74.L5U5
