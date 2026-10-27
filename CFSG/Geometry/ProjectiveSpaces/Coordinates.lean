module

public import CFSG.Geometry.ProjectiveSpaces.TraceEndomorphisms
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import CFSG.Geometry.ProjectiveSpaces.Dimension

public section

open scoped LinearAlgebra.Projectivization

namespace CFSG.Geometry.ProjectiveSpaces

namespace ProjectiveSpace

universe u

section Algebra

variable {K M : Type*} [Ring K] [AddCommGroup M] [Module K M]

theorem exists_smul_add_smul_one_one {x y z : M} :
    (∃ a b : K, a • ((1 : K), x) + b • ((1 : K), y) = ((1 : K), z)) ↔
      ∃ b : K, b • (y - x) = z - x := by
  constructor
  · rintro ⟨a, b, h⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨b, ?_⟩
    rw [← h2, eq_sub_of_add_eq h1, sub_smul, one_smul, smul_sub]
    abel
  · rintro ⟨b, h⟩
    refine ⟨1 - b, b, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, sub_add_cancel,
      Prod.mk.injEq, true_and]
    rw [smul_sub] at h
    calc (1 - b) • x + b • y = x + (b • y - b • x) := by rw [sub_smul, one_smul]; abel
      _ = z := by rw [h]; abel

theorem exists_smul_add_smul_one_one_zero {x y z : M} :
    (∃ a b : K, a • ((1 : K), x) + b • ((1 : K), y) = ((0 : K), z)) ↔
      ∃ b : K, b • (y - x) = z := by
  constructor
  · rintro ⟨a, b, h⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨b, ?_⟩
    rw [← h2, eq_neg_of_add_eq_zero_left h1, neg_smul, smul_sub]
    abel
  · rintro ⟨b, h⟩
    refine ⟨-b, b, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, neg_add_cancel,
      Prod.mk.injEq, true_and]
    rw [neg_smul, ← h, smul_sub]
    abel

theorem exists_smul_add_smul_one_zero {x y z : M} :
    (∃ a b : K, a • ((1 : K), x) + b • ((0 : K), y) = ((1 : K), z)) ↔
      ∃ b : K, b • y = z - x := by
  constructor
  · rintro ⟨a, b, h⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, mul_zero, add_zero,
      Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨b, ?_⟩
    rw [← h2, h1, one_smul]
    abel
  · rintro ⟨b, h⟩
    refine ⟨1, b, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, add_zero, one_smul,
      Prod.mk.injEq, true_and]
    rw [h]
    abel

theorem exists_smul_add_smul_one_zero_zero {x y z : M} :
    (∃ a b : K, a • ((1 : K), x) + b • ((0 : K), y) = ((0 : K), z)) ↔
      ∃ b : K, b • y = z := by
  constructor
  · rintro ⟨a, b, h⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_one, mul_zero, add_zero,
      Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨b, ?_⟩
    rw [← h2, h1, zero_smul, zero_add]
  · rintro ⟨b, h⟩
    refine ⟨0, b, ?_⟩
    simp only [Prod.smul_mk, smul_eq_mul, mul_zero, zero_smul, zero_add, Prod.mk.injEq,
      true_and]
    exact h

theorem not_exists_smul_add_smul_zero_zero_one [Nontrivial K] {x y z : M} :
    ¬ ∃ a b : K, a • ((0 : K), x) + b • ((0 : K), y) = ((1 : K), z) := by
  rintro ⟨a, b, h⟩
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, add_zero,
    Prod.mk.injEq] at h
  exact zero_ne_one h.1

theorem exists_smul_add_smul_zero_zero {x y z : M} :
    (∃ a b : K, a • ((0 : K), x) + b • ((0 : K), y) = ((0 : K), z)) ↔
      ∃ a b : K, a • x + b • y = z := by
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, add_zero, Prod.mk.injEq,
    true_and]

end Algebra

variable {P : Type u} {G : ProjectiveSpace P} {H : Set P} {hA : G.AffineData H}

theorem mem_line_of_mem_plane (hH : G.IsHyperplane H) {d e o f : P} (hde : d ≠ e) (hd : d ∈ H)
    (he : e ∈ H) (ho : o ∉ H) (hf : f ∈ G.plane d e o) (hfH : f ∈ H) : f ∈ G.line d e := by
  have h : ¬ G.Collinear d e o := G.not_collinear_of_not_mem hH.isSubspace hde hd he ho
  by_contra hfl
  have hT := (G.isSubspace_plane h).inter hH.isSubspace
  have hdef : ¬ G.Collinear d e f := fun h' => hfl ((G.collinear_iff_of_ne hde).1 h')
  have he' := G.eq_plane_of_subset h hT Set.inter_subset_left ⟨G.left_mem_plane d e o, hd⟩
    ⟨G.middle_mem_plane d e o, he⟩ ⟨hf, hfH⟩ hdef
  have hoT : o ∈ G.plane d e o ∩ H := by
    rw [he']
    exact G.right_mem_plane d e o
  exact ho hoT.2

variable (hA) in
@[expose] noncomputable def vecTo {o : P} (ho : o ∉ H) {x : P} (hx : x ∉ H) : Vec hA :=
  (Vec.exists_apply_eq hA ho hx).choose

theorem vecTo_apply {o : P} (ho : o ∉ H) {x : P} (hx : x ∉ H) : vecTo hA ho hx o = x :=
  (Vec.exists_apply_eq hA ho hx).choose_spec

theorem vecTo_sub_apply {o : P} (ho : o ∉ H) {p r : P} (hp : p ∉ H) (hr : r ∉ H) :
    (vecTo hA ho hr - vecTo hA ho hp) p = r := by
  have h1 : (-vecTo hA ho hp) p = o := by
    have := Vec.neg_apply_apply (vecTo hA ho hp) o
    rwa [vecTo_apply] at this
  rw [Vec.sub_apply, h1, vecTo_apply]

variable (hA) in
@[expose] noncomputable def dirVec {d : P} (hd : d ∈ H) : Vec hA :=
  (exists_ne_zero_mem_dirSub hA hd).choose

theorem dirVec_mem {d : P} (hd : d ∈ H) : dirVec hA hd ∈ dirSub hA d hd :=
  (exists_ne_zero_mem_dirSub hA hd).choose_spec.1

theorem dirVec_ne_zero {d : P} (hd : d ∈ H) : dirVec hA hd ≠ 0 :=
  (exists_ne_zero_mem_dirSub hA hd).choose_spec.2

variable (hA) in
open Classical in
@[expose] noncomputable def coord {o : P} (ho : o ∉ H) (p : P) : Scalar hA × Vec hA :=
  if hp : p ∈ H then (0, dirVec hA hp) else (1, vecTo hA ho hp)

theorem coord_of_mem {o : P} (ho : o ∉ H) {p : P} (hp : p ∈ H) :
    coord hA ho p = (0, dirVec hA hp) := by
  rw [coord, dite_eq_left hp]

theorem coord_of_not_mem {o : P} (ho : o ∉ H) {p : P} (hp : p ∉ H) :
    coord hA ho p = (1, vecTo hA ho hp) := by
  rw [coord, dite_eq_right hp]

theorem coord_ne_zero {o : P} (ho : o ∉ H) (p : P) : coord hA ho p ≠ 0 := by
  by_cases hp : p ∈ H
  · rw [coord_of_mem ho hp]
    exact fun h => dirVec_ne_zero hp (congrArg Prod.snd h)
  · rw [coord_of_not_mem ho hp]
    exact fun h => one_ne_zero (congrArg Prod.fst h)

theorem exists_smul_eq_vecTo_sub_iff {o : P} (ho : o ∉ H) {p r d : P} (hp : p ∉ H) (hr : r ∉ H)
    (hd : d ∈ H) {w : Vec hA} (hw : w ∈ dirSub hA d hd) (hw0 : w ≠ 0) :
    (∃ b : Scalar hA, b • w = vecTo hA ho hr - vecTo hA ho hp) ↔ r ∈ G.line p d := by
  have key : vecTo hA ho hr - vecTo hA ho hp ∈ dirSub hA d hd ↔ r ∈ G.line p d := by
    rw [mem_dirSub_iff hp, vecTo_sub_apply ho hp hr]
  rw [← key]
  constructor
  · rintro ⟨b, hb⟩
    rw [← hb]
    exact smul_mem_dirSub b hw
  · intro h
    exact exists_smul_eq hw h hw0

theorem exists_smul_eq_dirVec_iff {r d : P} (hr : r ∈ H) (hd : d ∈ H) {w : Vec hA}
    (hw : w ∈ dirSub hA d hd) (hw0 : w ≠ 0) :
    (∃ b : Scalar hA, b • w = dirVec hA hr) ↔ r = d := by
  constructor
  · rintro ⟨b, hb⟩
    by_contra hrd
    have hm : dirVec hA hr ∈ dirSub hA d hd := by
      rw [← hb]
      exact smul_mem_dirSub b hw
    exact dirVec_ne_zero hr (eq_zero_of_mem_dirSub hrd (dirVec_mem hr) hm)
  · rintro rfl
    exact exists_smul_eq hw (dirVec_mem hr) hw0

theorem exists_smul_add_smul_dirVec_iff {d e f : P} (hd : d ∈ H) (he : e ∈ H) (hf : f ∈ H)
    (hde : d ≠ e) :
    (∃ a b : Scalar hA, a • dirVec hA hd + b • dirVec hA he = dirVec hA hf) ↔
      f ∈ G.line d e := by
  have hH := hA.hyperplane
  obtain ⟨o, ho⟩ := hH.exists_not_mem
  have hdeo : ¬ G.Collinear d e o := G.not_collinear_of_not_mem hH.isSubspace hde hd he ho
  have hπ := G.isSubspace_plane hdeo
  have hδ0 : dirVec hA hf ≠ 0 := dirVec_ne_zero hf
  have hyo : dirVec hA hf o ≠ o := Vec.apply_ne hδ0 ho
  have hyl : dirVec hA hf o ∈ G.line o f := (mem_dirSub_iff ho).1 (dirVec_mem hf)
  have hyH : dirVec hA hf o ∉ H := (dirVec hA hf).map_not_mem ho
  constructor
  · rintro ⟨a, b, h⟩
    have hσ : a • dirVec hA hd ∈ dirSub hA d hd := smul_mem_dirSub a (dirVec_mem hd)
    have hσ' : b • dirVec hA he ∈ dirSub hA e he := smul_mem_dirSub b (dirVec_mem he)
    have hzH : (b • dirVec hA he) o ∉ H := (b • dirVec hA he).map_not_mem ho
    have hz : (b • dirVec hA he) o ∈ G.line o e := (mem_dirSub_iff ho).1 hσ'
    have hy : (a • dirVec hA hd) ((b • dirVec hA he) o) ∈ G.line ((b • dirVec hA he) o) d :=
      (mem_dirSub_iff hzH).1 hσ
    have hyδ : (a • dirVec hA hd) ((b • dirVec hA he) o) = dirVec hA hf o := by
      rw [← h]
      rfl
    have hzπ : (b • dirVec hA he) o ∈ G.plane d e o :=
      hπ.line_subset (G.right_mem_plane d e o) (G.middle_mem_plane d e o) hz
    have hyπ : dirVec hA hf o ∈ G.plane d e o := by
      rw [← hyδ]
      exact hπ.line_subset hzπ (G.left_mem_plane d e o) hy
    have hfπ : f ∈ G.plane d e o := by
      have hl : G.line o (dirVec hA hf o) = G.line o f := G.line_eq_of_mem hyl hyo
      refine hπ.line_subset (G.right_mem_plane d e o) hyπ ?_
      rw [hl]
      exact G.right_mem_line o f
    exact mem_line_of_mem_plane hH hde hd he ho hfπ hf
  · intro hfl
    have hyπ : dirVec hA hf o ∈ G.plane d e o := G.mem_join.2 ⟨f, hfl, hyl⟩
    have hyd : dirVec hA hf o ≠ d := fun h' => hyH (h' ▸ hd)
    have hoe : o ≠ e := fun h' => ho (h' ▸ he)
    obtain ⟨z, hz1, hz2⟩ := G.inter_nonempty_of_mem_plane hdeo (G.right_mem_plane d e o)
      (G.middle_mem_plane d e o) hyπ (G.left_mem_plane d e o) hoe hyd
    have hzH : z ∉ H := by
      intro hzH
      have h1 : z = e := hH.eq_of_mem_line ho hz1 (G.right_mem_line o e) hzH he
      have h2 : z = d := hH.eq_of_mem_line hyH hz2 (G.right_mem_line _ d) hzH hd
      exact hde (h2.symm.trans h1)
    obtain ⟨σ', hσ'⟩ := Vec.exists_apply_eq hA ho hzH
    obtain ⟨σ, hσ⟩ := Vec.exists_apply_eq hA hzH hyH
    have hm' : σ' ∈ dirSub hA e he := by
      rw [mem_dirSub_iff ho, hσ']
      exact hz1
    have hzd : z ≠ d := fun h' => hzH (h' ▸ hd)
    have hm : σ ∈ dirSub hA d hd := by
      rw [mem_dirSub_iff hzH, hσ, G.line_eq_line hzd hz2 (G.right_mem_line _ d)]
      exact G.left_mem_line _ d
    obtain ⟨a, ha⟩ := exists_smul_eq (dirVec_mem hd) hm (dirVec_ne_zero hd)
    obtain ⟨b, hb⟩ := exists_smul_eq (dirVec_mem he) hm' (dirVec_ne_zero he)
    refine ⟨a, b, ?_⟩
    rw [ha, hb]
    refine Vec.eq_of_apply_eq ho ?_
    rw [Vec.add_apply, hσ', hσ]

theorem coord_mem_span_pair_iff_of_not_mem_of_mem {o : P} (ho : o ∉ H) {p q r : P}
    (hp : p ∉ H) (hq : q ∈ H) :
    (∃ a b : Scalar hA, a • coord hA ho p + b • coord hA ho q = coord hA ho r) ↔
      r ∈ G.line p q := by
  have hH := hA.hyperplane
  rw [coord_of_not_mem ho hp, coord_of_mem ho hq]
  by_cases hr : r ∈ H
  · rw [coord_of_mem ho hr, exists_smul_add_smul_one_zero_zero,
      exists_smul_eq_dirVec_iff hr hq (dirVec_mem hq) (dirVec_ne_zero hq)]
    exact ⟨fun h => h ▸ G.right_mem_line p q,
      fun h => hH.eq_of_mem_line hp h (G.right_mem_line p q) hr hq⟩
  · rw [coord_of_not_mem ho hr, exists_smul_add_smul_one_zero,
      exists_smul_eq_vecTo_sub_iff ho hp hr hq (dirVec_mem hq) (dirVec_ne_zero hq)]

theorem coord_mem_span_pair_iff {o : P} (ho : o ∉ H) {p q r : P} (hpq : p ≠ q) :
    (∃ a b : Scalar hA, a • coord hA ho p + b • coord hA ho q = coord hA ho r) ↔
      r ∈ G.line p q := by
  have hH := hA.hyperplane
  by_cases hp : p ∈ H <;> by_cases hq : q ∈ H
  · rw [coord_of_mem ho hp, coord_of_mem ho hq]
    by_cases hr : r ∈ H
    · rw [coord_of_mem ho hr, exists_smul_add_smul_zero_zero,
        exists_smul_add_smul_dirVec_iff hp hq hr hpq]
    · rw [coord_of_not_mem ho hr]
      exact iff_of_false not_exists_smul_add_smul_zero_zero_one
        fun h => hr (hH.isSubspace.line_subset hp hq h)
  · rw [G.line_comm, ← coord_mem_span_pair_iff_of_not_mem_of_mem ho hq hp]
    constructor <;> rintro ⟨a, b, h⟩ <;> exact ⟨b, a, by rw [add_comm]; exact h⟩
  · exact coord_mem_span_pair_iff_of_not_mem_of_mem ho hp hq
  · rw [coord_of_not_mem ho hp, coord_of_not_mem ho hq]
    have hd : G.inf H p q ∈ H := hH.inf_mem hpq
    have hw : vecTo hA ho hq - vecTo hA ho hp ∈ dirSub hA (G.inf H p q) hd := by
      rw [mem_dirSub_iff hp, vecTo_sub_apply ho hp hq, hH.line_inf hp hpq]
      exact G.right_mem_line p q
    have hw0 : vecTo hA ho hq - vecTo hA ho hp ≠ 0 := fun h => hpq (by
      have := vecTo_sub_apply ho hp hq (hA := hA)
      rw [h, Vec.zero_apply] at this
      exact this)
    by_cases hr : r ∈ H
    · rw [coord_of_mem ho hr, exists_smul_add_smul_one_one_zero,
        exists_smul_eq_dirVec_iff hr hd hw hw0]
      exact ⟨fun h => h ▸ hH.inf_mem_line hpq, fun h => hH.eq_inf hp hpq h hr⟩
    · rw [coord_of_not_mem ho hr, exists_smul_add_smul_one_one,
        exists_smul_eq_vecTo_sub_iff ho hp hr hd hw hw0, hH.line_inf hp hpq]

variable (hA) in
@[expose] noncomputable def toProj {o : P} (ho : o ∉ H) (p : P) :
    ℙ (Scalar hA) (Scalar hA × Vec hA) :=
  Projectivization.mk _ (coord hA ho p) (coord_ne_zero ho p)

theorem toProj_injective {o : P} (ho : o ∉ H) : Function.Injective (toProj hA ho) := by
  intro p q h
  rw [toProj, toProj, Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  by_cases hp : p ∈ H <;> by_cases hq : q ∈ H
  · rw [coord_of_mem ho hp, coord_of_mem ho hq, Prod.smul_mk, Prod.mk.injEq] at ha
    by_contra hne
    have hm : dirVec hA hp ∈ dirSub hA q hq := by
      rw [← ha.2]
      exact smul_mem_dirSub a (dirVec_mem hq)
    exact dirVec_ne_zero hp (eq_zero_of_mem_dirSub hne (dirVec_mem hp) hm)
  · rw [coord_of_mem ho hp, coord_of_not_mem ho hq, Prod.smul_mk, Prod.mk.injEq, smul_eq_mul,
      mul_one] at ha
    obtain ⟨h1, h2⟩ := ha
    rw [h1, zero_smul] at h2
    exact absurd h2.symm (dirVec_ne_zero hp)
  · rw [coord_of_not_mem ho hp, coord_of_mem ho hq, Prod.smul_mk, Prod.mk.injEq,
      smul_zero] at ha
    exact absurd ha.1 zero_ne_one
  · rw [coord_of_not_mem ho hp, coord_of_not_mem ho hq, Prod.smul_mk, Prod.mk.injEq,
      smul_eq_mul, mul_one] at ha
    obtain ⟨h1, h2⟩ := ha
    rw [h1, one_smul] at h2
    calc p = vecTo hA ho hp o := (vecTo_apply ho hp).symm
      _ = vecTo hA ho hq o := by rw [h2]
      _ = q := vecTo_apply ho hq

theorem toProj_surjective {o : P} (ho : o ∉ H) : Function.Surjective (toProj hA ho) := by
  intro x
  obtain ⟨u, hu, rfl⟩ : ∃ u hu, x = Projectivization.mk (Scalar hA) u hu :=
    ⟨x.rep, x.rep_nonzero, (Projectivization.mk_rep x).symm⟩
  obtain ⟨c, w⟩ := u
  by_cases hc : c = 0
  · subst hc
    have hw : w ≠ 0 := fun h => hu (by rw [h]; rfl)
    have hd := vdir_mem hw
    refine ⟨vdir w, ?_⟩
    rw [toProj, Projectivization.mk_eq_mk_iff', coord_of_mem ho hd]
    obtain ⟨b, hb⟩ := exists_smul_eq (mem_dirSub_vdir hw) (dirVec_mem hd) hw
    exact ⟨b, by rw [Prod.smul_mk, smul_zero, hb]⟩
  · have hy : (c⁻¹ • w) o ∉ H := (c⁻¹ • w).map_not_mem ho
    refine ⟨(c⁻¹ • w) o, ?_⟩
    rw [toProj, Projectivization.mk_eq_mk_iff', coord_of_not_mem ho hy]
    have hv : vecTo hA ho hy = c⁻¹ • w := Vec.eq_of_apply_eq ho (vecTo_apply ho hy)
    refine ⟨c⁻¹, ?_⟩
    rw [hv, Prod.smul_mk, smul_eq_mul, inv_mul_cancel₀ hc]

theorem toProj_submodule {o : P} (ho : o ∉ H) (p : P) :
    (toProj hA ho p).submodule = Submodule.span (Scalar hA) {coord hA ho p} :=
  Projectivization.submodule_mk _ _

theorem mem_line_iff_le {o : P} (ho : o ∉ H) {p q r : P} (hpq : p ≠ q) :
    r ∈ G.line p q ↔
      (toProj hA ho r).submodule ≤ (toProj hA ho p).submodule ⊔ (toProj hA ho q).submodule := by
  rw [toProj_submodule, toProj_submodule, toProj_submodule, ← Submodule.span_insert,
    Submodule.span_singleton_le_iff_mem, Submodule.mem_span_pair, coord_mem_span_pair_iff ho hpq]

theorem exists_coordinatization (hA : G.AffineData H) :
    ∃ ψ : P ≃ ℙ (Scalar hA) (Scalar hA × Vec hA), ∀ p q r : P, p ≠ q →
      (r ∈ G.line p q ↔ (ψ r).submodule ≤ (ψ p).submodule ⊔ (ψ q).submodule) := by
  obtain ⟨o, ho⟩ := hA.hyperplane.exists_not_mem
  exact ⟨Equiv.ofBijective _ ⟨toProj_injective ho, toProj_surjective ho⟩,
    fun p q r hpq => mem_line_iff_le ho hpq⟩

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
