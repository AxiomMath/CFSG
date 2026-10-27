module

public import CFSG.Geometry.ProjectiveSpaces.Translations
public import Mathlib.Algebra.Module.Hom
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic

public section

namespace CFSG.Geometry.ProjectiveSpaces

namespace ProjectiveSpace

universe u

variable {P : Type u} {G : ProjectiveSpace P} {H : Set P}

@[ext] structure Vec (hA : G.AffineData H) where
  perm : Equiv.Perm P
  mem : perm ∈ G.translationGroup hA

namespace Vec

variable {hA : G.AffineData H}

instance : CoeFun (Vec hA) (fun _ => P → P) := ⟨fun v => v.perm⟩

instance : Add (Vec hA) := ⟨fun v w => ⟨v.perm * w.perm, mul_mem v.mem w.mem⟩⟩

instance : Zero (Vec hA) := ⟨⟨1, one_mem _⟩⟩

instance : Neg (Vec hA) := ⟨fun v => ⟨v.perm⁻¹, inv_mem v.mem⟩⟩

theorem add_apply (v w : Vec hA) (x : P) : (v + w) x = v (w x) := rfl

theorem zero_apply (x : P) : (0 : Vec hA) x = x := rfl

instance : AddCommGroup (Vec hA) where
  add_assoc _ _ _ := Vec.ext (mul_assoc _ _ _)
  zero_add _ := Vec.ext (one_mul _)
  add_zero _ := Vec.ext (mul_one _)
  neg_add_cancel _ := Vec.ext (inv_mul_cancel _)
  add_comm v w := Vec.ext (translation_mul_comm v.mem w.mem)
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem neg_apply_apply (v : Vec hA) (x : P) : (-v) (v x) = x := v.perm.symm_apply_apply x

theorem sub_apply (v w : Vec hA) (x : P) : (v - w) x = v ((-w) x) := by
  rw [sub_eq_add_neg, add_apply]

theorem perm_eq_one_iff {v : Vec hA} : v.perm = 1 ↔ v = 0 :=
  ⟨fun h => Vec.ext h, fun h => h ▸ rfl⟩

theorem map_not_mem (v : Vec hA) {x : P} (hx : x ∉ H) : v x ∉ H :=
  v.mem.1.map_not_mem x hx

theorem apply_ne {v : Vec hA} (hv : v ≠ 0) {x : P} (hx : x ∉ H) : v x ≠ x :=
  apply_ne_of_ne_one v.mem (fun h => hv (perm_eq_one_iff.1 h)) hx

theorem eq_of_apply_eq {v w : Vec hA} {x : P} (hx : x ∉ H) (h : v x = w x) : v = w :=
  Vec.ext (ProjectiveSpace.eq_of_apply_eq v.mem w.mem hx h)

theorem exists_apply_eq (hA : G.AffineData H) {a b : P} (ha : a ∉ H) (hb : b ∉ H) :
    ∃ v : Vec hA, v a = b := by
  obtain ⟨τ, hτ, h⟩ := G.exists_translation hA ha hb
  exact ⟨⟨τ, hτ⟩, h⟩

end Vec

@[expose] def dirSub (hA : G.AffineData H) (d : P) (hd : d ∈ H) : AddSubgroup (Vec hA) where
  carrier := {v | G.HasDir H v.perm d}
  add_mem' := fun {_ w} hv hw => HasDir.mul hv hw w.mem.1 hd
  zero_mem' := hasDir_one d
  neg_mem' := fun {v} hv => HasDir.inv hv v.mem.1 hd

variable {hA : G.AffineData H}

theorem mem_dirSub {d : P} {hd : d ∈ H} {v : Vec hA} :
    v ∈ dirSub hA d hd ↔ G.HasDir H v.perm d := Iff.rfl

theorem mem_dirSub_iff {d : P} {hd : d ∈ H} {v : Vec hA} {p : P} (hp : p ∉ H) :
    v ∈ dirSub hA d hd ↔ v p ∈ G.line p d :=
  hasDir_iff v.mem hd hp

@[expose] noncomputable def vdir (v : Vec hA) : P := G.dir hA v.perm

theorem vdir_mem {v : Vec hA} (hv : v ≠ 0) : vdir v ∈ H :=
  dir_mem v.mem fun h => hv (Vec.perm_eq_one_iff.1 h)

theorem mem_dirSub_vdir {v : Vec hA} (hv : v ≠ 0) : v ∈ dirSub hA (vdir v) (vdir_mem hv) :=
  hasDir_dir v.mem fun h => hv (Vec.perm_eq_one_iff.1 h)

theorem eq_zero_of_mem_dirSub {d e : P} {hd : d ∈ H} {he : e ∈ H} (hde : d ≠ e) {v : Vec hA}
    (h : v ∈ dirSub hA d hd) (h' : v ∈ dirSub hA e he) : v = 0 :=
  Vec.perm_eq_one_iff.1 (HasDir.eq_one h h' v.mem hd he hde)

theorem exists_ne_zero_mem_dirSub (hA : G.AffineData H) {d : P} (hd : d ∈ H) :
    ∃ v ∈ dirSub hA d hd, v ≠ 0 := by
  obtain ⟨τ, hτ, h1, h⟩ := G.exists_hasDir hA hd
  exact ⟨⟨τ, hτ⟩, h, fun e => h1 (Vec.perm_eq_one_iff.2 e)⟩

theorem exists_vdir_ne (hA : G.AffineData H) (d : P) :
    ∃ v : Vec hA, v ≠ 0 ∧ vdir v ≠ d := by
  obtain ⟨ρ, hρ, h1, h⟩ := G.exists_dir_ne hA (d := d)
  exact ⟨⟨ρ, hρ⟩, fun e => h1 (Vec.perm_eq_one_iff.2 e), h⟩

theorem Vec.exists_ne_zero (hA : G.AffineData H) : ∃ v : Vec hA, v ≠ 0 := by
  obtain ⟨x, hx⟩ := hA.hyperplane.exists_not_mem
  obtain ⟨v, hv, -⟩ := exists_vdir_ne hA x
  exact ⟨v, hv⟩

@[expose] def traceEnd (hA : G.AffineData H) : Subring (AddMonoid.End (Vec hA)) where
  carrier := {α | ∀ d (hd : d ∈ H), ∀ v ∈ dirSub hA d hd, α v ∈ dirSub hA d hd}
  mul_mem' := fun hα hβ d hd v hv => hα d hd _ (hβ d hd v hv)
  one_mem' := fun _ _ _ hv => hv
  add_mem' := fun hα hβ d hd v hv => add_mem (hα d hd v hv) (hβ d hd v hv)
  zero_mem' := fun _ _ _ _ => zero_mem _
  neg_mem' := fun hα d hd v hv => neg_mem (hα d hd v hv)

abbrev Scalar (hA : G.AffineData H) : Type u := traceEnd hA

theorem smul_mem_dirSub (a : Scalar hA) {d : P} {hd : d ∈ H} {v : Vec hA}
    (hv : v ∈ dirSub hA d hd) : a • v ∈ dirSub hA d hd := a.2 d hd v hv

theorem smul_eq_zero_of_vdir_ne {a : Scalar hA} {v w : Vec hA} (hv : v ≠ 0)
    (h : a • v = 0) (hw : w ≠ 0) (hvw : vdir w ≠ vdir v) : a • w = 0 := by
  have hu : v + w ≠ 0 := by
    intro e
    have hw' : w = -v := eq_neg_of_add_eq_zero_right e
    have : w ∈ dirSub hA (vdir v) (vdir_mem hv) := by
      rw [hw']
      exact neg_mem (mem_dirSub_vdir hv)
    exact hw (eq_zero_of_mem_dirSub hvw (mem_dirSub_vdir hw) this)
  have hdu : vdir (v + w) ≠ vdir w := by
    intro e
    have h1 : v + w ∈ dirSub hA (vdir w) (vdir_mem hw) := by
      have := mem_dirSub_vdir hu
      simp only [e] at this
      exact this
    have h2 : v ∈ dirSub hA (vdir w) (vdir_mem hw) := by
      have := sub_mem h1 (mem_dirSub_vdir hw)
      rwa [add_sub_cancel_right] at this
    exact hv (eq_zero_of_mem_dirSub (Ne.symm hvw) (mem_dirSub_vdir hv) h2)
  have h1 : a • w ∈ dirSub hA (vdir w) (vdir_mem hw) := smul_mem_dirSub a (mem_dirSub_vdir hw)
  have h2 : a • w ∈ dirSub hA (vdir (v + w)) (vdir_mem hu) := by
    have h3 : a • (v + w) = a • w := by rw [smul_add, h, zero_add]
    rw [← h3]
    exact smul_mem_dirSub a (mem_dirSub_vdir hu)
  exact eq_zero_of_mem_dirSub (Ne.symm hdu) h1 h2

theorem eq_zero_of_smul_eq_zero {a : Scalar hA} {v : Vec hA} (hv : v ≠ 0) (h : a • v = 0) :
    a = 0 := by
  have key : ∀ w : Vec hA, a • w = 0 := by
    intro w
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    by_cases hvw : vdir w ≠ vdir v
    · exact smul_eq_zero_of_vdir_ne hv h hw hvw
    have hvw' : vdir w = vdir v := Classical.not_not.1 hvw
    obtain ⟨w', hw', hw'v⟩ := exists_vdir_ne hA (vdir v)
    have h' := smul_eq_zero_of_vdir_ne hv h hw' hw'v
    refine smul_eq_zero_of_vdir_ne hw' h' hw ?_
    rw [hvw']
    exact Ne.symm hw'v
  exact Subtype.ext (AddMonoidHom.ext key)

section Conj

variable (hA) in
theorem conj_mem {f : Equiv.Perm P} (hf : G.IsDilatation H f) {τ : Equiv.Perm P}
    (hτ : τ ∈ G.translationGroup hA) : f * τ * f⁻¹ ∈ G.translationGroup hA := by
  have hH := hA.hyperplane
  refine ⟨?_, ?_⟩
  · rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul]
    exact (hf.comp hH hτ.1).comp hH (hf.inv hH)
  rcases hτ.2 with hid | hfix
  · left
    intro x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hid]
    exact f.apply_symm_apply x
  · right
    intro x hx e
    have hy : f⁻¹ x ∉ H := (hf.inv hH).map_not_mem x hx
    apply hfix _ hy
    have e' := congrArg (⇑(f⁻¹ : Equiv.Perm P)) e
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at e'
    rwa [show f⁻¹ (f (τ (f⁻¹ x))) = τ (f⁻¹ x) from f.symm_apply_apply _] at e'

theorem HasDir.conj {f : Equiv.Perm P} (hf : G.IsDilatation H f) {τ : Equiv.Perm P}
    (hτ : τ ∈ G.translationGroup hA) {d : P} (hd : d ∈ H) (h : G.HasDir H τ d) :
    G.HasDir H (f * τ * f⁻¹) d := by
  have hH := hA.hyperplane
  intro x hx
  have hy : f⁻¹ x ∉ H := (hf.inv hH).map_not_mem x hx
  have hfy : f (f⁻¹ x) = x := f.apply_symm_apply x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  by_cases hτy : τ (f⁻¹ x) = f⁻¹ x
  · rw [hτy, hfy]
    exact G.left_mem_line x d
  have h1 := hf.mem_line hH hy (hτ.1.map_not_mem _ hy) (Ne.symm hτy)
  have hl : G.line (f⁻¹ x) (τ (f⁻¹ x)) = G.line (f⁻¹ x) d := G.line_eq_of_mem (h _ hy) hτy
  have h2 : d = G.inf H (f⁻¹ x) (τ (f⁻¹ x)) := by
    refine hH.eq_inf hy (Ne.symm hτy) ?_ hd
    rw [hl]
    exact G.right_mem_line _ d
  rwa [← h2, hfy] at h1

variable (hA) in
@[expose] def conjEnd (f : Equiv.Perm P) (hf : G.IsDilatation H f) : Scalar hA :=
  ⟨{ toFun := fun v => ⟨f * v.perm * f⁻¹, conj_mem hA hf v.mem⟩
     map_zero' := Vec.ext (by
       change f * 1 * f⁻¹ = 1
       rw [mul_one, mul_inv_cancel])
     map_add' := fun v w => Vec.ext (by
       change f * (v.perm * w.perm) * f⁻¹ = f * v.perm * f⁻¹ * (f * w.perm * f⁻¹)
       simp only [mul_assoc, inv_mul_cancel_left]) },
    fun _ hd _ hv => HasDir.conj hf (Vec.mem _) hd hv⟩

theorem conjEnd_smul_apply (f : Equiv.Perm P) (hf : G.IsDilatation H f) (v : Vec hA) (x : P) :
    (conjEnd hA f hf • v) x = f (v ((f⁻¹ : Equiv.Perm P) x)) := rfl

end Conj

theorem exists_smul_eq {d : P} {hd : d ∈ H} {v w : Vec hA} (hv : v ∈ dirSub hA d hd)
    (hw : w ∈ dirSub hA d hd) (hv0 : v ≠ 0) : ∃ a : Scalar hA, a • v = w := by
  have hH := hA.hyperplane
  by_cases hw0 : w = 0
  · exact ⟨0, by rw [hw0, zero_smul]⟩
  obtain ⟨o, ho⟩ := hH.exists_not_mem
  by_cases hvw : v o = w o
  · exact ⟨1, by rw [one_smul]; exact Vec.eq_of_apply_eq ho hvw⟩
  have hvo := Vec.apply_ne hv0 ho
  have hwo := Vec.apply_ne hw0 ho
  have hb : G.IsBase H o (v o) (w o) := by
    refine ⟨v.map_not_mem ho, w.map_not_mem ho, hvo, hwo, hvw, ?_⟩
    rw [G.line_eq_of_mem ((mem_dirSub_iff ho).1 hv) hvo]
    exact (mem_dirSub_iff ho).1 hw
  obtain ⟨f, hf, hfv, -, hfo⟩ :=
    G.exists_centralCollineation hH hA.not_mem_plane hA.triangle hb
  refine ⟨conjEnd hA f hf, Vec.eq_of_apply_eq ho ?_⟩
  have hfo' : f⁻¹ o = o := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hfo ho).symm
  rw [conjEnd_smul_apply, hfo', hfv]

instance : Nontrivial (Scalar hA) := by
  obtain ⟨v, hv⟩ := Vec.exists_ne_zero hA
  refine ⟨⟨0, 1, fun h => hv ?_⟩⟩
  have : (1 : Scalar hA) • v = (0 : Scalar hA) • v := by rw [← h]
  rwa [one_smul, zero_smul] at this

theorem exists_mul_eq_one {a : Scalar hA} (ha : a ≠ 0) : ∃ b : Scalar hA, b * a = 1 := by
  obtain ⟨v, hv⟩ := Vec.exists_ne_zero hA
  have hav : a • v ≠ 0 := fun h => ha (eq_zero_of_smul_eq_zero hv h)
  obtain ⟨b, hb⟩ := exists_smul_eq (smul_mem_dirSub a (mem_dirSub_vdir hv)) (mem_dirSub_vdir hv)
    hav
  refine ⟨b, ?_⟩
  have h : (b * a - 1) • v = 0 := by rw [sub_smul, mul_smul, hb, one_smul, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_smul_eq_zero hv h)

theorem isUnit_or_eq_zero (a : Scalar hA) : IsUnit a ∨ a = 0 := by
  by_cases ha : a = 0
  · exact Or.inr ha
  left
  obtain ⟨b, hb⟩ := exists_mul_eq_one ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hb
    exact zero_ne_one hb
  obtain ⟨c, hc⟩ := exists_mul_eq_one hb0
  have hca : c = a := by
    calc c = c * (b * a) := by rw [hb, mul_one]
      _ = c * b * a := (mul_assoc _ _ _).symm
      _ = a := by rw [hc, one_mul]
  have hab : a * b = 1 := by rw [← hca, hc]
  exact ⟨⟨a, b, hab, hb⟩, rfl⟩

noncomputable instance : DivisionRing (Scalar hA) :=
  DivisionRing.ofIsUnitOrEqZero isUnit_or_eq_zero

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
