module

public import CFSG.Fischer.Classification.Symplectic.OrthoGenSymplectic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S12InspSp

open CFSG.Open CFSG.Fischer.Classification Matrix LinearMap.BilinForm

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem add_self_zmod2 (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem eq_of_add_eq_zero_zmod2 {a c : ZMod 2} (h : a + c = 0) : a = c := by
  revert a c
  decide

theorem add_self_vec {ι : Type} (z : ι → ZMod 2) : z + z = 0 := by
  funext i
  exact add_self_zmod2 (z i)

theorem eq_of_add_eq_zero_vec {ι : Type} {x z : ι → ZMod 2} (h : x + z = 0) : x = z := by
  calc x = x + (z + z) := by rw [add_self_vec, add_zero]
    _ = (x + z) + z := by rw [add_assoc]
    _ = z := by rw [h, zero_add]

theorem add_add_self_left {ι : Type} (x z : ι → ZMod 2) : x + z + x = z := by
  rw [add_comm x z, add_assoc, add_self_vec, add_zero]

theorem b_symm {ι : Type} {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)}
    (halt : ∀ x, b x x = 0) (x y : ι → ZMod 2) : b x y = b y x := by
  have h := halt (x + y)
  rw [add_left, add_right, add_right, halt x, halt y, zero_add, add_zero] at h
  exact eq_of_add_eq_zero_zmod2 h

theorem exists_b_eq_one {ι : Type} {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) {v : ι → ZMod 2}
    (hv : v ≠ 0) : ∃ y, b y v = 1 := by
  by_contra h
  push Not at h
  apply hv
  refine hnd v fun y => ?_
  rw [b_symm halt]
  exact (zmod_two_cases _).resolve_right (h y)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)}

variable (b) in
abbrev SpG : Subgroup (GL ι (ZMod 2)) :=
  fischerMatrixGroup fun A : Matrix ι ι (ZMod 2) => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y

@[expose] noncomputable def act (g : SpG b) (x : ι → ZMod 2) : ι → ZMod 2 :=
  ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ x

theorem act_mul (g h : SpG b) (x : ι → ZMod 2) : act (g * h) x = act g (act h x) := by
  simp only [act, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem act_one (x : ι → ZMod 2) : act (1 : SpG b) x = x := by
  simp only [act, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]

theorem act_add (g : SpG b) (x y : ι → ZMod 2) : act g (x + y) = act g x + act g y :=
  Matrix.mulVec_add _ _ _

theorem act_smul (g : SpG b) (c : ZMod 2) (x : ι → ZMod 2) : act g (c • x) = c • act g x :=
  Matrix.mulVec_smul _ _ _

theorem act_zero (g : SpG b) : act g 0 = 0 := Matrix.mulVec_zero _

theorem act_inv_act (g : SpG b) (x : ι → ZMod 2) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : SpG b) (x : ι → ZMod 2) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_ext {g h : SpG b} (e : ∀ x, act g x = act h x) : g = h :=
  Subtype.ext (Units.ext (Matrix.ext_of_mulVec_single fun _ => e _))

theorem b_act_act (g : SpG b) (x y : ι → ZMod 2) : b (act g x) (act g y) = b x y :=
  (mem_fischerMatrixGroup_bilin_iff b g).1 g.2 x y

theorem b_act_left {g : SpG b} {v : ι → ZMod 2} (hg : act g v = v) (x : ι → ZMod 2) :
    b (act g x) v = b x v := by
  conv_lhs => rw [← hg]
  exact b_act_act g x v

theorem act_inv_eq {g : SpG b} {v : ι → ZMod 2} (hg : act g v = v) : act g⁻¹ v = v := by
  conv_lhs => rw [← hg]
  exact act_inv_act g v

section Transvection

variable (halt : ∀ x, b x x = 0)

@[expose] noncomputable def tr (w : ι → ZMod 2) : SpG b :=
  ⟨sympTransvectionGL b halt w, sympTransvectionGL_mem_fischerMatrixGroup w⟩

theorem act_tr (w x : ι → ZMod 2) : act (tr halt w) x = x + b x w • w :=
  sympTransvectionGL_mulVec w x

end Transvection

variable (b) in
@[expose] noncomputable def rad (v : ι → ZMod 2) : Subgroup (SpG b) where
  carrier := {g | act g v = v ∧ ∀ y, b y v = 0 → ∃ c : ZMod 2, act g y = y + c • v}
  one_mem' := ⟨act_one v, fun y _ => ⟨0, by rw [act_one, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro g h ⟨hgv, hg⟩ ⟨hhv, hh⟩
    refine ⟨by rw [act_mul, hhv, hgv], fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hh y hy
    obtain ⟨c', hc'⟩ := hg y hy
    exact ⟨c' + c, by rw [act_mul, hc, act_add, act_smul, hgv, hc', add_smul, add_assoc]⟩
  inv_mem' := by
    rintro g ⟨hgv, hg⟩
    have hv' : act g⁻¹ v = v := act_inv_eq hgv
    refine ⟨hv', fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hg (act g⁻¹ y) (by rw [b_act_left hv', hy])
    rw [act_act_inv] at hc
    refine ⟨c, ?_⟩
    calc act g⁻¹ y = act g⁻¹ y + c • v + c • v := by rw [add_assoc, add_self_vec, add_zero]
      _ = y + c • v := by rw [← hc]

theorem mem_rad {v : ι → ZMod 2} {g : SpG b} :
    g ∈ rad b v ↔ act g v = v ∧ ∀ y, b y v = 0 → ∃ c : ZMod 2, act g y = y + c • v :=
  Iff.rfl

section Centralizer

variable (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
  {t : SpG b} {v : ι → ZMod 2} (hv : v ≠ 0) (ht : ∀ x, act t x = x + b x v • v)

include halt hnd hv ht in
theorem act_eq_of_mem_centralizer {c : SpG b} (hc : c ∈ Subgroup.centralizer {t}) :
    act c v = v := by
  obtain ⟨y₀, hy₀⟩ := exists_b_eq_one halt hnd hv
  have e := congrArg (fun g => act g y₀) (Subgroup.mem_centralizer_singleton_iff.1 hc)
  simp only [act_mul, ht, hy₀, one_smul, act_add] at e
  have e' : act c v = b (act c y₀) v • v := add_left_cancel e
  rcases zmod_two_cases (b (act c y₀) v) with h0 | h1
  · exfalso
    apply hv
    rw [h0, zero_smul] at e'
    rw [← act_inv_act c v, e', act_zero]
  · rw [e', h1, one_smul]

include halt hnd hv ht in
theorem conj_mem_rad {c g : SpG b} (hc : c ∈ Subgroup.centralizer {t}) (hg : g ∈ rad b v) :
    c * g * c⁻¹ ∈ rad b v := by
  have hcv := act_eq_of_mem_centralizer halt hnd hv ht hc
  have hcv' : act c⁻¹ v = v := act_inv_eq hcv
  obtain ⟨hgv, hg⟩ := hg
  refine ⟨by rw [act_mul, act_mul, hcv', hgv, hcv], fun y hy => ?_⟩
  obtain ⟨e, he⟩ := hg (act c⁻¹ y) (by rw [b_act_left hcv', hy])
  exact ⟨e, by rw [act_mul, act_mul, he, act_add, act_smul, act_act_inv, hcv]⟩

include halt hnd hv ht in
theorem centralizer_le_normalizer_rad :
    Subgroup.centralizer {t} ≤ Subgroup.normalizer (rad b v : Set (SpG b)) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => conj_mem_rad halt hnd hv ht hc hg, fun hg => ?_⟩
  have := conj_mem_rad halt hnd hv ht (Subgroup.inv_mem _ hc) hg
  simpa [mul_assoc] using this

end Centralizer

end CFSG.LargeExtraspecial.S12InspSp
