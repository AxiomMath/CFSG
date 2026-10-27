module

public import CFSG.Fischer.Classification.Recognition.SymOOrth
public import CFSG.Fischer.Classification.Uniqueness.Star

import CFSG.ClassicalGroups.Alternating.Transvections

public section

namespace CFSG.Fischer.Classification.Orth2

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Fischer.Classification.Recognition.SymO

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

variable (Q) in
@[expose] def reflClass : Set (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  {g | ∃ v, Q v = 1 ∧ (g : V ≃ₗ[ZMod 2] V) = reflect Q v}

theorem mem_reflClass {g : TauCeti.QuadraticMap.orthogonalGroup Q} :
    g ∈ reflClass Q ↔ ∃ v, Q v = 1 ∧ (g : V ≃ₗ[ZMod 2] V) = reflect Q v :=
  Iff.rfl

theorem ne_zero_of_map_eq_one {u : V} (hu : Q u = 1) : u ≠ 0 := by
  rintro rfl
  rw [QuadraticMap.map_zero] at hu
  exact zero_ne_one hu

theorem reflect_mul_comm_iff {u w : V} (hu : Q u = 1) (hw : Q w = 1) :
    reflect Q u * reflect Q w = reflect Q w * reflect Q u ↔ polar Q u w = 0 := by
  constructor
  · intro h
    rcases zmod_two_eq_zero_or_eq_one (polar Q u w) with h0 | h1
    · exact h0
    exfalso
    have key := DFunLike.congr_fun h u
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflect_apply_of_map_eq_one hw,
      reflect_apply_of_map_eq_one hu, reflect_apply_of_map_eq_one hu,
      reflect_apply_of_map_eq_one hw] at key
    rw [polar_self_zmod_two, zero_smul, add_zero, h1, one_smul, polar_add_left,
      polar_self_zmod_two, zero_add, polar_comm, h1, one_smul] at key
    have h2 : u = (u + w + u) - (u + w) := by abel
    rw [key, sub_self] at h2
    exact ne_zero_of_map_eq_one hu h2
  · intro h0
    refine LinearEquiv.ext fun x => ?_
    have h0' : polar Q w u = 0 := by rw [polar_comm]; exact h0
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflect_apply_of_map_eq_one hw,
      reflect_apply_of_map_eq_one hu, reflect_apply_of_map_eq_one hu,
      reflect_apply_of_map_eq_one hw, polar_add_left, polar_add_left, polar_smul_left,
      polar_smul_left, h0, h0']
    simp only [smul_eq_mul, mul_zero, add_zero]
    abel

theorem eq_of_reflect_eq (hnd : (polarBilin Q).Nondegenerate) {u w : V} (hu : Q u = 1)
    (h : reflect Q u = reflect Q w) (hw : Q w = 1) : u = w := by
  obtain ⟨x, hx⟩ := exists_polar_eq_one hnd hu
  have key := DFunLike.congr_fun h x
  rw [reflect_apply_of_map_eq_one hu, reflect_apply_of_map_eq_one hw, hx, one_smul] at key
  have key' := add_left_cancel key
  rcases zmod_two_eq_zero_or_eq_one (polar Q x w) with h0 | h1
  · rw [h0, zero_smul] at key'
    exact absurd key' (ne_zero_of_map_eq_one hu)
  · rwa [h1, one_smul] at key'

theorem reflect_mul_reflect_mul_reflect {u w : V} (hu : Q u = 1) (huw : polar Q u w = 1) :
    reflect Q u * reflect Q w * reflect Q u = reflect Q (u + w) := by
  have h := reflect_conj (reflect_mem_orthogonalGroup Q u) w
  rw [reflect_inv] at h
  rw [h, reflect_apply_of_map_eq_one hu, polar_comm, huw, one_smul, add_comm]

theorem zmod_two_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b
  decide

theorem exists_map_eq_one_polar_eq_one [FiniteDimensional (ZMod 2) V]
    (hnd : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank (ZMod 2) V) {s : V} (hs : s ≠ 0) :
    ∃ r, Q r = 1 ∧ polar Q s r = 1 := by
  obtain ⟨r₀, hr₀⟩ := exists_polar_ne_zero hnd hs
  have hr₀' : polar Q s r₀ = 1 := zmod_two_eq_one_of_ne_zero hr₀
  rcases zmod_two_eq_zero_or_eq_one (Q r₀) with hq | hq
  swap
  · exact ⟨r₀, hq, hr₀'⟩
  by_contra! hno
  set f := polarBilin Q s
  have hmem : ∀ a, a ∈ LinearMap.ker f ↔ polar Q s a = 0 := fun a => by simp [f]
  have hQa : ∀ a ∈ LinearMap.ker f, Q a = polar Q r₀ a := by
    intro a ha
    have hsa : polar Q s (r₀ + a) = 1 := by rw [polar_add_right, hr₀', (hmem a).mp ha, add_zero]
    have hQ0 : Q (r₀ + a) = 0 := by
      rcases zmod_two_eq_zero_or_eq_one (Q (r₀ + a)) with h | h
      · exact h
      · exact absurd hsa (hno _ h)
    rw [QuadraticMap.map_add (⇑Q) r₀ a, hq, zero_add] at hQ0
    exact zmod_two_eq_of_add_eq_zero hQ0
  have hle : LinearMap.ker f ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.ker f) := by
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    have hab : b + a ∈ LinearMap.ker f := add_mem hb ha
    show polarBilin Q b a = 0
    rw [polarBilin_apply_apply, polar, hQa _ hab, hQa _ hb, hQa _ ha, polar_add_right]
    ring
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hnd] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3' : finrank (ZMod 2) (LinearMap.range f) ≤ 1 :=
    (Submodule.finrank_le _).trans (by simp)
  omega

theorem exists_mem_map_eq_one_polar_eq_one [FiniteDimensional (ZMod 2) V]
    {U : Submodule (ZMod 2) V} (hU : ((bil Q).restrict U).Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) U) {s : V} (hsU : s ∈ U) (hs : s ≠ 0) :
    ∃ r ∈ U, Q r = 1 ∧ polar Q s r = 1 := by
  let Q' : QuadraticForm (ZMod 2) U := Q.comp U.subtype
  have hpol : ∀ x y : U, polar Q' x y = polar Q x y := fun x y => rfl
  have hnd' : (polarBilin Q').Nondegenerate := by
    have : polarBilin Q' = (bil Q).restrict U := by
      ext x y
      rw [polarBilin_apply_apply, hpol, LinearMap.BilinForm.restrict_apply,
        LinearMap.domRestrict_apply, bil_apply]
    rw [this]
    exact hU
  obtain ⟨r, hr, hsr⟩ := exists_map_eq_one_polar_eq_one hnd' h3 (s := ⟨s, hsU⟩)
    (fun h => hs (congrArg Subtype.val h))
  exact ⟨r, r.2, hr, by rwa [hpol] at hsr⟩

theorem mul_comm_iff_polar_eq_zero {g h : TauCeti.QuadraticMap.orthogonalGroup Q} {a b : V}
    (ha : Q a = 1) (hb : Q b = 1) (hg : (g : V ≃ₗ[ZMod 2] V) = reflect Q a)
    (hh : (h : V ≃ₗ[ZMod 2] V) = reflect Q b) : g * h = h * g ↔ polar Q a b = 0 := by
  rw [← reflect_mul_comm_iff ha hb, ← hg, ← hh, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
  exact Subtype.ext_iff

open CFSG.Blueprint.Fischer CFSG.ClassicalGroups.Alternating in
theorem tripleProperty_reflClass [FiniteDimensional (ZMod 2) V]
    (hnd : (polarBilin Q).Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V) :
    CFSG.Fischer.Classification.TripleProperty (reflClass Q) := by
  rintro e x ⟨u, hu, heu⟩ ⟨w, hw, hxw⟩ hex y ⟨⟨s, hs, hys⟩, hmu⟩
  have huw : polar Q u w = 1 := by
    rcases zmod_two_eq_zero_or_eq_one (polar Q u w) with h0 | h1
    · exact absurd ((mul_comm_iff_polar_eq_zero hu hw heu hxw).mpr h0) hex
    · exact h1
  have hwu : polar Q w u = 1 := by rw [polar_comm]; exact huw
  obtain ⟨-, hsplit⟩ := alternating_hyperbolic_splitting (bil_isAlt Q) hnd
    (ne_zero_of_map_eq_one hu)
  obtain ⟨-, -, -, -, hndU, hdimU⟩ := hsplit w (by rw [bil_apply]; exact huw)
  have hdec := eq_proj_add hwu s
  by_cases hp : (proj hwu s : V) = 0
  · rw [hp, zero_add] at hdec
    have h2V : ∀ z : V, -z = z := neg_eq_self_of_two_eq_zero (K := ZMod 2) (by decide)
    rcases zmod_two_eq_zero_or_eq_one (polar Q w s) with h1 | h1 <;>
      rcases zmod_two_eq_zero_or_eq_one (polar Q u s) with h2 | h2 <;>
      rw [h1, h2] at hdec
    · rw [zero_smul, zero_smul, sub_zero] at hdec
      exact absurd hdec (ne_zero_of_map_eq_one hs)
    · rw [zero_smul, one_smul, zero_sub, h2V] at hdec
      refine Or.inr (Or.inl (Subtype.ext ?_))
      rw [hys, hxw, hdec]
    · rw [zero_smul, one_smul, sub_zero] at hdec
      refine Or.inl (Subtype.ext ?_)
      rw [hys, heu, hdec]
    · rw [one_smul, one_smul, sub_eq_add_neg, h2V] at hdec
      refine Or.inr (Or.inr (Subtype.ext ?_))
      rw [hys, hdec, Subgroup.coe_mul, Subgroup.coe_mul, heu, hxw,
        reflect_mul_reflect_mul_reflect hu huw]
  · obtain ⟨r, hrU, hr1, hpr⟩ :=
      exists_mem_map_eq_one_polar_eq_one hndU (by omega) (proj hwu s).2 hp
    have hru : polar Q u r = 0 := (mem_perp.mp hrU).1
    have hrw : polar Q w r = 0 := (mem_perp.mp hrU).2
    let t : TauCeti.QuadraticMap.orthogonalGroup Q :=
      ⟨reflect Q r, reflect_mem_orthogonalGroup Q r⟩
    have htD : t ∈ reflClass Q := ⟨r, hr1, rfl⟩
    have hte : t ≠ e := by
      intro h
      have hr : r = u := eq_of_reflect_eq hnd hr1 (by rw [← heu, ← h]) hu
      rw [hr, hwu] at hrw
      exact one_ne_zero hrw
    have htx : t ≠ x := by
      intro h
      have hr : r = w := eq_of_reflect_eq hnd hr1 (by rw [← hxw, ← h]) hw
      rw [hr, huw] at hru
      exact one_ne_zero hru
    have htmu : t ∈ muSet (reflClass Q) e x :=
      ⟨⟨htD, hte, (mul_comm_iff_polar_eq_zero hr1 hu rfl heu).mpr
          (by rw [polar_comm]; exact hru)⟩,
        ⟨htD, htx, (mul_comm_iff_polar_eq_zero hr1 hw rfl hxw).mpr
          (by rw [polar_comm]; exact hrw)⟩⟩
    obtain ⟨-, -, hty⟩ := hmu htmu
    have hrs : polar Q r s = 0 := (mul_comm_iff_polar_eq_zero hr1 hs rfl hys).mp hty
    have hrs1 : polar Q r s = 1 := by
      rw [hdec, polar_add_right, polar_sub_right, polar_smul_right, polar_smul_right,
        polar_comm _ r u, hru, polar_comm _ r w, hrw, polar_comm, hpr]
      simp
    rw [hrs] at hrs1
    exact absurd hrs1 zero_ne_one

end CFSG.Fischer.Classification.Orth2
