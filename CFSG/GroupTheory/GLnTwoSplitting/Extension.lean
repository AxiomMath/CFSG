module

public import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Submodule

structure NatExt (G : Type*) [Group G] (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] where
  ι : E → G
  ι_add : ∀ a b, ι (a + b) = ι a * ι b
  injective : Function.Injective ι
  π : G →* (E ≃ₗ[ZMod 2] E)
  surjective : Function.Surjective π
  ker_iff : ∀ g, π g = 1 ↔ ∃ e, ι e = g
  conj : ∀ g e, g * ι e * g⁻¹ = ι (π g e)

namespace NatExt

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  (X : NatExt G E)

theorem ι_zero : X.ι 0 = 1 := by
  have h := X.ι_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem ι_mul_self (e : E) : X.ι e * X.ι e = 1 := by
  rw [← X.ι_add, two_add_self, X.ι_zero]

theorem ι_inv (e : E) : (X.ι e)⁻¹ = X.ι e :=
  inv_eq_of_mul_eq_one_left (X.ι_mul_self e)

theorem ι_mul_comm (a b : E) : X.ι a * X.ι b = X.ι b * X.ι a := by
  rw [← X.ι_add, ← X.ι_add, add_comm]

theorem π_ι (e : E) : X.π (X.ι e) = 1 :=
  (X.ker_iff _).2 ⟨e, rfl⟩

theorem ι_eq_one_iff {e : E} : X.ι e = 1 ↔ e = 0 :=
  ⟨fun h => X.injective (h.trans X.ι_zero.symm), fun h => h ▸ X.ι_zero⟩

theorem mul_ι (g : G) (e : E) : g * X.ι e = X.ι (X.π g e) * g := by
  rw [← X.conj, inv_mul_cancel_right]

theorem ι_mul (g : G) (e : E) : X.ι e * g = g * X.ι ((X.π g).symm e) := by
  rw [X.mul_ι, LinearEquiv.apply_symm_apply]

theorem conj_ι' (g : G) (e : E) : g⁻¹ * X.ι e * g = X.ι ((X.π g).symm e) := by
  rw [mul_assoc, X.ι_mul, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_eq_mul_ι {g g' : G} (h : X.π g = X.π g') : ∃ e, g' = g * X.ι e := by
  obtain ⟨e, he⟩ := (X.ker_iff (g⁻¹ * g')).1 (by rw [map_mul, map_inv, h, inv_mul_cancel])
  exact ⟨e, by rw [he, mul_inv_cancel_left]⟩

@[expose] def V : Subgroup G where
  carrier := {g | ∃ e, X.ι e = g}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, X.ι_add a b⟩
  one_mem' := ⟨0, X.ι_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, (X.ι_inv a).symm⟩

theorem mem_V {g : G} : g ∈ X.V ↔ ∃ e, X.ι e = g :=
  Iff.rfl

theorem ι_mem_V (e : E) : X.ι e ∈ X.V :=
  ⟨e, rfl⟩

theorem V_eq_ker : X.V = X.π.ker := by
  ext g
  rw [MonoidHom.mem_ker, X.ker_iff, X.mem_V]

instance V_normal : X.V.Normal := by
  rw [V_eq_ker]
  infer_instance

theorem mul_ι_mul_mul_ι (g : G) (v : E) :
    g * X.ι v * (g * X.ι v) = g * g * X.ι ((X.π g).symm v + v) := by
  rw [X.ι_add, ← X.conj_ι' g v]
  group

theorem sq_mem_of_π_eq_transvection [FiniteDimensional (ZMod 2) E] (hE : 4 ≤ finrank (ZMod 2) E)
    {f : Dual (ZMod 2) E} {d : E} (h : f d = 0) {g : G} (hg : X.π g = LinearEquiv.transvection h) :
    ∃ w ∈ (ZMod 2) ∙ d, g * g = X.ι w := by
  obtain ⟨w, hw⟩ := (X.ker_iff (g * g)).1 (by rw [map_mul, hg, transvection_mul_self])
  refine ⟨w, ?_, hw.symm⟩
  refine mem_span_of_forall_smul_mem_span (U := LinearMap.ker f)
    (by have := finrank_ker_add_one_ge f; omega) d w fun χ k hχd hχk hk => ?_
  rw [LinearMap.mem_ker] at hk
  obtain ⟨s, hs⟩ := X.surjective (LinearEquiv.transvection hχk)
  have hcomm := transvection_commute h hχk hk hχd
  obtain ⟨v, hv⟩ := X.exists_eq_mul_ι (g := g) (g' := s * g * s⁻¹)
    (by rw [map_mul, map_mul, map_inv, hs, hg, ← hcomm, mul_inv_cancel_right])
  have h1 : s * g * s⁻¹ * (s * g * s⁻¹) = X.ι (LinearEquiv.transvection hχk w) := by
    rw [← hs, ← X.conj, hw]
    group
  rw [hv, X.mul_ι_mul_mul_ι, ← hw, ← X.ι_add, hg,
    show (LinearEquiv.transvection h).symm = LinearEquiv.transvection h from transvection_inv h]
    at h1
  have h2 := X.injective h1
  have h3 : χ w • k = f v • d := by
    have e1 : v + f v • d + v = f v • d := by rw [add_comm v, add_assoc, two_add_self, add_zero]
    rw [transvection_apply, transvection_apply, e1] at h2
    exact (add_left_cancel h2).symm
  rw [h3]
  exact smul_mem _ _ (mem_span_singleton_self d)

theorem mul_ι_sq_of_π_eq_transvection {f : Dual (ZMod 2) E} {d : E} (h : f d = 0) {g : G}
    (hg : X.π g = LinearEquiv.transvection h) (v : E) :
    g * X.ι v * (g * X.ι v) = g * g * X.ι (f v • d) := by
  rw [X.mul_ι_mul_mul_ι, hg,
    show (LinearEquiv.transvection h).symm = LinearEquiv.transvection h from transvection_inv h,
    transvection_apply, add_comm v, add_assoc, two_add_self, add_zero]

theorem exists_involution_lift [FiniteDimensional (ZMod 2) E] (hE : 4 ≤ finrank (ZMod 2) E)
    {f : Dual (ZMod 2) E} {d : E} (h : f d = 0) (hf : f ≠ 0) :
    ∃ g, X.π g = LinearEquiv.transvection h ∧ g * g = 1 := by
  obtain ⟨g, hg⟩ := X.surjective (LinearEquiv.transvection h)
  obtain ⟨w, hw, hgw⟩ := X.sq_mem_of_π_eq_transvection hE h hg
  rcases (mem_span_singleton_iff_two.1 hw) with rfl | rfl
  · exact ⟨g, hg, by rw [hgw, X.ι_zero]⟩
  · obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra! hv
      exact hf (LinearMap.ext hv)
    refine ⟨g * X.ι v, by rw [map_mul, X.π_ι, mul_one, hg], ?_⟩
    rw [X.mul_ι_sq_of_π_eq_transvection h hg, hgw, zmod_two_eq_one_of_ne_zero hv, one_smul,
      ← X.ι_add, two_add_self, X.ι_zero]

theorem mul_ι_sq_eq_one_iff {f : Dual (ZMod 2) E} {d : E} (h : f d = 0) (hd : d ≠ 0) {g : G}
    (hg : X.π g = LinearEquiv.transvection h) (hgg : g * g = 1) (z : E) :
    g * X.ι z * (g * X.ι z) = 1 ↔ f z = 0 := by
  rw [X.mul_ι_sq_of_π_eq_transvection h hg, hgg, one_mul, X.ι_eq_one_iff, smul_eq_zero]
  exact ⟨fun h' => h'.resolve_right hd, Or.inl⟩

end NatExt

end CFSG.GroupTheory.GLnTwoSplitting
