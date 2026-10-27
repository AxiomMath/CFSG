module

public import CFSG.LargeExtraspecial.OrthoF2Eichler
public import CFSG.LargeExtraspecial.OrthoF2SpRadical
public import CFSG.LargeExtraspecial.S2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}

@[expose] def spSiegelLin (f : BilinForm (ZMod 2) V) (p u : V) (c : ZMod 2) :
    V →ₗ[ZMod 2] V where
  toFun x := x + f x p • u + (f x u + c * f x p) • p
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, add_smul, mul_add]
    abel
  map_smul' a x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    module

theorem spSiegelLin_apply (p u : V) (c : ZMod 2) (x : V) :
    spSiegelLin f p u c x = x + f x p • u + (f x u + c * f x p) • p :=
  rfl

theorem spSiegelLin_involutive (hf : f.IsAlt) {p u : V} (hpu : f p u = 0) (c : ZMod 2) :
    Function.Involutive (spSiegelLin f p u c) := fun x => by
  have hup : f u p = 0 := by rw [isAlt_symm hf, hpu]
  have h1 : f (spSiegelLin f p u c x) p = f x p := by
    simp only [spSiegelLin_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hup, hf.self_eq_zero, mul_zero, add_zero]
  have h2 : f (spSiegelLin f p u c x) u = f x u := by
    simp only [spSiegelLin_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hpu, hf.self_eq_zero, mul_zero, add_zero]
  rw [spSiegelLin_apply (x := spSiegelLin f p u c x), h1, h2, spSiegelLin_apply]
  refine eq_of_one_smul_eq ?_
  match_scalars <;> ring_nf <;> reduce_mod_char

open Classical in
@[expose] noncomputable def spSiegel (f : BilinForm (ZMod 2) V) (hf : f.IsAlt) (p u : V)
    (c : ZMod 2) : V ≃ₗ[ZMod 2] V :=
  if h : f p u = 0 then LinearEquiv.ofInvolutive (spSiegelLin f p u c)
    (spSiegelLin_involutive hf h c) else 1

theorem spSiegel_apply (hf : f.IsAlt) {p u : V} (hpu : f p u = 0) (c : ZMod 2) (x : V) :
    spSiegel f hf p u c x = x + f x p • u + (f x u + c * f x p) • p := by
  rw [spSiegel, dite_eq_left hpu]
  rfl

theorem spSiegel_mul_self (hf : f.IsAlt) {p u : V} (hpu : f p u = 0) (c : ZMod 2) :
    spSiegel f hf p u c * spSiegel f hf p u c = 1 := by
  ext x
  rw [LinearEquiv.mul_apply, spSiegel, dite_eq_left hpu]
  exact spSiegelLin_involutive hf hpu c x

theorem spSiegel_mem_isometryGroup (hf : f.IsAlt) {p u : V} (hpu : f p u = 0) (c : ZMod 2) :
    spSiegel f hf p u c ∈ TauCeti.BilinForm.isometryGroup f := by
  have hup : f u p = 0 := by rw [isAlt_symm hf, hpu]
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  rw [spSiegel_apply hf hpu, spSiegel_apply hf hpu]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hpu, hup,
    hf.self_eq_zero, mul_zero, add_zero, isAlt_symm hf y u, isAlt_symm hf y p]
  ring_nf
  reduce_mod_char

theorem spSiegel_zero_one (hf : f.IsAlt) (p : V) : spSiegel f hf p 0 1 = spTransvection f hf p := by
  ext x
  rw [spSiegel_apply hf (map_zero _), spTransvection_apply]
  simp

theorem spSiegel_add_smul (hf : f.IsAlt) {p u : V} (hpu : f p u = 0) (a c : ZMod 2) :
    spSiegel f hf p (u + a • p) c = spSiegel f hf p u c := by
  have hpu' : f p (u + a • p) = 0 := by
    rw [map_add, map_smul, hpu, hf.self_eq_zero, smul_zero, add_zero]
  ext x
  rw [spSiegel_apply hf hpu', spSiegel_apply hf hpu]
  simp only [map_add, map_smul, smul_eq_mul]
  refine eq_of_one_smul_eq ?_
  match_scalars <;> first | ring1 | (ring_nf; reduce_mod_char)

theorem spSiegel_one_mul_zero_one (hf : f.IsAlt) {p u : V} (hpu : f p u = 0) :
    spSiegel f hf p u 1 * spSiegel f hf p 0 1 = spSiegel f hf p u 0 := by
  have hp0 : f p 0 = 0 := map_zero _
  have hup : f u p = 0 := by rw [isAlt_symm hf, hpu]
  ext x
  rw [LinearEquiv.mul_apply, spSiegel_apply hf hpu, spSiegel_apply hf hp0, spSiegel_apply hf hpu]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hf.self_eq_zero, map_zero, smul_zero, add_zero, zero_add, mul_zero, one_mul, hpu, zero_mul]
  refine eq_of_one_smul_eq ?_
  match_scalars <;> first | ring1 | (ring_nf; reduce_mod_char)

theorem spSiegel_conj (hf : f.IsAlt) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup f) {p u : V} (hpu : f p u = 0) (c : ZMod 2) :
    g * spSiegel f hf p u c * g⁻¹ = spSiegel f hf (g p) (g u) c := by
  have hg' := TauCeti.BilinForm.mem_isometryGroup_iff.mp hg
  have hgpu : f (g p) (g u) = 0 := by rw [hg', hpu]
  ext x
  have hx : ∀ y, f (g⁻¹ x) y = f x (g y) := fun y => by
    rw [← hg', CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply']
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, spSiegel_apply hf hpu, spSiegel_apply hf hgpu,
    map_add, map_add, map_smul, map_smul,
    CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply', hx, hx]

theorem spSiegel_mem_spPointRadical (hf : f.IsAlt) {p u : V} (hpu : f p u = 0) (c : ZMod 2) :
    spSiegel f hf p u c ∈ spPointRadical f p := by
  refine ⟨spSiegel_mem_isometryGroup hf hpu c, ?_, fun x hx => ?_, fun v => ?_⟩
  · rw [spSiegel_apply hf hpu, hf.self_eq_zero, hpu]
    simp
  · rw [spSiegel_apply hf hpu, isAlt_symm hf x p, hx]
    simp only [zero_smul, mul_zero, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p)
  · rw [spSiegel_apply hf hpu, add_assoc, add_sub_cancel_left, map_add, map_smul, map_smul, hpu,
      hf.self_eq_zero]
    simp

theorem mem_spPointRadical_iff (hf : f.IsAlt) (hnd : f.Nondegenerate) {p : V} (hp0 : p ≠ 0)
    {t : V ≃ₗ[ZMod 2] V} :
    t ∈ spPointRadical f p ↔ ∃ u, f p u = 0 ∧ ∃ c, t = spSiegel f hf p u c := by
  constructor
  · intro ht
    obtain ⟨b, hb⟩ : ∃ b, f p b ≠ 0 := by
      by_contra! h
      exact hp0 (hnd.1 p h)
    have hb1 : f p b = 1 := zmod2_eq_one_of_ne_zero hb
    have hbp : f b p = 1 := by rw [isAlt_symm hf, hb1]
    set w := t b - b with hw
    have hpw : f p w = 0 := ht.2.2.2 b
    refine ⟨w, hpw, f b w, spPointRadical_ext hb1 ht (spSiegel_mem_spPointRadical hf hpw _) ?_⟩
    rw [spSiegel_apply hf hpw, hbp, one_smul, mul_one, zmod2_add_self, zero_smul, add_zero, hw,
      add_sub_cancel]
  · rintro ⟨u, hpu, c, rfl⟩
    exact spSiegel_mem_spPointRadical hf hpu c

theorem spSiegel_eq_one_iff (hf : f.IsAlt) (hnd : f.Nondegenerate) {p u : V} (hp0 : p ≠ 0)
    (hpu : f p u = 0) (c : ZMod 2) :
    spSiegel f hf p u c = 1 ↔ u ∈ (ZMod 2) ∙ p ∧ c = 0 := by
  obtain ⟨b, hb⟩ : ∃ b, f p b ≠ 0 := by
    by_contra! h
    exact hp0 (hnd.1 p h)
  have hbp : f b p = 1 := by rw [isAlt_symm hf]; exact zmod2_eq_one_of_ne_zero hb
  constructor
  · intro h1
    have h := LinearEquiv.congr_fun h1 b
    rw [spSiegel_apply hf hpu, hbp, one_smul, mul_one, LinearEquiv.coe_one, id, add_assoc,
      add_eq_left] at h
    have hu : u = (f b u + c) • p := by
      rw [add_eq_zero_iff_eq_neg, vec_neg] at h
      exact h
    have hmem : u ∈ (ZMod 2) ∙ p := by
      rw [hu]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p)
    refine ⟨hmem, ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    rw [show a • p = 0 + a • p by rw [zero_add], spSiegel_add_smul hf (map_zero _)] at h1
    have h2 := LinearEquiv.congr_fun h1 b
    rw [spSiegel_apply hf (map_zero _), hbp, map_zero, smul_zero, add_zero, zero_add, mul_one,
      LinearEquiv.coe_one, id, add_eq_left, smul_eq_zero] at h2
    exact h2.resolve_right hp0
  · rintro ⟨hu, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [show a • p = 0 + a • p by rw [zero_add], spSiegel_add_smul hf (map_zero _)]
    ext x
    rw [spSiegel_apply hf (map_zero _)]
    simp

theorem apply_spSiegel_self (hf : f.IsAlt) {p u : V} (hpu : f p u = 0) (c : ZMod 2) (v : V) :
    f v (spSiegel f hf p u c v) = c * f v p := by
  have key : ∀ a b c : ZMod 2, a * b + (b + c * a) * a = c * a := by decide
  rw [spSiegel_apply hf hpu]
  simp only [map_add, map_smul, smul_eq_mul, hf.self_eq_zero, zero_add]
  exact key _ _ _

theorem exists_apply_spSiegel_one_ne_zero (hf : f.IsAlt) (hnd : f.Nondegenerate) {p u : V}
    (hp0 : p ≠ 0) (hpu : f p u = 0) : ∃ v, f v (spSiegel f hf p u 1 v) ≠ 0 := by
  obtain ⟨b, hb⟩ : ∃ b, f p b ≠ 0 := by
    by_contra! h
    exact hp0 (hnd.1 p h)
  exact ⟨b, by rw [apply_spSiegel_self hf hpu, one_mul, isAlt_symm hf]; exact hb⟩

theorem not_isSpTypeA_spSiegel_one (hf : f.IsAlt) (hnd : f.Nondegenerate) {p u : V}
    (hp0 : p ≠ 0) (hpu : f p u = 0) : ¬ IsSpTypeA f (spSiegel f hf p u 1) 2 := by
  rintro ⟨-, -, -, -, h⟩
  obtain ⟨v, hv⟩ := exists_apply_spSiegel_one_ne_zero hf hnd hp0 hpu
  exact hv (h v)

theorem commSpace_spSiegel_le (hf : f.IsAlt) {p u : V} (hpu : f p u = 0) (c : ZMod 2) :
    commSpace (spSiegel f hf p u c) ≤ Submodule.span (ZMod 2) {p, u} := by
  intro y hy
  obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
  rw [spSiegel_apply hf hpu, add_assoc, add_sub_cancel_left, add_comm]
  exact Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩

theorem sp_exists_dual [FiniteDimensional (ZMod 2) V] (hf : f.IsAlt)
    (hnd : f.Nondegenerate) {v w : V}
    (hli : LinearIndependent (ZMod 2) ![v, w]) : ∃ x, f x v = 1 ∧ f x w = 0 := by
  have hv : v ∉ (ZMod 2) ∙ w := not_mem_span_singleton_of_pair (linearIndependent_pair_symm hli)
  have hv' : v ∉ f.orthogonal (f.orthogonal ((ZMod 2) ∙ w)) := by
    rwa [LinearMap.BilinForm.orthogonal_orthogonal hnd hf.isRefl]
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv'
  push Not at hv'
  obtain ⟨x, hx, hxv⟩ := hv'
  refine ⟨x, zmod2_eq_one_of_ne_zero hxv, ?_⟩
  rw [isAlt_symm hf]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) w (Submodule.mem_span_singleton_self w)

theorem commSpace_spSiegel [FiniteDimensional (ZMod 2) V] (hf : f.IsAlt)
    (hnd : f.Nondegenerate) {p u : V}
    (hpu : f p u = 0) (hli : LinearIndependent (ZMod 2) ![p, u]) (c : ZMod 2) :
    commSpace (spSiegel f hf p u c) = Submodule.span (ZMod 2) {p, u} := by
  refine le_antisymm (commSpace_spSiegel_le hf hpu c) ?_
  obtain ⟨x₁, hx₁p, hx₁u⟩ := sp_exists_dual hf hnd hli
  obtain ⟨x₂, hx₂u, hx₂p⟩ := sp_exists_dual hf hnd (linearIndependent_pair_symm hli)
  have hp : p ∈ commSpace (spSiegel f hf p u c) := by
    have h := sub_mem_commSpace (spSiegel f hf p u c) x₂
    rwa [spSiegel_apply hf hpu, hx₂p, hx₂u, zero_smul, add_zero, mul_zero, add_zero, one_smul,
      add_sub_cancel_left] at h
  have hu : u ∈ commSpace (spSiegel f hf p u c) := by
    have h := sub_mem_commSpace (spSiegel f hf p u c) x₁
    rw [spSiegel_apply hf hpu, hx₁p, hx₁u, one_smul, zero_add, mul_one, add_assoc,
      add_sub_cancel_left] at h
    have h2 := Submodule.sub_mem _ h (Submodule.smul_mem _ c hp)
    rwa [add_sub_cancel_right] at h2
  rw [Submodule.span_le]
  rintro y (rfl | rfl)
  · exact hp
  · exact hu

theorem isSpTypeA_spSiegel_zero [FiniteDimensional (ZMod 2) V] (hf : f.IsAlt)
    (hnd : f.Nondegenerate) {p u : V}
    (hpu : f p u = 0) (hli : LinearIndependent (ZMod 2) ![p, u]) :
    IsSpTypeA f (spSiegel f hf p u 0) 2 := by
  have hp0 : p ≠ 0 := (linearIndependent_pair_iff.mp hli).1
  refine ⟨TauCeti.BilinForm.mem_isometryGroup_iff.mp (spSiegel_mem_isometryGroup hf hpu 0),
    fun h => ?_, spSiegel_mul_self hf hpu 0, by rw [commSpace_spSiegel hf hnd hpu hli,
      finrank_span_pair hli], fun v => by rw [apply_spSiegel_self hf hpu, zero_mul]⟩
  have := ((spSiegel_eq_one_iff hf hnd hp0 hpu 0).mp h).1
  exact not_mem_span_singleton_of_pair hli this

theorem isSpTypeC_spSiegel_one [FiniteDimensional (ZMod 2) V] (hf : f.IsAlt)
    (hnd : f.Nondegenerate) {p u : V}
    (hpu : f p u = 0) (hli : LinearIndependent (ZMod 2) ![p, u]) :
    IsSpTypeC f (spSiegel f hf p u 1) 2 := by
  have hp0 : p ≠ 0 := (linearIndependent_pair_iff.mp hli).1
  refine ⟨TauCeti.BilinForm.mem_isometryGroup_iff.mp (spSiegel_mem_isometryGroup hf hpu 1),
    fun h => ?_, spSiegel_mul_self hf hpu 1, by rw [commSpace_spSiegel hf hnd hpu hli,
      finrank_span_pair hli], even_two, exists_apply_spSiegel_one_ne_zero hf hnd hp0 hpu⟩
  have := ((spSiegel_eq_one_iff hf hnd hp0 hpu 1).mp h).2
  exact one_ne_zero this

end S2

end CFSG.LargeExtraspecial
