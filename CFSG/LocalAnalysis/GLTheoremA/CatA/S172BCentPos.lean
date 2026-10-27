module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentKey

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open QuadraticMap Module CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_mem_ne_of_two_le_length {l : List (V × V)} (hl : IsFrame Q l) (hlen : 2 ≤ l.length) :
    ∃ p ∈ l, ∃ q ∈ l, p ≠ q := by
  rcases l with _ | ⟨a, _ | ⟨b, l'⟩⟩
  · simp at hlen
  · simp at hlen
  · obtain ⟨ha, hperp, -⟩ := isFrame_cons.1 hl
    refine ⟨a, List.mem_cons_self, b, by simp, fun hab => ?_⟩
    have h := (hperp b (by simp)).2.1
    rw [← hab, ha.ab] at h
    exact one_ne_zero h

theorem pow_apply_eq_of_apply_eq {ρ : V ≃ₗ[ZMod 2] V} {x : V} (hx : ρ x = x) (j : ℕ) :
    (ρ ^ j) x = x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, LinearEquiv.mul_apply, hx, ih]

theorem rot_apply_mem_planeSpan {p : V × V} (hp : MinusPair Q p.1 p.2) {x : V}
    (hx : x ∈ planeSpan p) : rot Q p.1 p.2 x ∈ planeSpan p := by
  rw [rot_apply hp]
  exact add_mem (add_mem hx (Submodule.smul_mem _ _ (left_mem_planeSpan p)))
    (Submodule.smul_mem _ _ (right_mem_planeSpan p))

theorem rot_pow_apply_mem_planeSpan {p : V × V} (hp : MinusPair Q p.1 p.2) (k : ℕ) {x : V}
    (hx : x ∈ planeSpan p) : (rot Q p.1 p.2 ^ k) x ∈ planeSpan p := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply]
    exact rot_apply_mem_planeSpan hp ih

theorem exists_pow_rot_apply_planeSpan {l : List (V × V)} (hl : IsFrame Q l) {p : V × V}
    (hp : p ∈ l) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ torus Q l) :
    ∃ k : ℕ, ∀ x ∈ planeSpan p, t x = (rot Q p.1 p.2 ^ k) x := by
  have hpp := hl.pair p hp
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨q, hq, rfl⟩ := ht
    by_cases hqp : q = p
    · subst hqp
      exact ⟨1, fun x _ => by rw [pow_one]⟩
    · refine ⟨0, fun x hx => ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := hl.perp_of_mem_of_ne hp hq (Ne.symm hqp)
      obtain ⟨c, e, rfl⟩ := (mem_planeSpan_iff p x).1 hx
      have h1' : polar Q (c • p.1 + e • p.2) q.1 = 0 := by
        rw [polar_add_left, polar_smul_left, polar_smul_left, h1, h3]
        simp
      have h2' : polar Q (c • p.1 + e • p.2) q.2 = 0 := by
        rw [polar_add_left, polar_smul_left, polar_smul_left, h2, h4]
        simp
      rw [pow_zero]
      exact rot_apply_of_perp (hl.pair q hq) h1' h2'
  | one => exact ⟨0, fun x _ => by rw [pow_zero]⟩
  | mul s t hs ht ihs iht =>
    obtain ⟨k₁, h₁⟩ := ihs
    obtain ⟨k₂, h₂⟩ := iht
    refine ⟨k₁ + k₂, fun x hx => ?_⟩
    rw [LinearEquiv.mul_apply, h₂ x hx, h₁ _ (rot_pow_apply_mem_planeSpan hpp k₂ hx), pow_add,
      LinearEquiv.mul_apply]
  | inv t ht iht =>
    obtain ⟨k, hk⟩ := iht
    refine ⟨2 * k, fun x hx => ?_⟩
    have hmem := rot_pow_apply_mem_planeSpan hpp (2 * k) hx
    have h3 : rot Q p.1 p.2 ^ (k + 2 * k) = 1 := by
      rw [show k + 2 * k = 3 * k by ring, pow_mul, rot_pow_three hpp, one_pow]
    show t.symm x = _
    rw [LinearEquiv.symm_apply_eq, hk _ hmem, ← LinearEquiv.mul_apply, ← pow_add, h3]
    rfl

theorem exists_pow_rot_mul_apply_left_eq {l : List (V × V)} (hl : IsFrame Q l) {p : V × V}
    (hp : p ∈ l) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ torus Q l) :
    ∃ j : ℕ, (t * rot Q p.1 p.2 ^ j) p.1 = p.1 := by
  obtain ⟨k, hk⟩ := exists_pow_rot_apply_planeSpan hl hp ht
  have hpp := hl.pair p hp
  refine ⟨2 * k, ?_⟩
  have hmem := rot_pow_apply_mem_planeSpan hpp (2 * k) (left_mem_planeSpan p)
  have h3 : rot Q p.1 p.2 ^ (k + 2 * k) = 1 := by
    rw [show k + 2 * k = 3 * k by ring, pow_mul, rot_pow_three hpp, one_pow]
  rw [LinearEquiv.mul_apply, hk _ hmem, ← LinearEquiv.mul_apply, ← pow_add, h3]
  rfl

theorem mem_zpowers_rot_of_fixes_perpPlane {l : List (V × V)} (hl : IsFrame Q l) {p₀ : V × V}
    (hp₀ : p₀ ∈ l) {b : V ≃ₗ[ZMod 2] V} (hb : b ∈ torus Q l)
    (hfix : ∀ w ∈ perpPlane Q p₀, b w = w) : b ∈ Subgroup.zpowers (rot Q p₀.1 p₀.2) := by
  obtain ⟨j, hj⟩ := exists_pow_rot_mul_apply_left_eq hl hp₀ hb
  have hb' : b * rot Q p₀.1 p₀.2 ^ j ∈ torus Q l := mul_mem hb (pow_mem (rot_mem_torus hp₀) j)
  have h1 : b * rot Q p₀.1 p₀.2 ^ j = 1 := by
    refine eq_one_of_forall_apply_left hl hb' fun p hp => ?_
    by_cases hpp : p = p₀
    · subst hpp
      exact hj
    · obtain ⟨e1, -, e3, -⟩ := hl.perp_of_mem_of_ne hp₀ hp (Ne.symm hpp)
      have hperp : p.1 ∈ perpPlane Q p₀ := (mem_perpPlane_iff p₀ p.1).2 ⟨e1, e3⟩
      have hfx : (rot Q p₀.1 p₀.2 ^ j) p.1 = p.1 :=
        pow_apply_eq_of_apply_eq (rot_apply_left_of_ne hl hp₀ hp (Ne.symm hpp)) j
      rw [LinearEquiv.mul_apply, hfx]
      exact hfix _ hperp
  have : b = (rot Q p₀.1 p₀.2 ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [this]
  exact inv_mem (pow_mem (Subgroup.mem_zpowers _) j)

theorem mem_planeSpan_of_rot_sq_add {p : V × V} (hp : MinusPair Q p.1 p.2) {v : V}
    (hv : rot Q p.1 p.2 (rot Q p.1 p.2 v) + rot Q p.1 p.2 v + v = 0) : v ∈ planeSpan p := by
  obtain ⟨w, hw, hu⟩ := hp.exists_decomp v
  obtain ⟨c, e, hwce⟩ := (mem_planeSpan_iff p w).1 hw
  have hu' := (mem_perpPlane_iff' p _).1 hu
  have h1 : rot Q p.1 p.2 (v - w) = v - w := rot_apply_of_perp hp hu'.1 hu'.2
  have hw0 : rot Q p.1 p.2 (rot Q p.1 p.2 w) + rot Q p.1 p.2 w + w = 0 := by
    rw [← hwce]
    simp only [map_add, map_smul, rot_apply_left hp, rot_apply_right hp]
    linear_combination (norm := module) (c + e) • vec_add_self p.1 + (c + 2 * e) • vec_add_self p.2
  have h2 : rot Q p.1 p.2 v = rot Q p.1 p.2 w + (v - w) := by
    rw [map_sub] at h1
    linear_combination (norm := module) h1
  have h3 : rot Q p.1 p.2 (rot Q p.1 p.2 v) = rot Q p.1 p.2 (rot Q p.1 p.2 w) + (v - w) := by
    rw [h2, map_add, h1]
  have h0 : v - w = 0 := by
    rw [h3, h2] at hv
    linear_combination (norm := module) hv - hw0 - vec_add_self (v - w)
  rw [sub_eq_zero.1 h0]
  exact hw

theorem exists_pair_adjust {l : List (V × V)} (hl : IsFrame Q l) {p₁ : V × V} (hp₁ : p₁ ∈ l)
    {d : V ≃ₗ[ZMod 2] V} (hd : d ∈ torus Q l) (hmov : ∀ p ∈ l, d p.1 ≠ p.1) :
    ∃ j : ℕ, (d * rot Q p₁.1 p₁.2 ^ j) p₁.1 = p₁.1 ∧
      (∀ p ∈ l, p ≠ p₁ → (d * rot Q p₁.1 p₁.2 ^ j) p.1 ≠ p.1) ∧
      fixedSpace (d * rot Q p₁.1 p₁.2 ^ j) ⊓ fixedSpace (rot Q p₁.1 p₁.2) = perpL Q l ∧
      ∀ v, rot Q p₁.1 p₁.2 (rot Q p₁.1 p₁.2 v) + rot Q p₁.1 p₁.2 v + v = 0 →
        (d * rot Q p₁.1 p₁.2 ^ j) v = v := by
  obtain ⟨j, hj⟩ := exists_pow_rot_mul_apply_left_eq hl hp₁ hd
  have hρt : rot Q p₁.1 p₁.2 ∈ torus Q l := rot_mem_torus hp₁
  have hd₂t : d * rot Q p₁.1 p₁.2 ^ j ∈ torus Q l := mul_mem hd (pow_mem hρt j)
  have hid : ∀ x ∈ planeSpan p₁, (d * rot Q p₁.1 p₁.2 ^ j) x = x :=
    fixes_planeSpan_of_apply_left hl hp₁ hd₂t hj
  have hother : ∀ p ∈ l, p ≠ p₁ → (d * rot Q p₁.1 p₁.2 ^ j) p.1 ≠ p.1 := by
    intro p hp hne
    rw [LinearEquiv.mul_apply,
      pow_apply_eq_of_apply_eq (rot_apply_left_of_ne hl hp₁ hp (Ne.symm hne)) j]
    exact hmov p hp
  refine ⟨j, hj, hother, ?_, fun v hv => hid v (mem_planeSpan_of_rot_sq_add (hl.pair p₁ hp₁) hv)⟩
  have hallmov : ∀ p ∈ l, ((d * rot Q p₁.1 p₁.2 ^ j) * rot Q p₁.1 p₁.2) p.1 ≠ p.1 := by
    intro p hp
    by_cases hpp : p = p₁
    · subst hpp
      rw [LinearEquiv.mul_apply, rot_apply_left (hl.pair p hp), hid _ (right_mem_planeSpan p)]
      exact (hl.pair p hp).ne.symm
    · rw [LinearEquiv.mul_apply, rot_apply_left_of_ne hl hp₁ hp (Ne.symm hpp)]
      exact hother p hp hpp
  have hfs := fixedSpace_eq_perpL hl (mul_mem hd₂t hρt) hallmov
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    rw [← hfs, mem_fixedSpace, LinearEquiv.mul_apply, mem_fixedSpace.1 hx2, mem_fixedSpace.1 hx1]
  · intro x hx
    have hx' : ∀ p ∈ l, polar Q x p.1 = 0 ∧ polar Q x p.2 = 0 := fun p hp => by
      have := (mem_perpL_iff l x).1 hx p hp
      rw [polar_comm Q x p.1, polar_comm Q x p.2]
      exact this
    exact Submodule.mem_inf.2 ⟨mem_fixedSpace.2 (torus_fixes hl hx' _ hd₂t),
      mem_fixedSpace.2 (torus_fixes hl hx' _ hρt)⟩

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
