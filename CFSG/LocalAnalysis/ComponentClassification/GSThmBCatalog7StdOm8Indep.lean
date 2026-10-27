module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8One
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Corr
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Rank

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

section Reflections

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {W : Submodule K V}

theorem reflectPair_mul_self {e₀ e₁ : W} (h₀ : (Q.comp W.subtype) e₀ = 1)
    (h₁ : (Q.comp W.subtype) e₁ = 1) (h₀₁ : polar (Q.comp W.subtype) e₀ e₁ = 0) :
    reflectPair (Q := Q) e₀ e₁ * reflectPair e₀ e₁ = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (reflect (Q.comp W.subtype) e₀ * reflect (Q.comp W.subtype) e₁)
    ((reflect (Q.comp W.subtype) e₀ * reflect (Q.comp W.subtype) e₁) x) = x
  rw [reflect_pair_apply h₀ h₁ h₀₁ ((reflect (Q.comp W.subtype) e₀ *
    reflect (Q.comp W.subtype) e₁) x), reflect_pair_apply h₀ h₁ h₀₁ x]
  simp only [polar_sub_right, polar_smul_right, OddClassSelector.polar_self_eq, h₀, h₁, h₀₁,
    polar_comm (Q.comp W.subtype) e₁ e₀, smul_eq_mul]
  module

theorem reflectPair_mul_reflectPair_apply {e₀ e₁ e₂ : W} (h₀ : (Q.comp W.subtype) e₀ = 1)
    (h₁ : (Q.comp W.subtype) e₁ = 1) (h₂ : (Q.comp W.subtype) e₂ = 1)
    (h₀₁ : polar (Q.comp W.subtype) e₀ e₁ = 0) (h₀₂ : polar (Q.comp W.subtype) e₀ e₂ = 0)
    (h₁₂ : polar (Q.comp W.subtype) e₁ e₂ = 0) (x : W) :
    (reflectPair (Q := Q) e₀ e₁ * reflectPair e₀ e₂).val x =
      x - polar (Q.comp W.subtype) e₁ x • e₁ - polar (Q.comp W.subtype) e₂ x • e₂ := by
  change (reflect (Q.comp W.subtype) e₀ * reflect (Q.comp W.subtype) e₁)
    ((reflect (Q.comp W.subtype) e₀ * reflect (Q.comp W.subtype) e₂) x) = _
  rw [reflect_pair_apply h₀ h₁ h₀₁ ((reflect (Q.comp W.subtype) e₀ *
    reflect (Q.comp W.subtype) e₂) x), reflect_pair_apply h₀ h₂ h₀₂ x]
  simp only [polar_sub_right, polar_smul_right, OddClassSelector.polar_self_eq, h₀, h₀₁, h₀₂,
    polar_comm (Q.comp W.subtype) e₁ e₀, h₁₂, smul_eq_mul]
  module

theorem reflectPair_comm {e₀ e₁ e₂ : W} (h₀ : (Q.comp W.subtype) e₀ = 1)
    (h₁ : (Q.comp W.subtype) e₁ = 1) (h₂ : (Q.comp W.subtype) e₂ = 1)
    (h₀₁ : polar (Q.comp W.subtype) e₀ e₁ = 0) (h₀₂ : polar (Q.comp W.subtype) e₀ e₂ = 0)
    (h₁₂ : polar (Q.comp W.subtype) e₁ e₂ = 0) :
    reflectPair (Q := Q) e₀ e₁ * reflectPair e₀ e₂ = reflectPair e₀ e₂ * reflectPair e₀ e₁ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [reflectPair_mul_reflectPair_apply h₀ h₁ h₂ h₀₁ h₀₂ h₁₂,
    reflectPair_mul_reflectPair_apply h₀ h₂ h₁ h₀₂ h₀₁ (by rw [polar_comm]; exact h₁₂)]
  abel

theorem pow_apply_of_apply {g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)}
    {x : W} {s : K} (h : g.val x = s • x) (n : ℕ) : (g ^ n).val x = s ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Subgroup.coe_mul, LinearEquiv.mul_apply, h, map_smul, ih, smul_smul,
      ← pow_succ']

theorem prod_apply_of_apply {g₁ g₂ g₃ : TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)}
    {x : W} {s₁ s₂ s₃ : K} (h₁ : g₁.val x = s₁ • x) (h₂ : g₂.val x = s₂ • x)
    (h₃ : g₃.val x = s₃ • x) (a b c : ℕ) :
    (g₁ ^ a * (g₂ ^ b * g₃ ^ c)).val x = (s₁ ^ a * s₂ ^ b * s₃ ^ c) • x := by
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, pow_apply_of_apply h₃, map_smul,
    pow_apply_of_apply h₂, pow_apply_of_apply h₁, smul_smul]
  congr 1
  ring

omit [AddCommGroup V] [Module K V] in
theorem eq_zero_of_neg_one_pow_smul {X : Type*} [AddCommGroup X] [Module K X]
    (h2 : (2 : K) ≠ 0) {x : X} (hx : x ≠ 0)
    {n : ℕ} (hn : n < 2) (h : ((-1 : K) ^ n) • x = x) : n = 0 := by
  interval_cases n
  · rfl
  · exfalso
    rw [pow_one, neg_one_smul, neg_eq_iff_add_eq_zero, ← two_smul K] at h
    exact hx ((smul_eq_zero.mp h).resolve_left h2)

@[expose] def reflectTriple (e₀ e₁ e₂ e₃ : W) (a b c : ℕ) :
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) :=
  reflectPair (Q := Q) e₀ e₁ ^ a * (reflectPair e₀ e₂ ^ b * reflectPair e₀ e₃ ^ c)

structure Frame (Q : QuadraticForm K V) (W : Submodule K V) (e₀ e₁ e₂ e₃ e₄ : W) : Prop where
  q₀ : (Q.comp W.subtype) e₀ = 1
  q₁ : (Q.comp W.subtype) e₁ = 1
  q₂ : (Q.comp W.subtype) e₂ = 1
  q₃ : (Q.comp W.subtype) e₃ = 1
  o01 : polar (Q.comp W.subtype) e₀ e₁ = 0
  o02 : polar (Q.comp W.subtype) e₀ e₂ = 0
  o03 : polar (Q.comp W.subtype) e₀ e₃ = 0
  o04 : polar (Q.comp W.subtype) e₀ e₄ = 0
  o12 : polar (Q.comp W.subtype) e₁ e₂ = 0
  o13 : polar (Q.comp W.subtype) e₁ e₃ = 0
  o14 : polar (Q.comp W.subtype) e₁ e₄ = 0
  o23 : polar (Q.comp W.subtype) e₂ e₃ = 0
  o24 : polar (Q.comp W.subtype) e₂ e₄ = 0
  o34 : polar (Q.comp W.subtype) e₃ e₄ = 0

variable {e₀ e₁ e₂ e₃ e₄ : W}

theorem reflectPair_apply_neg {u v : W} (hu : (Q.comp W.subtype) u = 1)
    (hv : (Q.comp W.subtype) v = 1) (huv : polar (Q.comp W.subtype) u v = 0) :
    (reflectPair (Q := Q) u v).val v = (-1 : K) • v := by
  rw [neg_one_smul]
  exact reflect_pair_apply_right hu hv huv

theorem reflectPair_apply_one {u v w : W} (hu : (Q.comp W.subtype) u = 1)
    (hv : (Q.comp W.subtype) v = 1) (huv : polar (Q.comp W.subtype) u v = 0)
    (huw : polar (Q.comp W.subtype) u w = 0) (hvw : polar (Q.comp W.subtype) v w = 0) :
    (reflectPair (Q := Q) u v).val w = (1 : K) • w := by
  rw [one_smul]
  exact reflect_pair_apply_fix hu hv huv huw hvw

theorem reflectTriple_apply₁ (hF : Frame Q W e₀ e₁ e₂ e₃ e₄) (a b c : ℕ) :
    (reflectTriple (Q := Q) e₀ e₁ e₂ e₃ a b c).val e₁ = (-1 : K) ^ a • e₁ := by
  have h := prod_apply_of_apply (reflectPair_apply_neg hF.q₀ hF.q₁ hF.o01)
    (reflectPair_apply_one hF.q₀ hF.q₂ hF.o02 hF.o01 (by rw [polar_comm]; exact hF.o12))
    (reflectPair_apply_one hF.q₀ hF.q₃ hF.o03 hF.o01 (by rw [polar_comm]; exact hF.o13)) a b c
  rw [one_pow, one_pow, mul_one, mul_one] at h
  exact h

theorem reflectTriple_apply₂ (hF : Frame Q W e₀ e₁ e₂ e₃ e₄) (a b c : ℕ) :
    (reflectTriple (Q := Q) e₀ e₁ e₂ e₃ a b c).val e₂ = (-1 : K) ^ b • e₂ := by
  have h := prod_apply_of_apply
    (reflectPair_apply_one hF.q₀ hF.q₁ hF.o01 hF.o02 hF.o12)
    (reflectPair_apply_neg hF.q₀ hF.q₂ hF.o02)
    (reflectPair_apply_one hF.q₀ hF.q₃ hF.o03 hF.o02 (by rw [polar_comm]; exact hF.o23)) a b c
  rw [one_pow, one_pow, mul_one, one_mul] at h
  exact h

theorem reflectTriple_apply₃ (hF : Frame Q W e₀ e₁ e₂ e₃ e₄) (a b c : ℕ) :
    (reflectTriple (Q := Q) e₀ e₁ e₂ e₃ a b c).val e₃ = (-1 : K) ^ c • e₃ := by
  have h := prod_apply_of_apply
    (reflectPair_apply_one hF.q₀ hF.q₁ hF.o01 hF.o03 hF.o13)
    (reflectPair_apply_one hF.q₀ hF.q₂ hF.o02 hF.o03 hF.o23)
    (reflectPair_apply_neg hF.q₀ hF.q₃ hF.o03) a b c
  rw [one_pow, one_pow, one_mul, one_mul] at h
  exact h

theorem reflectTriple_apply₄ (hF : Frame Q W e₀ e₁ e₂ e₃ e₄) (a b c : ℕ) :
    (reflectTriple (Q := Q) e₀ e₁ e₂ e₃ a b c).val e₄ = e₄ := by
  have h := prod_apply_of_apply
    (reflectPair_apply_one hF.q₀ hF.q₁ hF.o01 hF.o04 hF.o14)
    (reflectPair_apply_one hF.q₀ hF.q₂ hF.o02 hF.o04 hF.o24)
    (reflectPair_apply_one hF.q₀ hF.q₃ hF.o03 hF.o04 hF.o34) a b c
  rw [one_pow, one_pow, one_pow, mul_one, mul_one, one_smul] at h
  exact h

theorem reflectTriple_indep (h2 : (2 : K) ≠ 0) (hF : Frame Q W e₀ e₁ e₂ e₃ e₄)
    (hne₁ : e₁ ≠ 0) (hne₂ : e₂ ≠ 0) (hne₃ : e₃ ≠ 0) (hne₄ : e₄ ≠ 0) (a b c : ZMod 2)
    (h : (∀ v, (reflectTriple (Q := Q) e₀ e₁ e₂ e₃ a.val b.val c.val).val v = v) ∨
      (∀ v, (reflectTriple (Q := Q) e₀ e₁ e₂ e₃ a.val b.val c.val).val v = -v)) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  rcases h with h | h
  · refine ⟨(ZMod.val_eq_zero a).mp (eq_zero_of_neg_one_pow_smul h2 hne₁ (ZMod.val_lt a) ?_),
      (ZMod.val_eq_zero b).mp (eq_zero_of_neg_one_pow_smul h2 hne₂ (ZMod.val_lt b) ?_),
      (ZMod.val_eq_zero c).mp (eq_zero_of_neg_one_pow_smul h2 hne₃ (ZMod.val_lt c) ?_)⟩
    · rw [← reflectTriple_apply₁ hF a.val b.val c.val, h]
    · rw [← reflectTriple_apply₂ hF a.val b.val c.val, h]
    · rw [← reflectTriple_apply₃ hF a.val b.val c.val, h]
  · exfalso
    have h4 := (reflectTriple_apply₄ hF a.val b.val c.val).symm.trans (h e₄)
    rw [eq_neg_iff_add_eq_zero, ← two_smul K] at h4
    exact hne₄ ((smul_eq_zero.mp h4).resolve_left h2)

theorem frame_involutions (hF : Frame Q W e₀ e₁ e₂ e₃ e₄) :
    reflectPair (Q := Q) e₀ e₁ * reflectPair e₀ e₁ = 1 ∧
      reflectPair (Q := Q) e₀ e₂ * reflectPair e₀ e₂ = 1 ∧
      reflectPair (Q := Q) e₀ e₃ * reflectPair e₀ e₃ = 1 ∧
      reflectPair (Q := Q) e₀ e₁ * reflectPair e₀ e₂ = reflectPair e₀ e₂ * reflectPair e₀ e₁ ∧
      reflectPair (Q := Q) e₀ e₁ * reflectPair e₀ e₃ = reflectPair e₀ e₃ * reflectPair e₀ e₁ ∧
      reflectPair (Q := Q) e₀ e₂ * reflectPair e₀ e₃ = reflectPair e₀ e₃ * reflectPair e₀ e₂ :=
  ⟨reflectPair_mul_self hF.q₀ hF.q₁ hF.o01, reflectPair_mul_self hF.q₀ hF.q₂ hF.o02,
    reflectPair_mul_self hF.q₀ hF.q₃ hF.o03,
    reflectPair_comm hF.q₀ hF.q₁ hF.q₂ hF.o01 hF.o02 hF.o12,
    reflectPair_comm hF.q₀ hF.q₁ hF.q₃ hF.o01 hF.o03 hF.o13,
    reflectPair_comm hF.q₀ hF.q₂ hF.q₃ hF.o02 hF.o03 hF.o23⟩

variable [Finite K] [FiniteDimensional K V]

theorem exists_frame (hodd : Odd (Nat.card K)) (hW : (Q.comp W.subtype).polarBilin.Nondegenerate)
    (hdW : 5 ≤ finrank K W) :
    ∃ e₀ e₁ e₂ e₃ e₄ : W, Frame Q W e₀ e₁ e₂ e₃ e₄ ∧ e₁ ≠ 0 ∧ e₂ ≠ 0 ∧ e₃ ≠ 0 ∧ e₄ ≠ 0 := by
  obtain ⟨e, he, hQe⟩ := exists_unit_orthogonal_basis hodd hW (by omega)
  have ho : ∀ a b : ℕ, (ha : a < finrank K W) → (hb : b < finrank K W) → a ≠ b →
      polar (Q.comp W.subtype) (e ⟨a, ha⟩) (e ⟨b, hb⟩) = 0 :=
    fun a b ha hb hab => he _ _ (fun h => hab (congrArg Fin.val h))
  have hq : ∀ a : ℕ, (ha : a < 4) → (Q.comp W.subtype) (e ⟨a, by omega⟩) = 1 :=
    fun a ha => hQe _ (by simp; omega)
  refine ⟨e ⟨0, by omega⟩, e ⟨1, by omega⟩, e ⟨2, by omega⟩, e ⟨3, by omega⟩, e ⟨4, by omega⟩,
    ⟨hq 0 (by omega), hq 1 (by omega), hq 2 (by omega), hq 3 (by omega),
      ho 0 1 _ _ (by omega), ho 0 2 _ _ (by omega), ho 0 3 _ _ (by omega),
      ho 0 4 _ _ (by omega), ho 1 2 _ _ (by omega), ho 1 3 _ _ (by omega),
      ho 1 4 _ _ (by omega), ho 2 3 _ _ (by omega), ho 2 4 _ _ (by omega),
      ho 3 4 _ _ (by omega)⟩, e.ne_zero _, e.ne_zero _, e.ne_zero _, e.ne_zero _⟩

end Reflections

section Rank

variable {H : Type} [Group H] [Finite H] {G : Subgroup H} [G.Normal] {K : Type} [Field K]
  [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {Θ : G ≃* projectiveDerived Q} {t : H} (D : InvData G Q Θ t)
  {U U' : Submodule K V}
  (ι : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
  (hι : ∀ h (x : U) (y : U'), (ι.symm h).val.val (x.val + y.val) =
    (h.1.val x).val + (h.2.val y).val)

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem exists_lift (M : Subgroup (FN D))
    (hM : M.map (epsT D ι) =
      (commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))).prod ⊥)
    (s : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))
    (hs : s ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))) :
    ∃ m ∈ M, epsT D ι m = (s, 1) := by
  have hs' : ((s, 1) : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype)) ∈ M.map (epsT D ι) := by
    rw [hM]
    exact ⟨hs, Subgroup.one_mem _⟩
  obtain ⟨m, hm, hms⟩ := hs'
  exact ⟨m, hm, hms⟩

omit [Finite H] [Finite K] [FiniteDimensional K V] in
include hι in
theorem sign_of_toHD_eq_one (m : FN D) (s : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))
    (hms : epsT D ι m = (s, 1)) (hm : toHD D m = 1) :
    (∀ v, s.val v = v) ∨ (∀ v, s.val v = -v) := by
  have hys := (toH_eq_one_iff G Q Θ t D.A D.μ D.hsim D.hconj m).mp hm
  have hact : ∀ v : U, m.val.val.val v.val = (s.val v : V) := by
    intro v
    rw [← epsT_symm_val D ι m, hms]
    exact ext_left ι hι (s, 1) v
  rcases (mem_scalarSigns_iff Q _).mp hys with h1 | h1
  · left
    intro v
    apply Subtype.ext
    rw [← hact v, h1]
    rfl
  · right
    intro v
    apply Subtype.ext
    rw [← hact v, h1, QuadraticMap.coe_negOrthogonal]
    rfl

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem toHD_mul_self (m : FN D) (s : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))
    (hms : epsT D ι m = (s, 1)) (hss : s * s = 1) : toHD D m * toHD D m = 1 := by
  have : m * m = 1 := epsT_injective D ι (by
    rw [map_mul, hms, Prod.mk_mul_mk, hss, mul_one, map_one]
    rfl)
  rw [← map_mul, this, map_one]

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem toHD_comm (m m' : FN D) (s s' : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))
    (hms : epsT D ι m = (s, 1)) (hms' : epsT D ι m' = (s', 1)) (hss' : s * s' = s' * s) :
    toHD D m * toHD D m' = toHD D m' * toHD D m := by
  have : m * m' = m' * m := epsT_injective D ι (by
    rw [map_mul, map_mul, hms, hms', Prod.mk_mul_mk, Prod.mk_mul_mk, hss'])
  rw [← map_mul, this, map_mul]

omit [Finite H] [Finite K] [FiniteDimensional K V] in
include hι in
theorem lift_indep (h2 : (2 : K) ≠ 0) {e₀ e₁ e₂ e₃ e₄ : U} (hF : Frame Q U e₀ e₁ e₂ e₃ e₄)
    (hn₁ : e₁ ≠ 0) (hn₂ : e₂ ≠ 0) (hn₃ : e₃ ≠ 0) (hn₄ : e₄ ≠ 0) (m₁ m₂ m₃ : FN D)
    (hε₁ : epsT D ι m₁ = (reflectPair (Q := Q) e₀ e₁, 1))
    (hε₂ : epsT D ι m₂ = (reflectPair (Q := Q) e₀ e₂, 1))
    (hε₃ : epsT D ι m₃ = (reflectPair (Q := Q) e₀ e₃, 1)) (a b c : ZMod 2)
    (h : toHD D m₁ ^ a.val * (toHD D m₂ ^ b.val * toHD D m₃ ^ c.val) = 1) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  apply reflectTriple_indep h2 hF hn₁ hn₂ hn₃ hn₄
  apply sign_of_toHD_eq_one D ι hι (m₁ ^ a.val * (m₂ ^ b.val * m₃ ^ c.val))
    (reflectTriple (Q := Q) e₀ e₁ e₂ e₃ a.val b.val c.val)
  · rw [map_mul, map_mul, map_pow, map_pow, map_pow, hε₁, hε₂, hε₃, Prod.pow_mk,
      Prod.pow_mk, Prod.pow_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, one_pow, one_pow, one_pow,
      mul_one, mul_one, reflectTriple]
  · rw [map_mul, map_mul, map_pow, map_pow, map_pow]
    exact h

omit [Finite H] [Finite K] [FiniteDimensional K V] in
include hι in
theorem exists_three (h2 : (2 : K) ≠ 0) {e₀ e₁ e₂ e₃ e₄ : U} (hF : Frame Q U e₀ e₁ e₂ e₃ e₄)
    (hn₁ : e₁ ≠ 0) (hn₂ : e₂ ≠ 0) (hn₃ : e₃ ≠ 0) (hn₄ : e₄ ≠ 0) (M : Subgroup (FN D))
    (hM : M.map (epsT D ι) =
      (commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))).prod ⊥) :
    ∃ x₁ x₂ x₃ : M.map (toHD D), x₁ * x₁ = 1 ∧ x₂ * x₂ = 1 ∧ x₃ * x₃ = 1 ∧ Commute x₁ x₂ ∧
      Commute x₁ x₃ ∧ Commute x₂ x₃ ∧ ∀ a b c : ZMod 2,
        x₁ ^ a.val * (x₂ ^ b.val * x₃ ^ c.val) = 1 → a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨hs₁, hs₂, hs₃, hc₁₂, hc₁₃, hc₂₃⟩ := frame_involutions hF
  obtain ⟨m₁, hm₁, hε₁⟩ := exists_lift D ι M hM _
    (reflect_mul_reflect_mem_commutator h2 hF.q₀ hF.q₁)
  obtain ⟨m₂, hm₂, hε₂⟩ := exists_lift D ι M hM _
    (reflect_mul_reflect_mem_commutator h2 hF.q₀ hF.q₂)
  obtain ⟨m₃, hm₃, hε₃⟩ := exists_lift D ι M hM _
    (reflect_mul_reflect_mem_commutator h2 hF.q₀ hF.q₃)
  refine ⟨⟨_, mem_map_of_mem _ hm₁⟩, ⟨_, mem_map_of_mem _ hm₂⟩, ⟨_, mem_map_of_mem _ hm₃⟩,
    Subtype.ext (toHD_mul_self D ι m₁ _ hε₁ hs₁), Subtype.ext (toHD_mul_self D ι m₂ _ hε₂ hs₂),
    Subtype.ext (toHD_mul_self D ι m₃ _ hε₃ hs₃),
    Subtype.ext (toHD_comm D ι m₁ m₂ _ _ hε₁ hε₂ hc₁₂),
    Subtype.ext (toHD_comm D ι m₁ m₃ _ _ hε₁ hε₃ hc₁₃),
    Subtype.ext (toHD_comm D ι m₂ m₃ _ _ hε₂ hε₃ hc₂₃), fun a b c habc => ?_⟩
  exact lift_indep D ι hι h2 hF hn₁ hn₂ hn₃ hn₄ m₁ m₂ m₃ hε₁ hε₂ hε₃ a b c
    (congrArg Subtype.val habc)

include hι in
theorem false_of_five_le (hodd : Odd (Nat.card K))
    (hU : (Q.comp U.subtype).polarBilin.Nondegenerate) (hdU : 5 ≤ finrank K U)
    (M : Subgroup (FN D))
    (hM : M.map (epsT D ι) =
      (commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))).prod ⊥)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel ((M.map (toHD D)) ⧸ pPrimeCore 2 (M.map (toHD D))) .PSL 2 p f) :
    False := by
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨e₀, e₁, e₂, e₃, e₄, hF, hn₁, hn₂, hn₃, hn₄⟩ := exists_frame hodd hU hdU
  obtain ⟨x₁, x₂, x₃, hxx₁, hxx₂, hxx₃, hx₁₂, hx₁₃, hx₂₃, hind⟩ :=
    exists_three D ι hι h2 hF hn₁ hn₂ hn₃ hn₄ M hM
  have hmk : ∀ x : M.map (toHD D), x * x = 1 →
      (QuotientGroup.mk x : (M.map (toHD D)) ⧸ pPrimeCore 2 (M.map (toHD D))) *
        QuotientGroup.mk x = 1 := by
    intro x hx
    rw [← QuotientGroup.mk_mul, hx, QuotientGroup.mk_one]
  exact false_of_lieModel_psl_two hp hp2 hm (QuotientGroup.mk x₁) (QuotientGroup.mk x₂)
    (QuotientGroup.mk x₃) (hmk x₁ hxx₁) (hmk x₂ hxx₂) (hmk x₃ hxx₃)
    (hx₁₂.map (QuotientGroup.mk' _)) (hx₁₃.map (QuotientGroup.mk' _))
    (hx₂₃.map (QuotientGroup.mk' _))
    (independent_quotient_pPrimeCore x₁ x₂ x₃ hxx₁ hxx₂ hxx₃ hx₁₂ hx₁₃ hx₂₃ hind)

end Rank

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
