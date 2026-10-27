module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Fin

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L23

open A44

section Emb

variable {T : Type} [Group T] (A : Subgroup T) (θ : A ≃* Z4Z4)

@[expose] def embT (v : Vec) : T := (θ.symm (Multiplicative.ofAdd v) : T)

theorem embT_add (v w : Vec) : embT A θ (v + w) = embT A θ v * embT A θ w := by
  unfold embT
  rw [ofAdd_add, map_mul]
  rfl

theorem embT_inj : Function.Injective (embT A θ) := by
  intro v w h
  have h1 : θ.symm (Multiplicative.ofAdd v) = θ.symm (Multiplicative.ofAdd w) := Subtype.ext h
  exact Multiplicative.ofAdd.injective (θ.symm.injective h1)

theorem embT_mem (v : Vec) : embT A θ v ∈ A := (θ.symm (Multiplicative.ofAdd v)).2

theorem exists_embT {a : T} (ha : a ∈ A) : ∃ v, a = embT A θ v := by
  refine ⟨Multiplicative.toAdd (θ ⟨a, ha⟩), ?_⟩
  unfold embT
  simp

end Emb

section Rho

variable {T : Type} [Group T] (A : Subgroup T) [A.Normal] (θ : A ≃* Z4Z4)

@[expose] noncomputable def rhoHom : T →* G96 := (phiB θ).toMonoidHom.comp MulAut.conjNormal

theorem rhoHom_apply (t : T) : rhoHom A θ t = phiB θ (MulAut.conjNormal t : MulAut A) := rfl

theorem conj_embT (t : T) (v : Vec) :
    t * embT A θ v * t⁻¹ = embT A θ ((rhoHom A θ t).1.act v) := by
  have h := toAdd_phiB θ (MulAut.conjNormal t : MulAut A) (θ.symm (Multiplicative.ofAdd v))
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h
  rw [← rhoHom_apply] at h
  have h2 : θ ((MulAut.conjNormal t : MulAut A) (θ.symm (Multiplicative.ofAdd v))) =
      Multiplicative.ofAdd ((rhoHom A θ t).1.act v) := by
    rw [← h]; simp
  have h3 : (MulAut.conjNormal t : MulAut A) (θ.symm (Multiplicative.ofAdd v)) =
      θ.symm (Multiplicative.ofAdd ((rhoHom A θ t).1.act v)) := by
    rw [← h2]; simp
  have h4 := congrArg (fun a : A => (a : T)) h3
  simp only [MulAut.conjNormal_apply] at h4
  exact h4

theorem g96_ext {g h : G96} (H : ∀ v, g.1.act v = h.1.act v) : g = h := by
  apply Subtype.ext
  exact M4.ext_act (H (1, 0)) (H (0, 1))

theorem g96_act_mul (g h : G96) (v : Vec) : (g * h).1.act v = g.1.act (h.1.act v) :=
  M4.act_mul g.1 h.1 v

theorem g96_act_one (v : Vec) : (1 : G96).1.act v = v := M4.act_one v

theorem g96_act_inv' (g : G96) (v : Vec) : g.1.act (g⁻¹.1.act v) = v := by
  rw [← g96_act_mul, mul_inv_cancel, g96_act_one]

theorem rho_eq_one_iff (t : T) : rhoHom A θ t = 1 ↔ t ∈ Subgroup.centralizer (A : Set T) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    obtain ⟨v, rfl⟩ := exists_embT A θ ha
    have h1 := conj_embT A θ t v
    rw [h, g96_act_one] at h1
    calc embT A θ v * t = (t * embT A θ v * t⁻¹) * t := by rw [h1]
      _ = t * embT A θ v := by group
  · intro h
    apply g96_ext
    intro v
    apply embT_inj A θ
    rw [← conj_embT, g96_act_one]
    have h2 := h (embT A θ v) (embT_mem A θ v)
    rw [← h2]
    group

theorem ker_rho (hC : Subgroup.centralizer (A : Set T) = A) : (rhoHom A θ).ker = A := by
  ext t
  rw [MonoidHom.mem_ker, rho_eq_one_iff, hC]

theorem card_range_rho [Finite T] (hC : Subgroup.centralizer (A : Set T) = A)
    (hT : Nat.card T = 64) (hA : Nat.card A = 16) : Nat.card (rhoHom A θ).range = 4 := by
  have h := Subgroup.card_ker_mul_card_range (rhoHom A θ)
  rw [ker_rho A θ hC, hT, hA] at h
  omega

end Rho

section Coset

theorem exists_fixed_in_coset {T : Type} [Group T] [Finite T] (x : MulAut T) (hx : x ^ 3 = 1)
    (A : Subgroup T) (hA : ∀ a ∈ A, x a ∈ A) (hcard : Nat.card A % 3 = 1) (t : T)
    (ht : t⁻¹ * x t ∈ A) : ∃ s : T, t⁻¹ * s ∈ A ∧ x s = s := by
  classical
  have hmem : ∀ s : T, t⁻¹ * s ∈ A → t⁻¹ * x s ∈ A := by
    intro s hs
    have h1 : t⁻¹ * x s = (t⁻¹ * x t) * x (t⁻¹ * s) := by
      rw [map_mul, map_inv]; group
    rw [h1]; exact mul_mem ht (hA _ hs)
  let α : Type := {s : T // t⁻¹ * s ∈ A}
  have : Fintype α := Fintype.ofFinite α
  let f : Function.End α := fun s => ⟨x s.1, hmem s.1 s.2⟩
  have hf : ∀ k : ℕ, ∀ s : α, ((f ^ k) s : T) = (x ^ k) s.1 := by
    intro k
    induction k with
    | zero => intro s; rfl
    | succ k ih =>
      intro s
      rw [pow_succ, pow_succ]
      show ((f ^ k) (f s) : T) = (x ^ k) (x s.1)
      rw [ih]
  have hfp : f ^ 3 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    rw [pow_one, hf, hx]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hfp
  have hα : Fintype.card α = Nat.card A := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun s => ⟨t⁻¹ * s.1, s.2⟩
        invFun := fun a => ⟨t * a.1, by simp⟩
        left_inv := fun s => by apply Subtype.ext; simp
        right_inv := fun a => by apply Subtype.ext; simp }
  have hne : Fintype.card f.fixedPoints ≠ 0 := by
    intro h0
    have : Fintype.card α % 3 = Fintype.card f.fixedPoints % 3 := hmod
    rw [h0, hα, hcard] at this
    omega
  obtain ⟨⟨s, hs⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hne)
  refine ⟨s.1, s.2, ?_⟩
  have : f s = s := hs
  exact congrArg Subtype.val this

end Coset

section Res

variable {T : Type} [Group T] [Finite T]

@[expose] def xResHom (x : MulAut T) (A : Subgroup T) (hA : ∀ a ∈ A, x a ∈ A) : ↥A →* ↥A where
  toFun a := ⟨x a.1, hA a.1 a.2⟩
  map_one' := Subtype.ext (map_one x)
  map_mul' a b := Subtype.ext (map_mul x a.1 b.1)

@[expose] noncomputable def xRes (x : MulAut T) (A : Subgroup T) (hA : ∀ a ∈ A, x a ∈ A) :
    MulAut ↥A :=
  MulEquiv.ofBijective (xResHom x A hA) (by
    have hinj : Function.Injective (xResHom x A hA) := by
      intro a b h
      exact Subtype.ext (x.injective (congrArg Subtype.val h))
    exact Finite.injective_iff_bijective.mp hinj)

theorem xRes_pow (x : MulAut T) (A : Subgroup T) (hA : ∀ a ∈ A, x a ∈ A) (n : ℕ) (a : A) :
    (((xRes x A hA ^ n) a : A) : T) = (x ^ n) a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
    rfl

variable (A : Subgroup T) (θ : A ≃* Z4Z4) (x : MulAut T) (hA : ∀ a ∈ A, x a ∈ A)

@[expose] noncomputable def xi : G96 := phiB θ (xRes x A hA)

theorem x_embT (v : Vec) : x (embT A θ v) = embT A θ ((xi A θ x hA).1.act v) := by
  have h := toAdd_phiB θ (xRes x A hA) (θ.symm (Multiplicative.ofAdd v))
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd] at h
  have h' : Multiplicative.toAdd (θ (xRes x A hA (θ.symm (Multiplicative.ofAdd v)))) =
      (xi A θ x hA).1.act v := h
  have h2 : θ (xRes x A hA (θ.symm (Multiplicative.ofAdd v))) =
      Multiplicative.ofAdd ((xi A θ x hA).1.act v) := by
    rw [← h']; simp
  have h3 : xRes x A hA (θ.symm (Multiplicative.ofAdd v)) =
      θ.symm (Multiplicative.ofAdd ((xi A θ x hA).1.act v)) := by
    rw [← h2]; simp
  exact congrArg (fun a : A => (a : T)) h3

theorem rho_x [A.Normal] (t : T) :
    rhoHom A θ (x t) = xi A θ x hA * rhoHom A θ t * (xi A θ x hA)⁻¹ := by
  apply g96_ext
  intro v
  apply embT_inj A θ
  have e1 : embT A θ ((rhoHom A θ (x t)).1.act v) = x t * embT A θ v * (x t)⁻¹ :=
    (conj_embT A θ (x t) v).symm
  have e2 : embT A θ ((xi A θ x hA * rhoHom A θ t * (xi A θ x hA)⁻¹).1.act v) =
      x t * embT A θ v * (x t)⁻¹ := by
    rw [g96_act_mul, g96_act_mul, ← x_embT, ← conj_embT, map_mul, map_mul, x_embT A θ x hA,
      g96_act_inv', map_inv]
  rw [e1, e2]

theorem xi_pow_three (hx : x ^ 3 = 1) : xi A θ x hA ^ 3 = 1 := by
  unfold xi
  rw [← map_pow]
  have : xRes x A hA ^ 3 = 1 := by
    refine MulEquiv.ext fun a => ?_
    apply Subtype.ext
    rw [xRes_pow, hx]
    rfl
  rw [this, map_one]

theorem xi_ne_one (hfix : ∀ g : T, x g = g → g = 1) : xi A θ x hA ≠ 1 := by
  intro h
  have h1 : ∀ v, embT A θ v = 1 := by
    intro v
    apply hfix
    rw [x_embT A θ x hA, h, g96_act_one]
  have := embT_inj A θ ((h1 (1, 0)).trans (h1 (0, 0)).symm)
  exact absurd this (by decide)

theorem xi_mem_ord3 (hx : x ^ 3 = 1) (hfix : ∀ g : T, x g = g → g = 1) :
    (xi A θ x hA).1 ∈ ord3list := by
  have h3 : xi A θ x hA * xi A θ x hA * xi A θ x hA = 1 := by
    rw [← pow_three']; exact xi_pow_three A θ x hA hx
  refine (ord3_iff _ (xi A θ x hA).2).mp ⟨congrArg Subtype.val h3, ?_⟩
  intro h
  exact xi_ne_one A θ x hA hfix (Subtype.ext h)

theorem xi_fpf [A.Normal] (hx : x ^ 3 = 1) (hfix : ∀ g : T, x g = g → g = 1)
    (hC : Subgroup.centralizer (A : Set T) = A) (hA16 : Nat.card A = 16) (t : T)
    (ht : xi A θ x hA * rhoHom A θ t * (xi A θ x hA)⁻¹ = rhoHom A θ t) : rhoHom A θ t = 1 := by
  rw [← rho_x A θ x hA] at ht
  have h1 : t⁻¹ * x t ∈ A := by
    rw [← ker_rho A θ hC, MonoidHom.mem_ker, map_mul, map_inv, ht, inv_mul_cancel]
  obtain ⟨s, hs, hxs⟩ := exists_fixed_in_coset x hx A hA (by rw [hA16]) t h1
  have hs1 : s = 1 := hfix s hxs
  rw [hs1, mul_one] at hs
  have : t ∈ A := by simpa using inv_mem hs
  rw [← MonoidHom.mem_ker, ker_rho A θ hC]
  exact this

end Res

end L23

end CFSG.GH74.GLS.Bg.TwoGroups
