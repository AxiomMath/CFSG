module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbDefs

public section

open Subgroup

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace IIbSyl

variable {G : Type*} [Group G]

@[expose] def pairHom (n : ℕ) [NeZero n] (x y : G) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hxy : x * y = y * x) : Multiplicative (ZMod n × ZMod n) →* G where
  toFun c := x ^ (Multiplicative.toAdd c).1.val * y ^ (Multiplicative.toAdd c).2.val
  map_one' := by simp
  map_mul' c d := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hy, pow_add, pow_add]
    have hc : y ^ (Multiplicative.toAdd c).2.val * x ^ (Multiplicative.toAdd d).1.val =
        x ^ (Multiplicative.toAdd d).1.val * y ^ (Multiplicative.toAdd c).2.val :=
      ((Commute.pow_pow (show Commute x y from hxy) _ _).symm).eq
    rw [mul_assoc (x ^ _), mul_assoc (x ^ _)]
    congr 1
    rw [← mul_assoc, ← mul_assoc, hc]

theorem C0_eq_mul : ∀ c : C0, c = Multiplicative.ofAdd ((1 : ZMod 4), (0 : ZMod 4)) ^
    (Multiplicative.toAdd c).1.val *
      Multiplicative.ofAdd ((0 : ZMod 4), (1 : ZMod 4)) ^ (Multiplicative.toAdd c).2.val := by
  decide

theorem R0_eq_mul : ∀ r : R0, r = Multiplicative.ofAdd ((1 : ZMod 2), (0 : ZMod 2)) ^
    (Multiplicative.toAdd r).1.val *
      Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2)) ^ (Multiplicative.toAdd r).2.val := by
  decide

theorem C0_hom_ext {f f' : C0 →* G}
    (h₁ : f (Multiplicative.ofAdd (1, 0)) = f' (Multiplicative.ofAdd (1, 0)))
    (h₂ : f (Multiplicative.ofAdd (0, 1)) = f' (Multiplicative.ofAdd (0, 1))) : f = f' := by
  refine MonoidHom.ext fun c => ?_
  rw [C0_eq_mul c, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h₁, h₂]

theorem R0_hom_ext {f f' : R0 →* G}
    (h₁ : f (Multiplicative.ofAdd (1, 0)) = f' (Multiplicative.ofAdd (1, 0)))
    (h₂ : f (Multiplicative.ofAdd (0, 1)) = f' (Multiplicative.ofAdd (0, 1))) : f = f' := by
  refine MonoidHom.ext fun r => ?_
  rw [R0_eq_mul r, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h₁, h₂]

theorem rho_a_g₁ : rho (Multiplicative.ofAdd (1, 0)) (Multiplicative.ofAdd (1, 0)) =
    Multiplicative.ofAdd (3, 0) := by decide

theorem rho_a_g₂ : rho (Multiplicative.ofAdd (1, 0)) (Multiplicative.ofAdd (0, 1)) =
    Multiplicative.ofAdd (0, 3) := by decide

theorem rho_σ_g₁ : rho (Multiplicative.ofAdd (0, 1)) (Multiplicative.ofAdd (1, 0)) =
    Multiplicative.ofAdd (1, 2) := by decide

theorem rho_σ_g₂ : rho (Multiplicative.ofAdd (0, 1)) (Multiplicative.ofAdd (0, 1)) =
    Multiplicative.ofAdd (2, 3) := by decide

theorem theta_g₁ : theta (SemidirectProduct.inl (Multiplicative.ofAdd (1, 0))) =
    SemidirectProduct.inl (Multiplicative.ofAdd (3, 0)) := by decide

theorem theta_g₂ : theta (SemidirectProduct.inl (Multiplicative.ofAdd (0, 1))) =
    SemidirectProduct.inl (Multiplicative.ofAdd (3, 1)) := by decide

theorem theta_a : theta (SemidirectProduct.inr (Multiplicative.ofAdd (1, 0))) =
    SemidirectProduct.inr (Multiplicative.ofAdd (1, 0)) := by decide

theorem theta_σ : theta (SemidirectProduct.inr (Multiplicative.ofAdd (0, 1))) =
    SemidirectProduct.inr (Multiplicative.ofAdd (1, 1)) := by decide

theorem center_IIbSyl : ∀ s : IIbSyl, (∀ u : IIbSyl, s * u = u * s) → s = 1 ∨ s = z0 := by
  have key : ∀ s : IIbSyl,
      s * SemidirectProduct.inl (SemidirectProduct.inl (Multiplicative.ofAdd (1, 0))) =
        SemidirectProduct.inl (SemidirectProduct.inl (Multiplicative.ofAdd (1, 0))) * s →
      s * SemidirectProduct.inl (SemidirectProduct.inl (Multiplicative.ofAdd (0, 1))) =
        SemidirectProduct.inl (SemidirectProduct.inl (Multiplicative.ofAdd (0, 1))) * s →
      s * a = a * s → s * sigma = sigma * s → s * t = t * s → s = 1 ∨ s = z0 := by
    decide +kernel
  intro s hs
  exact key s (hs _) (hs _) (hs _) (hs _) (hs _)

theorem isPGroup_IIbSyl : IsPGroup 2 IIbSyl :=
  IsPGroup.of_card (n := 7) (by rw [card_IIbSyl]; norm_num)

theorem injective_of_ne_one {G : Type*} [Group G] (f : IIbSyl →* G) (hf : f z0 ≠ 1) :
    Function.Injective f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent IIbSyl := isPGroup_IIbSyl.isNilpotent
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  obtain ⟨t, ht1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨htk, htc⟩ := mem_inf.mp t.2
  rcases center_IIbSyl t (fun u => ((mem_center_iff.mp htc) u).symm) with h1 | h1
  · exact ht1 (Subtype.ext h1)
  · rw [h1, MonoidHom.mem_ker] at htk
    exact hf htk

end IIbSyl

variable {G : Type*} [Group G]

structure P0Gens (G : Type*) [Group G] where
  g₁ : G
  g₂ : G
  a : G
  σ : G
  a_sq : a * a = 1
  σ_sq : σ * σ = 1
  a_σ : a * σ = σ * a
  g₁_pow : g₁ ^ 4 = 1
  g₂_pow : g₂ ^ 4 = 1
  g₁_g₂ : g₁ * g₂ = g₂ * g₁
  a_g₁ : a * g₁ * a⁻¹ = g₁ ^ 3
  a_g₂ : a * g₂ * a⁻¹ = g₂ ^ 3
  σ_g₁ : σ * g₁ * σ⁻¹ = g₁ * g₂ ^ 2
  σ_g₂ : σ * g₂ * σ⁻¹ = g₁ ^ 2 * g₂ ^ 3

namespace P0Gens

variable (q : P0Gens G)

@[expose] def homC : IIbSyl.C0 →* G := IIbSyl.pairHom 4 q.g₁ q.g₂ q.g₁_pow q.g₂_pow q.g₁_g₂

@[expose] def homR : IIbSyl.R0 →* G :=
  IIbSyl.pairHom 2 q.a q.σ (by rw [sq]; exact q.a_sq) (by rw [sq]; exact q.σ_sq) q.a_σ

theorem homC_g₁ : q.homC (Multiplicative.ofAdd (1, 0)) = q.g₁ := by
  change q.g₁ ^ 1 * q.g₂ ^ 0 = q.g₁
  simp

theorem homC_g₂ : q.homC (Multiplicative.ofAdd (0, 1)) = q.g₂ := by
  change q.g₁ ^ 0 * q.g₂ ^ 1 = q.g₂
  simp

theorem homR_a : q.homR (Multiplicative.ofAdd (1, 0)) = q.a := by
  change q.a ^ 1 * q.σ ^ 0 = q.a
  simp

theorem homR_σ : q.homR (Multiplicative.ofAdd (0, 1)) = q.σ := by
  change q.a ^ 0 * q.σ ^ 1 = q.σ
  simp

theorem homC_30 : q.homC (Multiplicative.ofAdd (3, 0)) = q.g₁ ^ 3 := by
  change q.g₁ ^ 3 * q.g₂ ^ 0 = q.g₁ ^ 3
  rw [pow_zero, mul_one]

theorem homC_03 : q.homC (Multiplicative.ofAdd (0, 3)) = q.g₂ ^ 3 := by
  change q.g₁ ^ 0 * q.g₂ ^ 3 = q.g₂ ^ 3
  rw [pow_zero, one_mul]

theorem homC_12 : q.homC (Multiplicative.ofAdd (1, 2)) = q.g₁ * q.g₂ ^ 2 := by
  change q.g₁ ^ 1 * q.g₂ ^ 2 = q.g₁ * q.g₂ ^ 2
  rw [pow_one]

theorem homC_23 : q.homC (Multiplicative.ofAdd (2, 3)) = q.g₁ ^ 2 * q.g₂ ^ 3 := rfl

theorem homC_31 : q.homC (Multiplicative.ofAdd (3, 1)) = q.g₁ ^ 3 * q.g₂ := by
  change q.g₁ ^ 3 * q.g₂ ^ 1 = q.g₁ ^ 3 * q.g₂
  rw [pow_one]

theorem homR_11 : q.homR (Multiplicative.ofAdd (1, 1)) = q.a * q.σ := by
  change q.a ^ 1 * q.σ ^ 1 = q.a * q.σ
  rw [pow_one, pow_one]

@[expose] def Compat (r : IIbSyl.R0) : Prop :=
  q.homC.comp (IIbSyl.rho r).toMonoidHom = (MulAut.conj (q.homR r)).toMonoidHom.comp q.homC

theorem compat_mul {r s : IIbSyl.R0} (hr : q.Compat r) (hs : q.Compat s) : q.Compat (r * s) := by
  unfold Compat at *
  refine MonoidHom.ext fun c => ?_
  have h1 := DFunLike.congr_fun hr ((IIbSyl.rho s) c)
  have h2 := DFunLike.congr_fun hs c
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1 h2 ⊢
  rw [map_mul, MulAut.mul_apply, h1, h2, map_mul]
  group

theorem compat_one : q.Compat 1 := by
  unfold Compat
  rw [map_one, map_one]
  ext c
  simp

theorem compat_a : q.Compat (Multiplicative.ofAdd (1, 0)) := by
  unfold Compat
  apply IIbSyl.C0_hom_ext
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [IIbSyl.rho_a_g₁, homC_30, homR_a, homC_g₁, MulAut.conj_apply, q.a_g₁]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [IIbSyl.rho_a_g₂, homC_03, homR_a, homC_g₂, MulAut.conj_apply, q.a_g₂]

theorem compat_σ : q.Compat (Multiplicative.ofAdd (0, 1)) := by
  unfold Compat
  apply IIbSyl.C0_hom_ext
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [IIbSyl.rho_σ_g₁, homC_12, homR_σ, homC_g₁, MulAut.conj_apply, q.σ_g₁]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [IIbSyl.rho_σ_g₂, homC_23, homR_σ, homC_g₂, MulAut.conj_apply, q.σ_g₂]

theorem compat_pow {r : IIbSyl.R0} (hr : q.Compat r) : ∀ k : ℕ, q.Compat (r ^ k) := by
  intro k
  induction k with
  | zero => rw [pow_zero]; exact q.compat_one
  | succ k ih => rw [pow_succ]; exact q.compat_mul ih hr

theorem compat (r : IIbSyl.R0) : q.Compat r := by
  rw [IIbSyl.R0_eq_mul r]
  exact q.compat_mul (q.compat_pow q.compat_a _) (q.compat_pow q.compat_σ _)

@[expose] def hom : IIbSyl.P0 →* G := SemidirectProduct.lift q.homC q.homR q.compat

theorem hom_inl (c : IIbSyl.C0) : q.hom (SemidirectProduct.inl c) = q.homC c :=
  SemidirectProduct.lift_inl _ _ _ _

theorem hom_inr (r : IIbSyl.R0) : q.hom (SemidirectProduct.inr r) = q.homR r :=
  SemidirectProduct.lift_inr _ _ _ _

end P0Gens

structure SGens (G : Type*) [Group G] extends P0Gens G where
  t : G
  t_sq : t * t = 1
  t_g₁ : t * g₁ * t⁻¹ = g₁ ^ 3
  t_g₂ : t * g₂ * t⁻¹ = g₁ ^ 3 * g₂
  t_a : t * a * t⁻¹ = a
  t_σ : t * σ * t⁻¹ = a * σ

namespace SGens

variable (q : SGens G)

@[expose] def chi : Multiplicative (ZMod 2) →* G where
  toFun e := if e = 1 then 1 else q.t
  map_one' := by simp
  map_mul' a b := by
    have hcases : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
    have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    have hsq : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
    · simp
    · simp
    · simp
    · rw [hsq]
      simp [hne, q.t_sq]

theorem chi_ofAdd : q.chi (Multiplicative.ofAdd 1) = q.t := by
  have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  simp [chi, hne]

theorem theta_compat : q.toP0Gens.hom.comp IIbSyl.theta.toMonoidHom =
    (MulAut.conj q.t).toMonoidHom.comp q.toP0Gens.hom := by
  apply SemidirectProduct.hom_ext
  · apply IIbSyl.C0_hom_ext
    · change q.toP0Gens.hom (IIbSyl.theta (SemidirectProduct.inl (Multiplicative.ofAdd (1, 0)))) =
        q.t * q.toP0Gens.hom (SemidirectProduct.inl (Multiplicative.ofAdd (1, 0))) * q.t⁻¹
      rw [IIbSyl.theta_g₁, P0Gens.hom_inl, P0Gens.hom_inl, P0Gens.homC_30, P0Gens.homC_g₁,
        q.t_g₁]
    · change q.toP0Gens.hom (IIbSyl.theta (SemidirectProduct.inl (Multiplicative.ofAdd (0, 1)))) =
        q.t * q.toP0Gens.hom (SemidirectProduct.inl (Multiplicative.ofAdd (0, 1))) * q.t⁻¹
      rw [IIbSyl.theta_g₂, P0Gens.hom_inl, P0Gens.hom_inl, P0Gens.homC_31, P0Gens.homC_g₂,
        q.t_g₂]
  · apply IIbSyl.R0_hom_ext
    · change q.toP0Gens.hom (IIbSyl.theta (SemidirectProduct.inr (Multiplicative.ofAdd (1, 0)))) =
        q.t * q.toP0Gens.hom (SemidirectProduct.inr (Multiplicative.ofAdd (1, 0))) * q.t⁻¹
      rw [IIbSyl.theta_a, P0Gens.hom_inr, P0Gens.homR_a, q.t_a]
    · change q.toP0Gens.hom (IIbSyl.theta (SemidirectProduct.inr (Multiplicative.ofAdd (0, 1)))) =
        q.t * q.toP0Gens.hom (SemidirectProduct.inr (Multiplicative.ofAdd (0, 1))) * q.t⁻¹
      rw [IIbSyl.theta_σ, P0Gens.hom_inr, P0Gens.hom_inr, P0Gens.homR_11, P0Gens.homR_σ, q.t_σ]

theorem compat (e : Multiplicative (ZMod 2)) :
    q.toP0Gens.hom.comp (IIbSyl.psi e).toMonoidHom =
      (MulAut.conj (q.chi e)).toMonoidHom.comp q.toP0Gens.hom := by
  have hcases : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
  rcases hcases e with rfl | rfl
  · ext p
    simp
  · have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    have hpsi : IIbSyl.psi (Multiplicative.ofAdd 1) = IIbSyl.theta := by
      simp [IIbSyl.psi, hne]
    rw [hpsi, q.chi_ofAdd]
    exact q.theta_compat

@[expose] def hom : IIbSyl →* G := SemidirectProduct.lift q.toP0Gens.hom q.chi q.compat

theorem hom_inl (p : IIbSyl.P0) : q.hom (SemidirectProduct.inl p) = q.toP0Gens.hom p :=
  SemidirectProduct.lift_inl _ _ _ _

theorem hom_inr (e : Multiplicative (ZMod 2)) : q.hom (SemidirectProduct.inr e) = q.chi e :=
  SemidirectProduct.lift_inr _ _ _ _

end SGens

end CFSG.ComponentClassification.RankTwoAltFive
