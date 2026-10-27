module

public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory.SteinbergBS

open Subgroup

variable {G : Type*} [Group G] {α : MulAut G}

theorem bijective_inv_mul_apply [Finite G] (hα : MonoidHom.FixedPointFree α) :
    Function.Bijective fun x : G => x⁻¹ * α x := by
  have h1 : (fun x : G => x⁻¹ * α x) = MonoidHom.commutatorMap α ∘ fun x => x⁻¹ := by
    funext x
    simp [MonoidHom.commutatorMap, div_eq_mul_inv]
  rw [h1]
  exact Function.Bijective.comp ⟨hα.commutatorMap_injective, hα.commutatorMap_surjective⟩
    inv_involutive.bijective

theorem bijective_apply_mul_inv [Finite G] (hα : MonoidHom.FixedPointFree α) :
    Function.Bijective fun x : G => α x * x⁻¹ := by
  have h1 : (fun x : G => α x * x⁻¹) = (fun x => x⁻¹) ∘ MonoidHom.commutatorMap α := by
    funext x
    simp [MonoidHom.commutatorMap, div_eq_mul_inv]
  rw [h1]
  exact Function.Bijective.comp inv_involutive.bijective
    ⟨hα.commutatorMap_injective, hα.commutatorMap_surjective⟩

theorem fixedPointFree_quotientCongr [Finite G] (hα : MonoidHom.FixedPointFree α) (N : Subgroup G)
    [N.Normal] (hN : N.map (α : G →* G) = N) :
    MonoidHom.FixedPointFree (QuotientGroup.congr N N α hN) := by
  intro x' hx'
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x'
  rw [QuotientGroup.congr_mk, QuotientGroup.eq] at hx'
  have hxN : x⁻¹ * α x ∈ N := by
    have := inv_mem hx'
    rwa [mul_inv_rev, inv_inv] at this
  have hαN : ∀ n ∈ N, α n ∈ N := fun n hn => hN ▸ mem_map_of_mem _ hn
  have hmem : ∀ n : N, (x * n)⁻¹ * α (x * n) ∈ N := fun n => by
    have e : (x * (n : G))⁻¹ * α (x * n) = (n : G)⁻¹ * (x⁻¹ * α x) * α n := by
      rw [map_mul]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem n.2) hxN) (hαN _ n.2)
  set φ : N → N := fun n => ⟨(x * n)⁻¹ * α (x * n), hmem n⟩ with hφ
  have hφinj : Function.Injective φ := fun n m h => by
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel ((bijective_inv_mul_apply hα).1 h1))
  obtain ⟨n, hn⟩ := (Finite.injective_iff_surjective.1 hφinj) 1
  have h1 : (x * n)⁻¹ * α (x * n) = 1 := congrArg Subtype.val hn
  have h2 : x * n = 1 := hα _ (inv_mul_eq_one.1 h1).symm
  rw [QuotientGroup.eq_one_iff]
  rw [mul_eq_one_iff_eq_inv] at h2
  rw [h2]
  exact inv_mem n.2

section Sylow

variable {p : ℕ}

theorem smul_smul_sylow (α : MulAut G) (y : G) (P : Sylow p G) :
    α • (y • P) = α y • (α • P) := by
  rw [Sylow.smul_def, Sylow.smul_def (g := α y), ← mul_smul, ← mul_smul]
  congr 1
  refine MulEquiv.ext fun z => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem existsUnique_smul_sylow_eq [Finite G] [Fact p.Prime] (hα : MonoidHom.FixedPointFree α) :
    ∃! P : Sylow p G, α • P = P := by
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G P (α • P)
  obtain ⟨y, hy⟩ := (bijective_inv_mul_apply hα).2 x⁻¹
  have hyx : α y * x = y := by
    have h1 : α y = y * x⁻¹ := by
      rw [← hy]
      group
    rw [h1, inv_mul_cancel_right]
  have hfix : α • (y • P) = y • P := by
    rw [smul_smul_sylow, ← hx, smul_smul, hyx]
  have huniq : ∀ P₁ P₂ : Sylow p G, α • P₁ = P₁ → α • P₂ = P₂ → P₂ = P₁ := by
    intro P₁ P₂ hP₁ hP₂
    obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq G P₁ P₂
    rw [smul_smul_sylow, hP₁] at hP₂
    have h1 : (x⁻¹ * α x) • P₁ = P₁ := by
      rw [← smul_smul, hP₂, smul_smul, inv_mul_cancel, one_smul]
    have hnorm : x⁻¹ * α x ∈ normalizer (P₁ : Set G) := Sylow.smul_eq_iff_mem_normalizer.1 h1
    have hαnorm : ∀ z ∈ normalizer (P₁ : Set G), α z ∈ normalizer (P₁ : Set G) := fun z hz => by
      rw [← Sylow.smul_eq_iff_mem_normalizer] at hz ⊢
      have h2 := smul_smul_sylow α z P₁
      rw [hz, hP₁] at h2
      exact h2.symm
    set ψ : normalizer (P₁ : Set G) → normalizer (P₁ : Set G) :=
      fun z => ⟨(z : G)⁻¹ * α z, mul_mem (inv_mem z.2) (hαnorm z z.2)⟩ with hψ
    have hψinj : Function.Injective ψ := fun z w h =>
      Subtype.ext ((bijective_inv_mul_apply hα).1 (congrArg Subtype.val h))
    obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hψinj) ⟨_, hnorm⟩
    have hzx : (z : G) = x := (bijective_inv_mul_apply hα).1 (congrArg Subtype.val hz)
    rw [← hzx]
    exact Sylow.smul_eq_iff_mem_normalizer.2 z.2
  exact ⟨y • P, hfix, fun P₂ hP₂ => huniq _ _ hfix hP₂⟩

end Sylow

section Prime

abbrev invariantRestrict (α : MulAut G) (H : Subgroup G) (hH : H.map α.toMonoidHom = H) :
    MulAut H :=
  (α.subgroupMap H).trans (MulEquiv.subgroupCongr hH)

theorem coe_invariantRestrict_pow (α : MulAut G) (H : Subgroup G)
    (hH : H.map α.toMonoidHom = H) (k : ℕ) (h : H) :
    ((invariantRestrict α H hH ^ k) h : G) = (α ^ k) h := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply, ← ih]
    rfl

theorem quotientCongr_pow_mk (α : MulAut G) (N : Subgroup G) [N.Normal]
    (hN : N.map (α : G →* G) = N) (k : ℕ) (x : G) :
    (QuotientGroup.congr N N α hN ^ k) (x : G ⧸ N) = ((α ^ k) x : G) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, QuotientGroup.congr_mk, ih, pow_succ, MulAut.mul_apply]

theorem not_dvd_card_of_orderOf_eq_prime [Finite G] (hα : MonoidHom.FixedPointFree α) {r : ℕ}
    (hr : r.Prime) (hαr : orderOf α = r) : ¬ r ∣ Nat.card G := by
  have : Fact r.Prime := ⟨hr⟩
  have hZ : IsPGroup r (zpowers α) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hαr, pow_one])
  have hmod := hZ.card_modEq_card_fixedPoints G
  have hfix : MulAction.fixedPoints (zpowers α) G = {1} := by
    ext g
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      exact hα g (h ⟨α, mem_zpowers α⟩)
    · rintro rfl z
      exact map_one (z : MulAut G)
  rw [hfix, Nat.card_unique (α := ↥({1} : Set G))] at hmod
  intro hdvd
  have h0 : Nat.card G ≡ 0 [MOD r] := Nat.modEq_zero_iff_dvd.2 hdvd
  have h1 := (h0.symm.trans hmod)
  rw [Nat.ModEq, Nat.zero_mod, Nat.one_mod_eq_one.2 hr.one_lt.ne'] at h1
  exact zero_ne_one h1

end Prime

theorem fixed_point_free_automorphism_quotients_and_sylows [Finite G] (α : MulAut G)
    (hα : MonoidHom.FixedPointFree α) :
    Function.Bijective (fun x : G => x⁻¹ * α x) ∧ Function.Bijective (fun x : G => α x * x⁻¹) ∧
      (∀ (N : Subgroup G) [N.Normal] (hN : N.map (α : G →* G) = N),
        MonoidHom.FixedPointFree (QuotientGroup.congr N N α hN)) ∧
      (∀ (p : ℕ) [Fact p.Prime], ∃! P : Sylow p G, α • P = P) ∧
      ∀ r : ℕ, r.Prime → orderOf α = r →
        ¬ r ∣ Nat.card G ∧
        (∀ (H : Subgroup G) (hH : H.map α.toMonoidHom = H), H ≠ ⊥ →
          orderOf (invariantRestrict α H hH) = r) ∧
        (∀ (N : Subgroup G) [N.Normal] (hN : N.map (α : G →* G) = N), N ≠ ⊤ →
          orderOf (QuotientGroup.congr N N α hN) = r) := by
  refine ⟨bijective_inv_mul_apply hα, bijective_apply_mul_inv hα,
    fun N _ hN => fixedPointFree_quotientCongr hα N hN, fun p _ => existsUnique_smul_sylow_eq hα,
    fun r hr hαr => ⟨not_dvd_card_of_orderOf_eq_prime hα hr hαr, fun H hH hH1 => ?_,
      fun N _ hN hN1 => ?_⟩⟩
  ·
    have hpow : invariantRestrict α H hH ^ r = 1 := MulEquiv.ext fun h => Subtype.ext (by
      rw [coe_invariantRestrict_pow, ← hαr, pow_orderOf_eq_one]
      rfl)
    rcases (Nat.dvd_prime hr).1 (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
    · exfalso
      apply hH1
      rw [eq_bot_iff]
      intro h hh
      rw [orderOf_eq_one_iff] at h1
      have h2 := congrArg (fun φ : MulAut H => (φ ⟨h, hh⟩ : G)) h1
      exact hα h h2
    · exact h1
  ·
    have hpow : QuotientGroup.congr N N α hN ^ r = 1 := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      rw [quotientCongr_pow_mk, ← hαr, pow_orderOf_eq_one]
      rfl
    rcases (Nat.dvd_prime hr).1 (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
    · exfalso
      apply hN1
      rw [eq_top_iff]
      intro x _
      rw [orderOf_eq_one_iff] at h1
      have h2 := fixedPointFree_quotientCongr hα N hN (x : G ⧸ N) (by rw [h1]; rfl)
      exact (QuotientGroup.eq_one_iff x).1 h2
    · exact h1

end CFSG.GroupTheory.SteinbergBS
