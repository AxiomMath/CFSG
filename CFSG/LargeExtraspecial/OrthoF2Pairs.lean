module

public import CFSG.LargeExtraspecial.OrthoF2Timmesfeld12

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

namespace OrthoF2

section Ring

variable {R : Type*} [Ring R]

theorem braid_of_pair (h2 : ∀ x : R, x + x = 0) {φ ψ : R} (hφ : φ * φ = 0) (hψ : ψ * ψ = 0)
    (hφψφ : φ * ψ * φ = φ) (hψφψ : ψ * φ * ψ = ψ) :
    (1 + φ) * (1 + ψ) * (1 + φ) = (1 + ψ) * (1 + φ) * (1 + ψ) := by
  have e : (1 + φ) * (1 + ψ) * (1 + φ) - (1 + ψ) * (1 + φ) * (1 + ψ) =
      (φ * ψ * φ + φ) - (ψ * φ * ψ + ψ) + φ * φ - ψ * ψ := by noncomm_ring
  rw [hφψφ, hψφψ, hφ, hψ, h2, h2, sub_zero, add_zero, sub_zero] at e
  exact sub_eq_zero.mp e

theorem sq_of_pair (h2 : ∀ x : R, x + x = 0) {φ ψ : R} (hφ : φ * φ = 0) (hψ : ψ * ψ = 0)
    (hφψφ : φ * ψ * φ = 0) (hψφψ : ψ * φ * ψ = 0) :
    (1 + φ) * (1 + ψ) * ((1 + φ) * (1 + ψ)) = 1 + φ * ψ + ψ * φ := by
  have e : (1 + φ) * (1 + ψ) * ((1 + φ) * (1 + ψ)) = 1 + φ * ψ + ψ * φ + (φ + φ) + (ψ + ψ) +
      (φ * ψ + φ * ψ) + φ * φ + ψ * ψ + φ * ψ * φ + ψ * φ * ψ + φ * (ψ * ψ) + φ * φ * ψ +
      φ * ψ * φ * ψ := by noncomm_ring
  rw [e, hφψφ, hψφψ, hφ, hψ, h2, h2, h2]
  simp

theorem sq_sq_of_pair (h2 : ∀ x : R, x + x = 0) {φ ψ : R} (hφ : φ * φ = 0) (hψ : ψ * ψ = 0)
    (hφψφ : φ * ψ * φ = 0) (hψφψ : ψ * φ * ψ = 0) :
    (1 + φ * ψ + ψ * φ) * (1 + φ * ψ + ψ * φ) = 1 := by
  have e : (1 + φ * ψ + ψ * φ) * (1 + φ * ψ + ψ * φ) = 1 + (φ * ψ + φ * ψ) + (ψ * φ + ψ * φ) +
      φ * ψ * φ * ψ + φ * (ψ * ψ) * φ + ψ * (φ * φ) * ψ + ψ * φ * ψ * φ := by noncomm_ring
  rw [e, hφψφ, hψφψ, hφ, hψ, h2, h2]
  simp

theorem sub_one_mul_sub_one (h2 : ∀ x : R, x + x = 0) {a : R} (h : a * a = 1) :
    (a - 1) * (a - 1) = 0 := by
  have e : (a - 1) * (a - 1) = a * a - (a + a) + 1 := by noncomm_ring
  rw [e, h, h2, sub_zero, h2]

theorem pow_three_eq_one_of_braid {M : Type*} [Monoid M] {a b : M} (ha : a * a = 1)
    (hb : b * b = 1) (h : a * b * a = b * a * b) : (a * b) ^ 3 = 1 := by
  calc (a * b) ^ 3 = (a * b * a) * (b * a * b) := by simp only [pow_succ, pow_zero, one_mul,
        mul_assoc]
    _ = b * a * (b * b) * a * b := by rw [h]; simp only [mul_assoc]
    _ = 1 := by rw [hb, mul_one, mul_assoc b a a, ha, mul_one, hb]

end Ring

theorem end_add_self (x : Module.End (ZMod 2) V) : x + x = 0 :=
  LinearMap.ext fun v => by rw [LinearMap.add_apply, vec_add_self, LinearMap.zero_apply]

theorem pair_smul_aux₁ (m11 m12 m21 m22 : ZMod 2) (a1 a2 : V) :
    m11 • (m12 • a2 + m22 • a1) + m12 • (m11 • a2 + m21 • a1) =
      (m11 * m22 + m12 * m21) • a1 := by
  match_scalars
  all_goals (revert m11 m12 m21 m22; decide)

theorem pair_smul_aux₂ (m11 m12 m21 m22 : ZMod 2) (a1 a2 : V) :
    m21 • (m12 • a2 + m22 • a1) + m22 • (m11 • a2 + m21 • a1) =
      (m11 * m22 + m12 * m21) • a2 := by
  match_scalars
  all_goals (revert m11 m12 m21 m22; decide)

theorem comp_comp_eq_smul {φ ψ : V →ₗ[ZMod 2] V} {a1 a2 b1 b2 : V}
    (hφ : ∀ v, φ v = polar q v a1 • a2 + polar q v a2 • a1)
    (hψ : ∀ v, ψ v = polar q v b1 • b2 + polar q v b2 • b1) (v : V) :
    φ (ψ (φ v)) =
      (polar q a1 b1 * polar q a2 b2 + polar q a1 b2 * polar q a2 b1) • φ v := by
  have h1 : φ (ψ a1) =
      (polar q a1 b1 * polar q a2 b2 + polar q a1 b2 * polar q a2 b1) • a1 := by
    rw [hψ, map_add, map_smul, map_smul, hφ, hφ, polar_comm q b2 a1, polar_comm q b2 a2,
      polar_comm q b1 a1, polar_comm q b1 a2]
    exact pair_smul_aux₁ _ _ _ _ a1 a2
  have h2 : φ (ψ a2) =
      (polar q a1 b1 * polar q a2 b2 + polar q a1 b2 * polar q a2 b1) • a2 := by
    rw [hψ, map_add, map_smul, map_smul, hφ, hφ, polar_comm q b2 a1, polar_comm q b2 a2,
      polar_comm q b1 a1, polar_comm q b1 a2]
    exact pair_smul_aux₂ _ _ _ _ a1 a2
  rw [hφ v, map_add, map_smul, map_smul, map_add, map_smul, map_smul, h1, h2, smul_add,
    smul_comm _ (polar q v a1), smul_comm _ (polar q v a2)]

theorem exists_sub_apply_of_isTypeA [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2) :
    ∃ a1 a2 : V, LinearIndependent (ZMod 2) ![a1, a2] ∧
      commSpace α = Submodule.span (ZMod 2) {a1, a2} ∧ q a1 = 0 ∧ q a2 = 0 ∧
      polar q a1 a2 = 0 ∧ ∀ v, α v - v = polar q v a1 • a2 + polar q v a2 • a1 := by
  obtain ⟨a1, a2, hli, hspan⟩ := exists_pair_of_finrank_eq_two hα.2.2.2.1
  obtain ⟨h1, h2, h12, hE⟩ := eq_eichler_of_isTypeA hq hα hli hspan.symm
  refine ⟨a1, a2, hli, hspan.symm, h1, h2, h12, fun v => ?_⟩
  rw [hE, eichler_apply_zmod2 h1 h12, h2, zero_mul, add_zero, add_assoc, add_sub_cancel_left]

theorem sub_one_apply (α : V ≃ₗ[ZMod 2] V) (v : V) :
    ((α : V →ₗ[ZMod 2] V) - 1) v = α v - v :=
  rfl

theorem exists_pair_scalar [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2) (hβ : IsTypeA q β 2) :
    ∃ d : ZMod 2,
      ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) =
        d • ((α : V →ₗ[ZMod 2] V) - 1) ∧
      ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) =
        d • ((β : V →ₗ[ZMod 2] V) - 1) := by
  obtain ⟨a1, a2, -, -, -, -, -, ha⟩ := exists_sub_apply_of_isTypeA hq hα
  obtain ⟨b1, b2, -, -, -, -, -, hb⟩ := exists_sub_apply_of_isTypeA hq hβ
  refine ⟨polar q a1 b1 * polar q a2 b2 + polar q a1 b2 * polar q a2 b1, ?_, ?_⟩
  · refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply]
    exact comp_comp_eq_smul (q := q) (φ := (α : V →ₗ[ZMod 2] V) - 1)
      (ψ := (β : V →ₗ[ZMod 2] V) - 1) (fun v => ha v) (fun v => hb v) v
  · refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply]
    have h := comp_comp_eq_smul (q := q) (φ := (β : V →ₗ[ZMod 2] V) - 1)
      (ψ := (α : V →ₗ[ZMod 2] V) - 1) (fun v => hb v) (fun v => ha v) v
    rw [polar_comm q b1 a1, polar_comm q b2 a2, polar_comm q b1 a2, polar_comm q b2 a1,
      mul_comm (polar q a2 b1)] at h
    exact h

theorem sub_one_mul_sub_one_of_mul_self {t : V ≃ₗ[ZMod 2] V} (htt : t * t = 1) :
    ((t : V →ₗ[ZMod 2] V) - 1) * ((t : V →ₗ[ZMod 2] V) - 1) = 0 := by
  refine sub_one_mul_sub_one end_add_self ?_
  rw [← LinearEquiv.coe_toLinearMap_mul, htt]
  rfl

theorem coe_eq_one_add_sub_one (t : V ≃ₗ[ZMod 2] V) :
    (t : V →ₗ[ZMod 2] V) = 1 + ((t : V →ₗ[ZMod 2] V) - 1) := by
  abel

theorem mul_pow_three_eq_one_of_scalar_one {α β : V ≃ₗ[ZMod 2] V} (hαα : α * α = 1)
    (hββ : β * β = 1)
    (h1 : ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) =
      (α : V →ₗ[ZMod 2] V) - 1)
    (h2 : ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) =
      (β : V →ₗ[ZMod 2] V) - 1) :
    (α * β) ^ 3 = 1 := by
  refine pow_three_eq_one_of_braid hαα hββ (LinearEquiv.toLinearMap_injective ?_)
  change (α : V →ₗ[ZMod 2] V) * β * α = (β : V →ₗ[ZMod 2] V) * α * β
  rw [coe_eq_one_add_sub_one α, coe_eq_one_add_sub_one β]
  exact braid_of_pair end_add_self (sub_one_mul_sub_one_of_mul_self hαα)
    (sub_one_mul_sub_one_of_mul_self hββ) h1 h2

theorem coe_mul_sq_of_scalar_zero {α β : V ≃ₗ[ZMod 2] V} (hαα : α * α = 1)
    (hββ : β * β = 1)
    (h1 : ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) =
      0)
    (h2 : ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) =
      0) :
    (((α * β) ^ 2 : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) =
      1 + ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) +
        ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) := by
  rw [pow_two]
  change (α : V →ₗ[ZMod 2] V) * β * ((α : V →ₗ[ZMod 2] V) * β) = _
  rw [coe_eq_one_add_sub_one α, coe_eq_one_add_sub_one β, add_sub_cancel_left,
    add_sub_cancel_left]
  exact sq_of_pair end_add_self (sub_one_mul_sub_one_of_mul_self hαα)
    (sub_one_mul_sub_one_of_mul_self hββ) h1 h2

theorem mul_pow_four_eq_one_of_scalar_zero {α β : V ≃ₗ[ZMod 2] V} (hαα : α * α = 1)
    (hββ : β * β = 1)
    (h1 : ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) =
      0)
    (h2 : ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) =
      0) :
    (α * β) ^ 4 = 1 := by
  have h := coe_mul_sq_of_scalar_zero hαα hββ h1 h2
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
  apply LinearEquiv.toLinearMap_injective
  rw [LinearEquiv.coe_toLinearMap_mul, h]
  exact sq_sq_of_pair end_add_self (sub_one_mul_sub_one_of_mul_self hαα)
    (sub_one_mul_sub_one_of_mul_self hββ) h1 h2

theorem sub_one_apply_sub_one_apply_eq_zero [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hαO : α ∈ orthogonalGroup q)
    (horth : ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar q a b = 0) (v : V) :
    α (β v - v) - (β v - v) = 0 := by
  have hmem : β v - v ∈ fixSpace α := by
    rw [fixSpace_eq_orthogonal_commSpace_of_mem hq hαO, LinearMap.BilinForm.mem_orthogonal_iff]
    intro a ha
    exact horth a ha _ (sub_mem_commSpace β v)
  rw [mem_fixSpace.mp hmem, sub_self]

end OrthoF2

theorem isTypeA_mul_sq_of_scalar_zero [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2)
    (h1 : ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) =
      0)
    (h2 : ((β : V →ₗ[ZMod 2] V) - 1) * ((α : V →ₗ[ZMod 2] V) - 1) * ((β : V →ₗ[ZMod 2] V) - 1) =
      0)
    (hne : (α * β) ^ 2 ≠ 1) :
    IsTypeA q ((α * β) ^ 2) 2 ∧ commSpace ((α * β) ^ 2) ≤ commSpace α ⊔ commSpace β := by
  have hαO := mem_orthogonalGroup_of_isTypeA hα
  have hβO := mem_orthogonalGroup_of_isTypeA hβ
  have hαα := hα.2.2.1
  have hββ := hβ.2.2.1
  have hγO : (α * β) ^ 2 ∈ orthogonalGroup q := pow_mem (mul_mem hαO hβO) 2
  have hγγ : (α * β) ^ 2 * (α * β) ^ 2 = 1 := by
    rw [← pow_add]
    exact mul_pow_four_eq_one_of_scalar_zero hαα hββ h1 h2
  have hform : ∀ v, ((α * β) ^ 2) v - v =
      (α (β v - v) - (β v - v)) + (β (α v - v) - (α v - v)) := by
    intro v
    have h := LinearMap.congr_fun (coe_mul_sq_of_scalar_zero hαα hββ h1 h2) v
    rw [LinearEquiv.coe_coe] at h
    rw [h]
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, sub_one_apply]
    abel
  have hle : commSpace ((α * β) ^ 2) ≤ commSpace α ⊔ commSpace β := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    rw [hform]
    exact Submodule.add_mem_sup (sub_mem_commSpace α _) (sub_mem_commSpace β _)
  have hzero : ∀ x ∈ commSpace ((α * β) ^ 2), q x = 0 := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    rw [hform, map_add_eq, hα.2.2.2.2 _ (sub_mem_commSpace α _),
      hβ.2.2.2.2 _ (sub_mem_commSpace β _), zero_add, zero_add,
      ← polar_sub_eq_polar_sub hβO hββ]
    have h := LinearMap.congr_fun h2 v
    simp only [Module.End.mul_apply, sub_one_apply, LinearMap.zero_apply] at h
    rw [h, polar_zero_left]
  have hev := even_finrank_commSpace_of_forall_eq_zero hq hγO hγγ hzero
  have hpos := one_le_finrank_commSpace hne
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (commSpace α) (commSpace β)
  rw [hα.2.2.2.1, hβ.2.2.2.1] at hsup
  have hmono := Submodule.finrank_mono hle
  have hne4 : finrank (ZMod 2) (commSpace ((α * β) ^ 2)) ≠ 4 := by
    intro h4
    apply hne
    have heq : commSpace ((α * β) ^ 2) = commSpace α ⊔ commSpace β :=
      Submodule.eq_of_le_of_finrank_eq hle (by omega)
    have horth : ∀ a ∈ commSpace α, ∀ b ∈ commSpace β, polar q a b = 0 := by
      intro a ha b hb
      have hab := hzero (a + b) (heq ▸ Submodule.add_mem_sup ha hb)
      rwa [map_add_eq, hzero a (heq ▸ Submodule.mem_sup_left ha),
        hzero b (heq ▸ Submodule.mem_sup_right hb), zero_add, zero_add] at hab
    have horth' : ∀ b ∈ commSpace β, ∀ a ∈ commSpace α, polar q b a = 0 := fun b hb a ha => by
      rw [polar_comm]
      exact horth a ha b hb
    refine LinearEquiv.ext fun v => ?_
    have e := hform v
    rw [sub_one_apply_sub_one_apply_eq_zero hq hαO horth v,
      sub_one_apply_sub_one_apply_eq_zero hq hβO horth' v, add_zero, sub_eq_zero] at e
    exact e
  obtain ⟨r, hr⟩ := hev
  refine ⟨⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hγO v, hne, hγγ, ?_, hzero⟩,
    hle⟩
  omega

theorem aschbacher_3_7 [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2) (hβ : IsTypeA q β 2) :
    orderOf (α * β) ∈ ({1, 2, 3, 4} : Finset ℕ) ∧
      (orderOf (α * β) = 4 → IsTypeA q ((α * β) ^ 2) 2) := by
  obtain ⟨d, h1, h2⟩ := exists_pair_scalar hq hα hβ
  rcases zmod2_eq_zero_or_eq_one d with rfl | rfl
  · rw [zero_smul] at h1 h2
    have h4 := mul_pow_four_eq_one_of_scalar_zero hα.2.2.1 hβ.2.2.1 h1 h2
    have hdvd := orderOf_dvd_of_pow_eq_one h4
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf (α * β) :=
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, h4⟩).orderOf_pos
    refine ⟨?_, fun ho => (isTypeA_mul_sq_of_scalar_zero hq hα hβ h1 h2
      (pow_ne_one_of_lt_orderOf (by norm_num) (by omega))).1⟩
    set n := orderOf (α * β)
    interval_cases n <;> simp_all
  · rw [one_smul] at h1 h2
    have h3 := mul_pow_three_eq_one_of_scalar_one hα.2.2.1 hβ.2.2.1 h1 h2
    have hdvd := orderOf_dvd_of_pow_eq_one h3
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf (α * β) :=
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, h3⟩).orderOf_pos
    refine ⟨?_, fun ho => by omega⟩
    set n := orderOf (α * β)
    interval_cases n <;> simp_all

end CFSG.LargeExtraspecial
