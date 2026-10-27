module

public import CFSG.ClassicalInvolution.SmallOrth.Iwasawa
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_pow_three (h3 : (3 : K) = 0) (u w : V) : eichler Q u w ^ 3 = 1 := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hw2 : polar Q u (w + w) = 0 := by rw [polar_add_right, h.2, add_zero]
    rw [pow_succ, pow_two, eichler_mul h.2 h.2, eichler_mul hw2 h.2,
      show w + w + w = (3 : K) • w by module, h3, zero_smul, eichler_zero_right]
  · rw [eichler_of_not h, one_pow]

section Weyl

variable (P : HypPair Q)

theorem weyl_one_mul_self (h2 : (2 : K) ≠ 0) {a : V} (ha : a ∈ P.perp) (hc : Q a ≠ 0) :
    weyl Q P a 1 (Q a)⁻¹ * weyl Q P a 1 (Q a)⁻¹ = 1 := by
  have h : Q a * 1 * (Q a)⁻¹ = 1 := by rw [mul_one, mul_inv_cancel₀ hc]
  set W := weyl Q P a 1 (Q a)⁻¹ with hW
  have hWe : W P.e = (-((Q a)⁻¹ ^ 2 * Q a)) • P.f := weyl_apply_e P ha h
  have hWf : W P.f = (-(1 ^ 2 * Q a)) • P.e := weyl_apply_f P ha h
  have hWa : W a = -a := weyl_apply_a P ha h
  have hWee : W (W P.e) = P.e := by
    rw [hWe, map_smul, hWf, smul_smul]
    have : -((Q a)⁻¹ ^ 2 * Q a) * -(1 ^ 2 * Q a) = 1 := by field_simp
    rw [this, one_smul]
  have hWff : W (W P.f) = P.f := by
    rw [hWf, map_smul, hWe, smul_smul]
    have : -(1 ^ 2 * Q a) * -((Q a)⁻¹ ^ 2 * Q a) = 1 := by field_simp
    rw [this, one_smul]
  have hperp : ∀ y ∈ P.perp, W (W y) = y := by
    intro y hy
    set α : K := polar Q y a / (2 * Q a) with hα
    set z : V := y - α • a with hz
    have hzP : z ∈ P.perp := P.perp.sub_mem hy (P.perp.smul_mem _ ha)
    have hza : polar Q z a = 0 := by
      rw [hz, polar_sub_left, polar_smul_left_eq, polar_self_eq_two_mul, hα]
      field_simp
      ring
    have hy' : y = α • a + z := by rw [hz]; abel
    have hWz : W z = z := weyl_apply_of_perp P hzP hza 1 (Q a)⁻¹
    rw [hy', map_add, map_smul, hWa, hWz, map_add, map_smul, map_neg, hWa, hWz, neg_neg]
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, P.eq_add_proj x]
  simp only [map_add, map_smul, hWee, hWff, hperp _ (P.proj_mem_perp x)]
  rfl

theorem weyl_one_ne_one {a : V} (ha : a ∈ P.perp) (hc : Q a ≠ 0) :
    weyl Q P a 1 (Q a)⁻¹ ≠ 1 := by
  have h : Q a * 1 * (Q a)⁻¹ = 1 := by rw [mul_one, mul_inv_cancel₀ hc]
  intro h1
  have hWe := weyl_apply_e P ha h
  rw [h1] at hWe
  have h3 := congrArg (polar Q P.e) hWe
  change polar Q P.e P.e = polar Q P.e _ at h3
  rw [polar_smul_right_eq, P.polar_ee, P.polar_ef, mul_one] at h3
  have : (Q a)⁻¹ ^ 2 * Q a = 0 := by linear_combination h3
  exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hc)) hc this

end Weyl

theorem eq_one_of_forall_smul_eq (P : HypPair Q) (hA : HasAnisoPerp Q)
    (N : Subgroup (elementaryGroup Q))
    (hfix : MulAction.fixedPoints N (singularLines Q) = Set.univ) (hodd : Odd (Nat.card N))
    {n : elementaryGroup Q} (hn : n ∈ N) : n = 1 := by
  obtain ⟨a, ha, hc⟩ := hA P
  have hscal : (n : V ≃ₗ[K] V) ∈ scalars K V :=
    mem_scalars_of_forall_singular_small P ha hc (elementaryGroup_le_orthogonalGroup Q n.2)
      (fun v hv0 hv => by
        have hx : lineMk v hv0 hv ∈ MulAction.fixedPoints N (singularLines Q) :=
          hfix ▸ Set.mem_univ _
        have h1 : n • lineMk v hv0 hv = lineMk v hv0 hv := hx ⟨n, hn⟩
        rw [smul_lineMk, lineMk_eq_lineMk_iff] at h1
        obtain ⟨c, hc⟩ := h1
        exact ⟨c, hc.symm⟩)
  have hsq : (n : V ≃ₗ[K] V) * n = 1 :=
    mul_self_eq_one_of_mem_scalars (elementaryGroup_le_orthogonalGroup Q n.2) hscal hc
  set m : N := ⟨n, hn⟩ with hm
  have hm2 : m ^ 2 = 1 := Subtype.ext (Subtype.ext (by simpa [pow_two] using hsq))
  have h1 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one hm2
  have h2 : Odd (orderOf m) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard m)
  have h3 : orderOf m = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 (by decide)
  have : m = 1 := orderOf_eq_one_iff.mp h3
  exact congrArg Subtype.val this

theorem eq_bot_of_odd_normal (h3 : (3 : K) = 0) (h2 : (2 : K) ≠ 0)
    (hA : HasAnisoPerp Q) (P : HypPair Q)
    (hprim : MulAction.IsPreprimitive (elementaryGroup Q) (singularLines Q))
    (N : Subgroup (elementaryGroup Q)) [hN : N.Normal] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  by_cases hfix : MulAction.fixedPoints N (singularLines Q) = Set.univ
  · exact eq_one_of_forall_smul_eq P hA N hfix hodd hn
  exfalso
  have hle : commutator (elementaryGroup Q) ≤ N := commutator_le_of_not_fixed N hfix
  obtain ⟨a, ha, hc⟩ := hA P
  let W : elementaryGroup Q := ⟨weyl Q P a 1 (Q a)⁻¹, weyl_mem P a _ _⟩
  have hW2 : W * W = 1 := Subtype.ext (weyl_one_mul_self P h2 ha hc)
  have hW1 : W ≠ 1 := fun h => weyl_one_ne_one P ha hc (congrArg Subtype.val h)
  set π := QuotientGroup.mk' N with hπ
  have hcomm : ∀ x y : elementaryGroup Q ⧸ N, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | H g => ?_
    induction y using QuotientGroup.induction_on with | H h => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have : (g * h)⁻¹ * (h * g) = ⁅h⁻¹, g⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hcube : ∀ g : elementaryGroup Q, (π g) ^ 3 = 1 := by
    let S : Subgroup (elementaryGroup Q) :=
      { carrier := {g | (π g) ^ 3 = 1}
        mul_mem' := fun {x y} hx hy => by
          have hx' : (π x) ^ 3 = 1 := hx
          have hy' : (π y) ^ 3 = 1 := hy
          show (π (x * y)) ^ 3 = 1
          rw [map_mul, (show Commute (π x) (π y) from hcomm _ _).mul_pow, hx', hy', one_mul]
        one_mem' := by
          show (π 1) ^ 3 = 1
          rw [map_one, one_pow]
        inv_mem' := fun {x} hx => by
          have hx' : (π x) ^ 3 = 1 := hx
          show (π x⁻¹) ^ 3 = 1
          rw [map_inv, inv_pow, hx', inv_one] }
    have hle' : elementaryGroup Q ≤ S.map (elementaryGroup Q).subtype := by
      apply elementaryGroup_le_of_eichler_mem
      intro u w hu hw
      refine ⟨⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩, ?_, rfl⟩
      show (π ⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩) ^ 3 = 1
      have : (⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩ : elementaryGroup Q) ^ 3 = 1 :=
        Subtype.ext (eichler_pow_three h3 u w)
      rw [← map_pow, this, map_one]
    intro g
    obtain ⟨t, ht, htg⟩ := hle' g.2
    have : t = g := Subtype.ext htg
    rw [← this]
    exact ht
  have hπW : π W = 1 := by
    have h3' := hcube W
    have h2' : (π W) ^ 2 = 1 := by rw [pow_two, ← map_mul, hW2, map_one]
    calc π W = (π W) ^ 3 * ((π W) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h2', inv_one, one_mul]
  have hWN : W ∈ N := (QuotientGroup.eq_one_iff W).mp hπW
  set m : N := ⟨W, hWN⟩ with hm
  have hm2 : orderOf m = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (Subtype.ext (by simpa [pow_two] using congrArg Subtype.val hW2))
    · intro h
      exact hW1 (congrArg Subtype.val h)
  have h4 : orderOf m ∣ Nat.card N := orderOf_dvd_natCard m
  rw [hm2] at h4
  exact absurd (Odd.of_dvd_nat hodd h4) (by decide)

end CFSG.ClassicalGroups.Orthogonal.Small
