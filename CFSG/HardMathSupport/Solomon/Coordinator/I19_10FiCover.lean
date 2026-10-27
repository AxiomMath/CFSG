module

public import CFSG.HardMathSupport.Solomon.Proving.CentralSylowCommutator
public import CFSG.HardMathSupport.Solomon.Proving.CommutatorScalar
public import CFSG.Open.GLADefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

variable {Y : Type*} [Group Y]

theorem isPGroup_center_of_pPrimeCore_eq_bot [Finite Y] {p : ℕ} (hp : p.Prime)
    (h : CFSG.Open.GLAPPrimeCore p Y = ⊥) : IsPGroup p (Subgroup.center Y) := by
  intro z
  obtain ⟨a, m, hpm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (z : Y)).ne' p hp.ne_one
  refine ⟨a, Subtype.ext ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : Y, y = (z : Y) ^ p ^ a := ⟨_, rfl⟩
  have hyc : y ∈ Subgroup.center Y := hy ▸ Subgroup.pow_mem _ z.2 _
  have hym : y ^ m = 1 := by rw [hy, ← pow_mul, ← hn, pow_orderOf_eq_one]
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hym)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hN : (Subgroup.zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnc : n ∈ Subgroup.center Y := (Subgroup.zpowers_le.2 hyc) hn
    rw [Subgroup.mem_center_iff.1 hnc g, mul_inv_cancel_right]
    exact hn
  have hle : Subgroup.zpowers y ≤ CFSG.Open.GLAPPrimeCore p Y := le_sSup ⟨hN, hcop⟩
  rw [h] at hle
  have h1 : y = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers y))
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy, h1]

theorem commutatorElement_pow_left_of_mem_center {x y : Y} (hc : ⁅x, y⁆ ∈ Subgroup.center Y)
    (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcn : ⁅x, y⁆ ^ n ∈ Subgroup.center Y := Subgroup.pow_mem _ hc n
    calc ⁅x ^ (n + 1), y⁆ = x * ⁅x ^ n, y⁆ * (y * x⁻¹ * y⁻¹) := by
          simp only [commutatorElement_def, pow_succ']
          group
      _ = ⁅x, y⁆ ^ n * (x * y * x⁻¹ * y⁻¹) := by
          rw [ih, Subgroup.mem_center_iff.1 hcn x]
          simp only [mul_assoc]
      _ = ⁅x, y⁆ ^ (n + 1) := by rw [pow_succ, commutatorElement_def]

theorem center_eq_bot_of_sylow_scalar {K : Type*} [Group K] [Finite Y]
    (hY : commutator Y = ⊤) (hZ : IsPGroup 5 (Subgroup.center Y)) (f : Y →* K)
    (hf : Function.Surjective f) (hker : f.ker = Subgroup.center Y) (S : Sylow 5 K)
    (hcomm : ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), a * b = b * a)
    (hexp : ∀ a ∈ (S : Subgroup K), a ^ 5 = 1) {g₀ : K}
    (hg₀ : ∀ s ∈ (S : Subgroup K), g₀ * s * g₀⁻¹ = s ^ 2) : Subgroup.center Y = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hkerP : IsPGroup 5 f.ker := by
    rw [hker]
    exact hZ
  have hrange : (S : Subgroup K) ≤ f.range := by
    rw [MonoidHom.range_eq_top.2 hf]
    exact le_top
  let P : Sylow 5 Y := S.comapOfKerIsPGroup f hkerP hrange
  have hP : ∀ x, x ∈ (P : Subgroup Y) ↔ f x ∈ (S : Subgroup K) := fun _ => Iff.rfl
  obtain ⟨g, rfl⟩ := hf g₀
  have hZ1 : ∀ u, f u = 1 → u ∈ Subgroup.center Y := fun u hu => by
    rw [← hker]
    exact hu
  have hz : ∀ u ∈ (P : Subgroup Y), (u ^ 2)⁻¹ * (g * u * g⁻¹) ∈ Subgroup.center Y := by
    intro u hu
    refine hZ1 _ ?_
    simp only [map_mul, map_inv, map_pow]
    rw [hg₀ _ ((hP u).1 hu), inv_mul_cancel]
  have hconj : ∀ u : Y, g * u * g⁻¹ = u ^ 2 * ((u ^ 2)⁻¹ * (g * u * g⁻¹)) := fun u =>
    (mul_inv_cancel_left _ _).symm
  have hcommP : ∀ x ∈ (P : Subgroup Y), ∀ y ∈ (P : Subgroup Y), ⁅x, y⁆ = 1 := by
    intro x hx y hy
    have hfx : f x ∈ (S : Subgroup K) := (hP x).1 hx
    have hfy : f y ∈ (S : Subgroup K) := (hP y).1 hy
    have hc : ⁅x, y⁆ ∈ Subgroup.center Y := hZ1 _ (by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ hfx _ hfy)
    have h5 : ⁅x, y⁆ ^ 5 = 1 := by
      rw [← commutatorElement_pow_left_of_mem_center hc 5, commutatorElement_eq_one_iff_mul_comm]
      have hx5 : x ^ 5 ∈ Subgroup.center Y := hZ1 _ (by rw [map_pow, hexp _ hfx])
      exact (Subgroup.mem_center_iff.1 hx5 y).symm
    exact Proving.commutatorElement_eq_one_of_conj_pow Nat.prime_five hc (hz x hx) (hz y hy)
      (hconj x) (hconj y) h5 (by decide)
  have hPP : ⁅(P : Subgroup Y), (P : Subgroup Y)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [hcommP x hx y hy]
    exact Subgroup.one_mem _
  have hle := Proving.le_commutator_sylow_of_le_center hY le_rfl hZ P
  rw [hPP] at hle
  exact le_bot_iff.1 hle

end CFSG.HardMathSupport.Solomon.Coordinator
