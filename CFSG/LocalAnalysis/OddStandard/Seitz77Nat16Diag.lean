module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Kernels

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Polynomial

variable {F : Type*} [Field F]

section Restrict

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (H : Module.End (ZMod 2) V)

theorem aeval_mul_comm (g : (ZMod 2)[X]) : H * aeval H g = aeval H g * H := by
  have := (Commute.all (X : (ZMod 2)[X]) g).map
    (aeval H : (ZMod 2)[X] →ₐ[ZMod 2] Module.End (ZMod 2) V)
  simpa using this.eq

theorem ker_aeval_invariant (g : (ZMod 2)[X]) {v : V} (hv : v ∈ LinearMap.ker (aeval H g)) :
    H v ∈ LinearMap.ker (aeval H g) := by
  rw [LinearMap.mem_ker] at hv ⊢
  calc (aeval H g) (H v) = ((aeval H g) * H) v := rfl
    _ = (H * (aeval H g)) v := by rw [aeval_mul_comm]
    _ = H ((aeval H g) v) := rfl
    _ = 0 := by rw [hv, map_zero]


theorem eq_add_of_add_add_eq_zero {a b c : V} (h : a + b + c = 0) : a = b + c := by
  calc a = a + (b + c + (b + c)) := by rw [add_self_zmod2, add_zero]
    _ = (a + b + c) + (b + c) := by abel
    _ = b + c := by rw [h, zero_add]

variable (T : Module.End (ZMod 2) V)

theorem restrict_pow_four {K : Submodule (ZMod 2) V} (hinv : ∀ v ∈ K, T v ∈ K)
    (h4 : ∀ v ∈ K, (T ^ 4) v = T v + v) : T.restrict hinv ^ 4 = T.restrict hinv + 1 := by
  rw [Module.End.pow_restrict 4 hinv]
  refine LinearMap.ext fun v => Subtype.ext ?_
  simp only [LinearMap.restrict_apply, LinearMap.add_apply, Module.End.one_apply,
    Submodule.coe_add]
  exact h4 v v.2

section Param

variable (hF : Nat.card F = 16) {ζ : F} (hζ : ζ ^ 4 = ζ + 1)

include hF hζ

theorem four_dvd_finrank {K : Submodule (ZMod 2) V} [Finite K] (hinv : ∀ v ∈ K, T v ∈ K)
    (h4 : ∀ v ∈ K, (T ^ 4) v = T v + v) : 4 ∣ Module.finrank (ZMod 2) K := by
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have := charP_two hF
  obtain ⟨ψ, hψ⟩ := exists_ringHom_zeta hF hζ (restrict_pow_four T hinv h4)
  let _ : Module F K := Module.compHom K ψ
  have hfin : Module.Finite F K := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := F) (V := K)
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [Nat.card_zmod] at h2
  rw [hF] at h1
  have h3 : 2 ^ Module.finrank (ZMod 2) K = 2 ^ (4 * Module.finrank F K) := by
    rw [← h2, h1, pow_mul]
    norm_num
  exact ⟨_, Nat.pow_right_injective (le_refl 2) h3⟩

theorem exists_param {K : Submodule (ZMod 2) V} (hinv : ∀ v ∈ K, T v ∈ K)
    (h4 : ∀ v ∈ K, (T ^ 4) v = T v + v) (hK : Nat.card K = 16) :
    ∃ Θ : F ≃+ K, ∀ x, ((Θ (ζ * x) : K) : V) = T ((Θ x : K) : V) := by
  obtain ⟨ψ, hψ⟩ := exists_ringHom_zeta hF hζ (restrict_pow_four T hinv h4)
  obtain ⟨Θ, hΘ⟩ := exists_addEquiv hF ψ hK
  refine ⟨Θ, fun x => ?_⟩
  rw [hΘ, hψ]
  rfl

end Param

section Main

variable [Module.Finite (ZMod 2) V] (hF : Nat.card F = 16) {ζ : F} (hζ : ζ ^ 4 = ζ + 1)

include hF hζ

theorem exists_diagonalizing (hV : Module.finrank (ZMod 2) V = 8)
    (R : Module.End (ZMod 2) V) (hH15 : H ^ 15 = 1) (hH3 : H ^ 3 ≠ 1)
    (hR2 : R * R = 1) (hRH : R * H = H ^ 14 * R) (hfpf : ∀ v, (H ^ 5) v = v → v = 0) :
    ∃ Θ : (F × F) ≃+ V, ∀ x y, H (Θ (x, y)) = Θ (ζ * x, ζ⁻¹ * y) := by
  have hVfin : Finite V := Module.finite_of_finite (ZMod 2)
  have h10 := pow_ten H hH15 hfpf
  have hsum := finrank_sum H hV h10
  have hbc := finrank_K1_eq_K7 H R hH15 hR2 hRH
  have hinv1 : ∀ v ∈ LinearMap.ker (aeval H g1), H v ∈ LinearMap.ker (aeval H g1) :=
    fun v hv => ker_aeval_invariant H g1 hv
  have hinv7 : ∀ v ∈ LinearMap.ker (aeval H g7), H v ∈ LinearMap.ker (aeval H g7) :=
    fun v hv => ker_aeval_invariant H g7 hv
  have h4_1 : ∀ v ∈ LinearMap.ker (aeval H g1), (H ^ 4) v = H v + v := by
    intro v hv
    rw [LinearMap.mem_ker, aeval_g1_eq] at hv
    simp only [LinearMap.add_apply, Module.End.one_apply] at hv
    exact eq_add_of_add_add_eq_zero hv
  have hdiv := four_dvd_finrank H hF hζ hinv1 h4_1
  have hb0 : Module.finrank (ZMod 2) (LinearMap.ker (aeval H g1)) ≠ 0 := by
    intro hb
    have hc0 : Module.finrank (ZMod 2) (LinearMap.ker (aeval H g7)) = 0 := by omega
    have ha8 : Module.finrank (ZMod 2) (LinearMap.ker (aeval H g5)) = 8 := by omega
    have htop : LinearMap.ker (aeval H g5) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [ha8, hV])
    have h5 : H ^ 2 + H + 1 = 0 := by
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ LinearMap.ker (aeval H g5) := by rw [htop]; trivial
      rwa [LinearMap.mem_ker, aeval_g5_eq] at hv
    apply hH3
    have : (H - 1) * (H ^ 2 + H + 1) = H ^ 3 - 1 := by noncomm_ring
    rw [h5, mul_zero] at this
    exact (sub_eq_zero.1 this.symm)
  obtain ⟨k, hk⟩ := hdiv
  have hb4 : Module.finrank (ZMod 2) (LinearMap.ker (aeval H g1)) = 4 := by omega
  have hc4 : Module.finrank (ZMod 2) (LinearMap.ker (aeval H g7)) = 4 := by omega
  have ha0 : Module.finrank (ZMod 2) (LinearMap.ker (aeval H g5)) = 0 := by omega
  have hK5 : LinearMap.ker (aeval H g5) = ⊥ := Submodule.finrank_eq_zero.1 ha0
  have hsup : LinearMap.ker (aeval H g1) ⊔ LinearMap.ker (aeval H g7) = ⊤ := by
    have := ker_sup_eq_top H h10
    rwa [hK5, bot_sup_eq] at this
  have hcompl : IsCompl (LinearMap.ker (aeval H g1)) (LinearMap.ker (aeval H g7)) :=
    ⟨disjoint_ker_g1_g7 H, codisjoint_iff.2 hsup⟩
  have hK1 : Nat.card (LinearMap.ker (aeval H g1)) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hb4, Nat.card_zmod]; norm_num
  have hK7 : Nat.card (LinearMap.ker (aeval H g7)) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hc4, Nat.card_zmod]; norm_num
  have h14pow : (H ^ 14) ^ 4 = H ^ 11 := by
    rw [← pow_mul, show 14 * 4 = 15 * 3 + 11 from rfl, pow_add, pow_mul, hH15, one_pow, one_mul]
  have hinv7' : ∀ v ∈ LinearMap.ker (aeval H g7), (H ^ 14) v ∈ LinearMap.ker (aeval H g7) := by
    intro v hv
    have hall : ∀ n : ℕ, (H ^ n) v ∈ LinearMap.ker (aeval H g7) := by
      intro n
      induction n with
      | zero => simpa using hv
      | succ n ih =>
        rw [pow_succ']
        exact hinv7 _ ih
    exact hall 14
  have h4_7 : ∀ v ∈ LinearMap.ker (aeval H g7), ((H ^ 14) ^ 4) v = (H ^ 14) v + v := by
    intro v hv
    rw [LinearMap.mem_ker, aeval_g7_eq] at hv
    have h1 : (H ^ 11 * (H ^ 4 + H ^ 3 + 1) : Module.End (ZMod 2) V) = 1 + H ^ 14 + H ^ 11 := by
      rw [mul_add, mul_add, ← pow_add, ← pow_add, mul_one, show 11 + 4 = 15 from rfl, hH15,
        show 11 + 3 = 14 from rfl]
    have h2 := congrArg (fun w => (H ^ 11) w) hv
    simp only [map_zero] at h2
    rw [← Module.End.mul_apply, h1] at h2
    simp only [LinearMap.add_apply, Module.End.one_apply] at h2
    rw [h14pow]
    exact eq_add_of_add_add_eq_zero (by rw [← h2]; abel)
  obtain ⟨Θ₁, hΘ₁⟩ := exists_param H hF hζ hinv1 h4_1 hK1
  obtain ⟨Θ₇, hΘ₇⟩ := exists_param (H ^ 14) hF hζ hinv7' h4_7 hK7
  let Θ : (F × F) ≃+ V :=
    (Θ₁.prodCongr Θ₇).trans (Submodule.prodEquivOfIsCompl _ _ hcompl).toAddEquiv
  have hΘ : ∀ x y, Θ (x, y) = ((Θ₁ x : LinearMap.ker (aeval H g1)) : V) +
      ((Θ₇ y : LinearMap.ker (aeval H g7)) : V) := fun x y => rfl
  refine ⟨Θ, fun x y => ?_⟩
  rw [hΘ, hΘ, map_add, ← hΘ₁]
  congr 1
  have h1 := hΘ₇ (ζ⁻¹ * y)
  rw [mul_inv_cancel_left₀ (zeta_ne_zero hζ)] at h1
  rw [h1]
  calc H ((H ^ 14) ((Θ₇ (ζ⁻¹ * y) : LinearMap.ker (aeval H g7)) : V)) =
      (H ^ 15) ((Θ₇ (ζ⁻¹ * y) : LinearMap.ker (aeval H g7)) : V) := by
        rw [← Module.End.mul_apply, ← pow_succ']
    _ = _ := by rw [hH15]; rfl

end Main

end Restrict


end Nat16

end CFSG.OddStandard.Seitz77
