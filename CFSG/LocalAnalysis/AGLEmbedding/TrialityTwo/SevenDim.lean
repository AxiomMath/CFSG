module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenOrth
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {t : Module.End K V}

section Two

theorem eq_zero_or_eq_one_of_card (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  rcases eq_or_ne c 0 with h | h
  · exact .inl h
  · right
    have h1 := FiniteField.pow_card_sub_one_eq_one c h
    rwa [← Nat.card_eq_fintype_card, hK, show 2 - 1 = 1 from rfl, pow_one] at h1

theorem two_eq_zero_of_card (hK : Nat.card K = 2) : (2 : K) = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rwa [← Nat.card_eq_fintype_card, hK, Nat.cast_ofNat] at h

end Two

theorem two_pow_mod_seven (a : ℕ) : 2 ^ a % 7 = 2 ^ (a % 3) % 7 := by
  conv_lhs => rw [← Nat.div_add_mod a 3, pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

theorem mod_three_eq_of_two_pow_modEq {a b : ℕ} (h : 2 ^ a ≡ 2 ^ b [MOD 7]) :
    a % 3 = b % 3 := by
  unfold Nat.ModEq at h
  rw [two_pow_mod_seven a, two_pow_mod_seven b] at h
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb] at h ⊢ <;>
    norm_num at h

theorem two_pow_finrank_modEq [FiniteDimensional K V] (hK : Nat.card K = 2) (h7 : t ^ 7 = 1)
    (S : Submodule K V) (hS : ∀ x ∈ S, t x ∈ S) :
    2 ^ finrank K S ≡ 2 ^ finrank K ↥(S ⊓ fixC t) [MOD 7] := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Finite S := Module.finite_of_finite K
  let _ : Fintype S := Fintype.ofFinite S
  let f : Function.End S := fun x => ⟨t x, hS x x.2⟩
  have hpow : ∀ (n : ℕ) (x : S), ((f ^ n) x : V) = (t ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ]; exact ih (f x)
  have hf : f ^ 7 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [pow_one, hpow, h7]
    rfl
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc := Equiv.Perm.card_fixedPoints_modEq (p := 7) (n := 1) hf
  let e : Function.fixedPoints f ≃ ↥(S ⊓ fixC t) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, (mem_fixC_iff).2 (congrArg Subtype.val x.2)⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subtype.ext ((mem_fixC_iff).1 y.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Nat.card_congr e,
    Module.natCard_eq_pow_finrank (K := K) (V := S),
    Module.natCard_eq_pow_finrank (K := K) (V := ↥(S ⊓ fixC t)), hK] at hc
  exact hc

section Dims

variable [FiniteDimensional K V] (h7 : t ^ 7 = 1) (h2 : (2 : K) = 0)
include h7 h2

theorem finrank_fixC_add_finrank_spU₁_add_finrank_spU₂ :
    finrank K (fixC t) + finrank K (spU₁ t) + finrank K (spU₂ t) = finrank K V := by
  have hd1 : fixC t ⊓ spU₁ t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot K).2 (eq_zero_of_mem_spU₁_of_mem_fixC h7 h2 hx.2 hx.1)
  have hd2 : (fixC t ⊔ spU₁ t) ⊓ spU₂ t = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx₂⟩
    obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
    have h := (mem_spU₂_iff h7 h2).1 hx₂
    rw [map_add, projU₂_apply_of_mem_fixC h7 h2 hc, projU₂_apply_of_mem_spU₁ h7 h2 hu,
      add_zero] at h
    exact (Submodule.mem_bot K).2 h.symm
  have htop : fixC t ⊔ spU₁ t ⊔ spU₂ t = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← projC_add_projU₁_add_projU₂_apply h7 h2 x]
    exact add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left
      (projC_apply_mem_fixC h7 h2 x))) (Submodule.mem_sup_left (Submodule.mem_sup_right
        (projU₁_apply_mem x)))) (Submodule.mem_sup_right (projU₂_apply_mem x))
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (fixC t) (spU₁ t)
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq (fixC t ⊔ spU₁ t) (spU₂ t)
  rw [hd1, finrank_bot, add_zero] at e1
  rw [hd2, finrank_bot, add_zero, htop, finrank_top, e1] at e2
  exact e2.symm

variable (hQt : ∀ v, Q (t v) = Q v) (hB : (polarBilin Q).Nondegenerate)
include hQt hB

theorem finrank_spU₁_eq_finrank_spU₂ : finrank K (spU₁ t) = finrank K (spU₂ t) := by
  apply le_antisymm
  · have hinj : Function.Injective ((polarBilin Q).domRestrict₁₂ (spU₁ t) (spU₂ t)) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      refine (Submodule.mem_bot K).2 (Subtype.ext ?_)
      refine eq_zero_of_mem_spU₁_of_polar hQt h7 h2 hB x.2 fun y hy => ?_
      have := LinearMap.congr_fun hx ⟨y, hy⟩
      simpa [LinearMap.domRestrict₁₂_apply, polarBilin_apply_apply] using this
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Subspace.dual_finrank_eq] at h
  · have hinj : Function.Injective ((polarBilin Q).domRestrict₁₂ (spU₂ t) (spU₁ t)) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      refine (Submodule.mem_bot K).2 (Subtype.ext ?_)
      refine eq_zero_of_mem_spU₂_of_polar hQt h7 h2 hB x.2 fun y hy => ?_
      have := LinearMap.congr_fun hx ⟨y, hy⟩
      simpa [LinearMap.domRestrict₁₂_apply, polarBilin_apply_apply] using this
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Subspace.dual_finrank_eq] at h

end Dims

section Dims8

variable [FiniteDimensional K V] (hK : Nat.card K = 2) (h7 : t ^ 7 = 1) (ht : t ≠ 1)
  (hQt : ∀ v, Q (t v) = Q v) (hB : (polarBilin Q).Nondegenerate) (hV : finrank K V = 8)
include hK h7 ht hQt hB hV

theorem finrank_fixC_eq_two : finrank K (fixC t) = 2 := by
  have h2 := two_eq_zero_of_card hK
  have hc := two_pow_finrank_modEq hK h7 ⊤ fun x _ => Submodule.mem_top
  rw [finrank_top, hV, top_inf_eq] at hc
  have h3 := mod_three_eq_of_two_pow_modEq hc
  have hsum := finrank_fixC_add_finrank_spU₁_add_finrank_spU₂ h7 h2
  rw [← finrank_spU₁_eq_finrank_spU₂ h7 h2 hQt hB, hV] at hsum
  have hne : finrank K (fixC t) ≠ 8 := by
    intro h8
    have htop : fixC t = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h8, hV])
    apply ht
    ext x
    have hx : x ∈ fixC t := htop ▸ Submodule.mem_top
    rw [(mem_fixC_iff).1 hx, Module.End.one_apply]
  omega

theorem finrank_spU₁_eq_three : finrank K (spU₁ t) = 3 := by
  have h2 := two_eq_zero_of_card hK
  have hsum := finrank_fixC_add_finrank_spU₁_add_finrank_spU₂ h7 h2
  rw [← finrank_spU₁_eq_finrank_spU₂ h7 h2 hQt hB, hV,
    finrank_fixC_eq_two hK h7 ht hQt hB hV] at hsum
  omega

theorem finrank_spU₂_eq_three : finrank K (spU₂ t) = 3 := by
  rw [← finrank_spU₁_eq_finrank_spU₂ h7 (two_eq_zero_of_card hK) hQt hB]
  exact finrank_spU₁_eq_three hK h7 ht hQt hB hV

theorem eq_bot_or_eq_of_le_spU₁ {S : Submodule K V} (hS : ∀ x ∈ S, t x ∈ S)
    (hSU : S ≤ spU₁ t) : S = ⊥ ∨ S = spU₁ t := by
  have h2 := two_eq_zero_of_card hK
  have hc := two_pow_finrank_modEq hK h7 S hS
  have hinf : S ⊓ fixC t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot K).2 (eq_zero_of_mem_spU₁_of_mem_fixC h7 h2 (hSU hx.1) hx.2)
  rw [hinf, finrank_bot] at hc
  have h3 := mod_three_eq_of_two_pow_modEq hc
  have hle := Submodule.finrank_mono hSU
  rw [finrank_spU₁_eq_three hK h7 ht hQt hB hV] at hle
  rcases (show finrank K S = 0 ∨ finrank K S = 3 by omega) with h | h
  · exact .inl (Submodule.finrank_eq_zero.1 h)
  · exact .inr (Submodule.eq_of_le_of_finrank_eq hSU
      (by rw [h, finrank_spU₁_eq_three hK h7 ht hQt hB hV]))

theorem eq_bot_or_eq_of_le_spU₂ {S : Submodule K V} (hS : ∀ x ∈ S, t x ∈ S)
    (hSU : S ≤ spU₂ t) : S = ⊥ ∨ S = spU₂ t := by
  have h2 := two_eq_zero_of_card hK
  have hc := two_pow_finrank_modEq hK h7 S hS
  have hinf : S ⊓ fixC t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot K).2 (eq_zero_of_mem_spU₂_of_mem_fixC h7 h2 (hSU hx.1) hx.2)
  rw [hinf, finrank_bot] at hc
  have h3 := mod_three_eq_of_two_pow_modEq hc
  have hle := Submodule.finrank_mono hSU
  rw [finrank_spU₂_eq_three hK h7 ht hQt hB hV] at hle
  rcases (show finrank K S = 0 ∨ finrank K S = 3 by omega) with h | h
  · exact .inl (Submodule.finrank_eq_zero.1 h)
  · exact .inr (Submodule.eq_of_le_of_finrank_eq hSU
      (by rw [h, finrank_spU₂_eq_three hK h7 ht hQt hB hV]))

end Dims8

end CFSG.AGLEmbedding.TrialityTwo.Seven
