module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

open scoped IsMulCommutative

private def conjFun {G : Type*} [Group G] (Y : Subgroup G) (x : G)
    (hx : x ∈ normalizer (Y : Set G)) (v : Additive Y) : Additive Y :=
  Additive.ofMul ⟨x * (Additive.toMul v) * x⁻¹,
    (Subgroup.mem_normalizer_iff.mp hx _).mp (Additive.toMul v).2⟩

private lemma conjFun_zero {G : Type*} [Group G] (Y : Subgroup G) (x : G)
    (hx : x ∈ normalizer (Y : Set G)) : conjFun Y x hx 0 = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp [conjFun]

private lemma conjFun_add {G : Type*} [Group G] (Y : Subgroup G) (x : G)
    (hx : x ∈ normalizer (Y : Set G)) (a b : Additive Y) :
    conjFun Y x hx (a + b) = conjFun Y x hx a + conjFun Y x hx b := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [conjFun, toMul_add, toMul_ofMul, Subgroup.coe_mul]
  group

private def conjAddHom {G : Type*} [Group G] (Y : Subgroup G) (x : G)
    (hx : x ∈ normalizer (Y : Set G)) : Additive Y →+ Additive Y where
  toFun := conjFun Y x hx
  map_zero' := conjFun_zero Y x hx
  map_add' := conjFun_add Y x hx

theorem pow_four_centralizes {G : Type*} [Group G] {Y : Subgroup G}
    (hY : CFSG.Open.IsElemAbelian 2 Y) (hcard : Nat.card Y = 16) {x : G}
    (hx : x ∈ normalizer (Y : Set G)) (h2 : ∃ k : ℕ, x ^ (2 ^ k) = 1) :
    ∀ y ∈ Y, x ^ 4 * y * (x ^ 4)⁻¹ = y := by
  classical
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype Y := Fintype.ofFinite Y
  haveI : Nontrivial Y :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  haveI : Nontrivial (Additive Y) := inferInstance
  haveI : Finite (Additive Y) := inferInstance
  haveI : IsMulCommutative Y := hY.1
  letI : Module (ZMod 2) (Additive Y) :=
    AddCommGroup.zmodModule (n := 2) (fun v => by
      apply Additive.toMul.injective
      rw [two_nsmul, toMul_add, toMul_zero]
      apply Subtype.ext
      simpa [pow_two] using hY.2 ((Additive.toMul v : Y) : G) (Additive.toMul v).2)
  haveI : FiniteDimensional (ZMod 2) (Additive Y) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod 2) (Additive Y) = 4 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Y)
    have hYcard : Nat.card (Additive Y) = 16 := by
      rw [(Nat.card_congr Additive.ofMul).symm, hcard]
    rw [hYcard, Nat.card_eq_fintype_card, ZMod.card] at hc
    have hpow : 2 ^ Module.finrank (ZMod 2) (Additive Y) = 2 ^ 4 := by
      rw [← hc]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  let F : Additive Y →ₗ[ZMod 2] Additive Y :=
    AddMonoidHom.toZModLinearMap 2 (conjAddHom Y x hx)
  have hF_apply : ∀ w : Additive Y, ((F w).toMul : G) = x * (w.toMul : G) * x⁻¹ := by
    intro w
    rfl
  have hFpow : ∀ m : ℕ, ∀ w : Additive Y,
      (((F ^ m) w).toMul : G) = x ^ m * (w.toMul : G) * (x ^ m)⁻¹ := by
    intro m
    induction m with
    | zero =>
        intro w
        simp
    | succ m ih =>
        intro w
        rw [pow_succ, Module.End.mul_apply]
        rw [ih (F w), hF_apply w]
        group
  obtain ⟨k, hk⟩ := h2
  have hFpowk : F ^ (2 ^ k) = 1 := by
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hFpow (2 ^ k) w, hk]
    simp
  haveI : CharP (Module.End (ZMod 2) (Additive Y)) 2 :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) (Module.End (ZMod 2) (Additive Y))) 2
      (by norm_num)
  let T : Module.End (ZMod 2) (Additive Y) := F - 1
  have hTnil : T ^ (2 ^ k) = 0 := by
    have hcomm : Commute F (1 : Module.End (ZMod 2) (Additive Y)) := Commute.one_right F
    rw [show T = F - 1 from rfl, sub_pow_char_pow_of_commute 2 k hcomm, hFpowk, one_pow,
      sub_self]
  have hT4 : T ^ 4 = 0 := by
    have h1 : LinearMap.ker (T ^ (2 ^ k)) = ⊤ := by rw [hTnil]; simp
    have hle := Module.End.ker_pow_le_ker_pow_finrank (K := ZMod 2) (V := Additive Y) T (2 ^ k)
    have hker : LinearMap.ker (T ^ Module.finrank (ZMod 2) (Additive Y)) = ⊤ :=
      top_le_iff.mp (h1 ▸ hle)
    rw [hfin] at hker
    exact LinearMap.ext fun w => by
      have hw : w ∈ LinearMap.ker (T ^ 4) := by rw [hker]; exact Submodule.mem_top
      simpa using hw
  have hF4 : F ^ 4 = 1 := by
    have hFT : F = T + 1 := by
      rw [show T = F - 1 from rfl, sub_add_cancel]
    rw [hFT]
    change (T + 1) ^ (2 ^ 2) = 1
    rw [add_pow_char_pow_of_commute 2 2 (Commute.one_right T)]
    change T ^ 4 + 1 ^ 4 = 1
    rw [hT4, one_pow, zero_add]
  intro y hy
  have h1 : (F ^ 4) (Additive.ofMul (⟨y, hy⟩ : Y)) = Additive.ofMul (⟨y, hy⟩ : Y) := by
    rw [hF4]; rfl
  have h2 : (((F ^ 4) (Additive.ofMul (⟨y, hy⟩ : Y))).toMul : G)
      = ((Additive.ofMul (⟨y, hy⟩ : Y)).toMul : G) :=
    congrArg (fun z : Additive Y => (z.toMul : G)) h1
  rw [hFpow 4 (Additive.ofMul (⟨y, hy⟩ : Y))] at h2
  simpa using h2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
