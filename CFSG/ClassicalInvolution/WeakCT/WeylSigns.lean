module

public import CFSG.Timmesfeld.RankTwo.LevisExtras

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open scoped commutatorElement MatrixGroups

section SL2

variable {F : Type} [Field F]

@[expose] def wS (t : Fˣ) : SL(2, F) :=
  Steinberg.sl2Upper (t : F) * Steinberg.sl2Lower (-((t⁻¹ : Fˣ) : F)) * Steinberg.sl2Upper (t : F)

theorem coe_sl2Upper (c : F) :
    ((Steinberg.sl2Upper c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := rfl

theorem coe_sl2Lower (c : F) :
    ((Steinberg.sl2Lower c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := rfl

theorem wS_one_mul_wS_neg_one : wS (1 : Fˣ) * wS (-1 : Fˣ) = (1 : SL(2, F)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, wS,
    coe_sl2Upper, coe_sl2Lower, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem wS_one_mul_upper (u : F) :
    wS (1 : Fˣ) * Steinberg.sl2Upper u = Steinberg.sl2Lower (-u) * wS (1 : Fˣ) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, wS, coe_sl2Upper, coe_sl2Lower,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem eq_one_or_eq_sq_of_mem_center {a : SL(2, F)} (ha : a ∈ Subgroup.center SL(2, F)) :
    a = 1 ∨ a = wS (1 : Fˣ) * wS (1 : Fˣ) := by
  obtain ⟨r, hr, hra⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 ha
  rw [Fintype.card_fin] at hr
  have h : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.1 h with h | h
  · left
    have h1 : r = 1 := sub_eq_zero.1 h
    subst h1
    apply Subtype.ext
    rw [← hra]
    simp
  · right
    have h1 : r = -1 := eq_neg_of_add_eq_zero_left h
    subst h1
    apply Subtype.ext
    rw [← hra]
    simp only [Matrix.SpecialLinearGroup.coe_mul, wS, coe_sl2Upper, coe_sl2Lower,
      Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end SL2

section Weyl

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem weylElement_eq_map {φ : SL(2, F) →* K} {i : Fin D.rank}
    (hup : ∀ c, φ (Steinberg.sl2Upper c) = x (Pi.single i 1) c)
    (hlow : ∀ c, φ (Steinberg.sl2Lower c) = x (-Pi.single i 1) c) (t : Fˣ) :
    Steinberg.weylElement x i t = φ (wS t) := by
  simp only [Steinberg.weylElement, wS, map_mul, hup, hlow]

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem weylElement_one_mul_neg_one (i : Fin D.rank) :
    Steinberg.weylElement x i 1 * Steinberg.weylElement x i (-1) = 1 := by
  obtain ⟨φ, -, hup, hlow⟩ := hE.rankOne i
  rw [weylElement_eq_map hup hlow, weylElement_eq_map hup hlow, ← map_mul,
    wS_one_mul_wS_neg_one, map_one]

theorem weylElement_one_conj_single (i : Fin D.rank) (u : F) :
    Steinberg.weylElement x i 1 * x (Pi.single i 1) u * (Steinberg.weylElement x i 1)⁻¹ =
      x (-Pi.single i 1) (-u) := by
  obtain ⟨φ, -, hup, hlow⟩ := hE.rankOne i
  have h : wS (1 : Fˣ) * Steinberg.sl2Upper u * (wS (1 : Fˣ))⁻¹ = Steinberg.sl2Lower (-u) :=
    mul_inv_eq_iff_eq_mul.2 (wS_one_mul_upper u)
  have h' := congrArg φ h
  rw [map_mul, map_mul, map_inv, hup, hlow] at h'
  rwa [weylElement_eq_map hup hlow]

theorem weylElement_one_sq (i : Fin D.rank) :
    ∃ φ : SL(2, F) →* K, Function.Injective φ ∧
      (∀ c, φ (Steinberg.sl2Upper c) = x (Pi.single i 1) c) ∧
      (∀ c, φ (Steinberg.sl2Lower c) = x (-Pi.single i 1) c) ∧
      Steinberg.weylElement x i 1 ^ 2 = φ (wS (1 : Fˣ) * wS (1 : Fˣ)) := by
  obtain ⟨φ, hφ, hup, hlow⟩ := hE.rankOne i
  refine ⟨φ, hφ, hup, hlow, ?_⟩
  rw [pow_two, map_mul, weylElement_eq_map hup hlow]

open Classical in
@[expose] noncomputable def wsign (k : Fin D.rank) (β : Fin D.rank → ℤ) : F :=
  if h : β ∈ D.roots then ((Classical.choose (hE.weyl k β h) : ℤ) : F) else 1

theorem wsign_spec {k : Fin D.rank} {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    (wsign hE k β = 1 ∨ wsign hE k β = -1) ∧ ∀ (t : Fˣ) (u : F),
      Steinberg.weylElement x k t * x β u * (Steinberg.weylElement x k t)⁻¹ =
        x (reflection D.cartan k β)
          (wsign hE k β * ((t ^ (-(∑ j, D.cartan k j * β j)) : Fˣ) : F) * u) := by
  have h := Classical.choose_spec (hE.weyl k β hβ)
  rw [wsign, dite_eq_left_of_eq_true (eq_true hβ)]
  refine ⟨?_, h.2⟩
  rcases h.1 with h1 | h1 <;> rw [h1] <;> simp

theorem wsign_mul_self {k : Fin D.rank} {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    wsign hE k β * wsign hE k β = 1 := by
  rcases (wsign_spec hE hβ).1 with h | h <;> rw [h] <;> simp

theorem wsign_ne_zero {k : Fin D.rank} {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    wsign hE k β ≠ 0 := fun h => by
  have := wsign_mul_self hE (k := k) hβ
  rw [h] at this
  simp at this

theorem weyl_conj_one {k : Fin D.rank} {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (u : F) :
    Steinberg.weylElement x k 1 * x β u * (Steinberg.weylElement x k 1)⁻¹ =
      x (reflection D.cartan k β) (wsign hE k β * u) := by
  rw [(wsign_spec hE hβ).2 1 u]
  simp

theorem wsign_single_self (i : Fin D.rank) : wsign hE i (Pi.single i 1) = -1 := by
  have hβ : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := single_mem_roots i
  have h1 := weyl_conj_one hE hβ (k := i) 1
  rw [weylElement_one_conj_single hE i 1,
    reflection_single_self (D.isFiniteType.apply_self i)] at h1
  have h2 := (hE.param _ (neg_mem_roots hβ)).2.2 h1
  simpa using h2.symm

theorem wsign_reflection {k : Fin D.rank} {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots)
    (hodd : Odd (∑ j, D.cartan k j * β j)) :
    wsign hE k (reflection D.cartan k β) = -wsign hE k β := by
  have hk : D.cartan k k = 2 := D.isFiniteType.apply_self k
  have hβ' : reflection D.cartan k β ∈ D.roots := reflection_mem_roots k hβ
  have hss : reflection D.cartan k (reflection D.cartan k β) = β := by
    have := congrArg (fun f => f β) (reflection_mul_self hk)
    simpa using this
  have hn' : ∑ j, D.cartan k j * (reflection D.cartan k β) j = -∑ j, D.cartan k j * β j := by
    rw [← coroot_apply, coroot_reflection hk, coroot_apply]
  have hW : Steinberg.weylElement x k (-1) = (Steinberg.weylElement x k 1)⁻¹ :=
    eq_inv_of_mul_eq_one_right (weylElement_one_mul_neg_one hE k)
  have key : x β 1 = Steinberg.weylElement x k (-1) *
      (Steinberg.weylElement x k 1 * x β 1 * (Steinberg.weylElement x k 1)⁻¹) *
        (Steinberg.weylElement x k (-1))⁻¹ := by
    rw [hW, inv_inv]
    group
  rw [weyl_conj_one hE hβ 1, (wsign_spec hE hβ').2 (-1) _, hss] at key
  have hpow : (((-1 : Fˣ) ^ (-(∑ j, D.cartan k j * (reflection D.cartan k β) j)) : Fˣ) : F) =
      -1 := by
    rw [hn', neg_neg, hodd.neg_one_zpow]
    simp
  rw [hpow] at key
  have h2 := (hE.param _ hβ).2.2 key
  have hsq := wsign_mul_self hE (k := k) hβ
  linear_combination (-wsign hE k (reflection D.cartan k β)) * hsq + wsign hE k β * h2

theorem wsign_comm {k : Fin D.rank} {z w : Fin D.rank → ℤ} (hz : z ∈ D.roots)
    (hw : w ∈ D.roots) (hzw : z + w ∈ D.roots) {N N' : F}
    (hN : ∀ c d, ⁅x z c, x w d⁆ = x (z + w) (N * c * d))
    (hN' : ∀ c d, ⁅x (reflection D.cartan k z) c, x (reflection D.cartan k w) d⁆ =
      x (reflection D.cartan k z + reflection D.cartan k w) (N' * c * d)) :
    N' * wsign hE k z * wsign hE k w = wsign hE k (z + w) * N := by
  have h1 : Steinberg.weylElement x k 1 * ⁅x z 1, x w 1⁆ * (Steinberg.weylElement x k 1)⁻¹ =
      ⁅Steinberg.weylElement x k 1 * x z 1 * (Steinberg.weylElement x k 1)⁻¹,
        Steinberg.weylElement x k 1 * x w 1 * (Steinberg.weylElement x k 1)⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hN 1 1, weyl_conj_one hE hzw, weyl_conj_one hE hz, weyl_conj_one hE hw, hN' _ _,
    ← map_add] at h1
  have h2 := (hE.param _ (reflection_mem_roots k hzw)).2.2 h1
  linear_combination -h2

end Weyl

end CFSG.ClassicalInvolution.WeakCT
