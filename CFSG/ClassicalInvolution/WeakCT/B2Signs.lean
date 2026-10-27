module

public import CFSG.ClassicalInvolution.WeakCT.B2Basic

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open scoped commutatorElement MatrixGroups

section SL2

variable {F : Type} [Field F]

theorem wS_one_mul_lower (u : F) :
    wS (1 : Fˣ) * Steinberg.sl2Lower u = Steinberg.sl2Upper (-u) * wS (1 : Fˣ) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, wS, coe_sl2Upper, coe_sl2Lower,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem wS_neg_one_eq :
    wS (-1 : Fˣ) = Steinberg.sl2Lower (1 : F) * Steinberg.sl2Upper (-1) * Steinberg.sl2Lower 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, wS, coe_sl2Upper, coe_sl2Lower,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end SL2

section Pairing

variable {K : Type} [Group K] {D : UniversalRootDatum K} {s l : Fin D.rank}

theorem pairing_pair (k : Fin D.rank) (z : ℤ × ℤ) :
    ∑ j, D.cartan k j * (pair s l z) j = z.1 * D.cartan k s + z.2 * D.cartan k l := by
  rw [← coroot_apply, pair_apply, map_add, map_zsmul, map_zsmul, coroot_single, coroot_single]
  simp only [smul_eq_mul]

end Pairing

section Signs

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem wsign_reflection_even {k : Fin D.rank} {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots)
    (heven : Even (∑ j, D.cartan k j * β j)) :
    wsign hE k (reflection D.cartan k β) = wsign hE k β := by
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
      1 := by
    rw [hn', neg_neg, heven.neg_one_zpow]
    simp
  rw [hpow] at key
  have h2 := (hE.param _ hβ).2.2 key
  have hsq := wsign_mul_self hE (k := k) hβ
  linear_combination (-wsign hE k β) * h2 + (-wsign hE k (reflection D.cartan k β)) * hsq

theorem weylElement_sq_commute {k : Fin D.rank} {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots)
    (heven : Even (∑ j, D.cartan k j * β j)) (u : F) :
    Commute (Steinberg.weylElement x k 1 ^ 2) (x β u) := by
  have hk : D.cartan k k = 2 := D.isFiniteType.apply_self k
  have hβ' : reflection D.cartan k β ∈ D.roots := reflection_mem_roots k hβ
  have hss : reflection D.cartan k (reflection D.cartan k β) = β := by
    have := congrArg (fun f => f β) (reflection_mul_self hk)
    simpa using this
  have h1 := weyl_conj_one hE (k := k) hβ u
  have h2 := weyl_conj_one hE (k := k) hβ' (wsign hE k β * u)
  rw [hss, wsign_reflection_even hE hβ heven] at h2
  have hsq := wsign_mul_self hE (k := k) hβ
  have h3 : Steinberg.weylElement x k 1 * (Steinberg.weylElement x k 1 * x β u *
      (Steinberg.weylElement x k 1)⁻¹) * (Steinberg.weylElement x k 1)⁻¹ = x β u := by
    rw [h1, h2, ← mul_assoc, hsq, one_mul]
  rw [commute_iff_eq, pow_two]
  calc Steinberg.weylElement x k 1 * Steinberg.weylElement x k 1 * x β u
      = (Steinberg.weylElement x k 1 * (Steinberg.weylElement x k 1 * x β u *
          (Steinberg.weylElement x k 1)⁻¹) * (Steinberg.weylElement x k 1)⁻¹) *
        (Steinberg.weylElement x k 1 * Steinberg.weylElement x k 1) := by group
    _ = x β u * (Steinberg.weylElement x k 1 * Steinberg.weylElement x k 1) := by rw [h3]

theorem weylElement_one_conj_neg_single (i : Fin D.rank) (u : F) :
    Steinberg.weylElement x i 1 * x (-Pi.single i 1) u * (Steinberg.weylElement x i 1)⁻¹ =
      x (Pi.single i 1) (-u) := by
  obtain ⟨φ, -, hup, hlow⟩ := hE.rankOne i
  have h : wS (1 : Fˣ) * Steinberg.sl2Lower u * (wS (1 : Fˣ))⁻¹ = Steinberg.sl2Upper (-u) :=
    mul_inv_eq_iff_eq_mul.2 (wS_one_mul_lower u)
  have h' := congrArg φ h
  rw [map_mul, map_mul, map_inv, hup, hlow] at h'
  rwa [weylElement_eq_map hup hlow]

theorem weylElement_neg_one_eq (i : Fin D.rank) :
    x (-Pi.single i 1) 1 * x (Pi.single i 1) (-1) * x (-Pi.single i 1) 1 =
      Steinberg.weylElement x i (-1) := by
  obtain ⟨φ, -, hup, hlow⟩ := hE.rankOne i
  rw [weylElement_eq_map hup hlow, wS_neg_one_eq, map_mul, map_mul, hup, hlow]

theorem wsign_neg_single_self (i : Fin D.rank) : wsign hE i (-Pi.single i 1) = -1 := by
  have hβ : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := neg_mem_roots (single_mem_roots i)
  have h1 := weyl_conj_one hE hβ (k := i) 1
  rw [weylElement_one_conj_neg_single hE i 1, map_neg,
    reflection_single_self (D.isFiniteType.apply_self i), neg_neg] at h1
  have h2 := (hE.param _ (single_mem_roots i)).2.2 h1
  simpa using h2.symm

theorem wsign_eq_one_of_commute {k : Fin D.rank} {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots)
    (hr : reflection D.cartan k β = β)
    (h1 : Commute (x (Pi.single k 1) 1) (x β 1))
    (h2 : Commute (x (-Pi.single k 1) (-1)) (x β 1)) : wsign hE k β = 1 := by
  have hW : Commute (Steinberg.weylElement x k 1) (x β 1) := by
    unfold Steinberg.weylElement
    simpa using (h1.mul_left h2).mul_left h1
  have h3 := weyl_conj_one hE hβ (k := k) 1
  rw [hr, show Steinberg.weylElement x k 1 * x β 1 * (Steinberg.weylElement x k 1)⁻¹ = x β 1 by
    rw [hW.eq]; group] at h3
  have h4 := (hE.param _ hβ).2.2 h3
  simpa using h4.symm

end Signs

section B2

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {s l : Fin D.rank}

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem b2_wsign_s_one_zero : wsign hE s (pair s l (1, 0)) = -1 := by
  rw [pair_one_zero]
  exact wsign_single_self hE s

theorem b2_wsign_s_neg_one_zero : wsign hE s (pair s l (-1, 0)) = -1 := by
  rw [pair_neg_one_zero]
  exact wsign_neg_single_self hE s

theorem b2_wsign_l_zero_one : wsign hE l (pair s l (0, 1)) = -1 := by
  rw [pair_zero_one]
  exact wsign_single_self hE l

theorem b2_wsign_l_zero_neg_one : wsign hE l (pair s l (0, -1)) = -1 := by
  rw [pair_zero_neg_one]
  exact wsign_neg_single_self hE l

theorem b2_wsign_l_two_one (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) : wsign hE l (pair s l (2, 1)) = 1 := by
  refine wsign_eq_one_of_commute hE (pair_mem_roots_zB2 hcsl hcls _ (by decide)) ?_ ?_ ?_
  · rw [reflection_pair_bL hcls]
    exact congrArg _ (by decide)
  · have := commute_of_nil hE hdiv hcsl hcls (z := (0, 1)) (w := (2, 1)) (by decide) (by decide)
      (by decide) (by decide) 1 1
    rwa [pair_zero_one] at this
  · have := commute_of_nil hE hdiv hcsl hcls (z := (0, -1)) (w := (2, 1)) (by decide)
      (by decide) (by decide) (by decide) (-1) 1
    rwa [pair_zero_neg_one] at this

theorem b2_wsign_l_neg_two_neg_one (hdiv : D.divisible = ∅) (hcsl : D.cartan s l = -2)
    (hcls : D.cartan l s = -1) : wsign hE l (pair s l (-2, -1)) = 1 := by
  refine wsign_eq_one_of_commute hE (pair_mem_roots_zB2 hcsl hcls _ (by decide)) ?_ ?_ ?_
  · rw [reflection_pair_bL hcls]
    exact congrArg _ (by decide)
  · have := commute_of_nil hE hdiv hcsl hcls (z := (0, 1)) (w := (-2, -1)) (by decide)
      (by decide) (by decide) (by decide) 1 1
    rwa [pair_zero_one] at this
  · have := commute_of_nil hE hdiv hcsl hcls (z := (0, -1)) (w := (-2, -1)) (by decide)
      (by decide) (by decide) (by decide) (-1) 1
    rwa [pair_zero_neg_one] at this

theorem b2_wsign_s_two_one (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    wsign hE s (pair s l (2, 1)) = wsign hE s (pair s l (0, 1)) := by
  have h := wsign_reflection_even hE (k := s) (pair_mem_roots_zB2 hcsl hcls (0, 1) (by decide))
    (by rw [pairing_pair, hcsl, D.isFiniteType.apply_self s]; decide)
  rwa [reflection_pair_bS hcsl, show bS (0, 1) = (2, 1) by decide] at h

theorem b2_wsign_s_neg_two_neg_one (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    wsign hE s (pair s l (-2, -1)) = wsign hE s (pair s l (0, -1)) := by
  have h := wsign_reflection_even hE (k := s) (pair_mem_roots_zB2 hcsl hcls (0, -1) (by decide))
    (by rw [pairing_pair, hcsl, D.isFiniteType.apply_self s]; decide)
  rwa [reflection_pair_bS hcsl, show bS (0, -1) = (-2, -1) by decide] at h

theorem b2_wsign_l_one_one (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    wsign hE l (pair s l (1, 1)) = -wsign hE l (pair s l (1, 0)) := by
  have h := wsign_reflection hE (k := l) (pair_mem_roots_zB2 hcsl hcls (1, 0) (by decide))
    (by rw [pairing_pair, hcls, D.isFiniteType.apply_self l]; decide)
  rwa [reflection_pair_bL hcls, show bL (1, 0) = (1, 1) by decide] at h

theorem b2_wsign_l_neg_one_neg_one (hcsl : D.cartan s l = -2) (hcls : D.cartan l s = -1) :
    wsign hE l (pair s l (-1, -1)) = -wsign hE l (pair s l (-1, 0)) := by
  have h := wsign_reflection hE (k := l) (pair_mem_roots_zB2 hcsl hcls (-1, 0) (by decide))
    (by rw [pairing_pair, hcls, D.isFiniteType.apply_self l]; decide)
  rwa [reflection_pair_bL hcls, show bL (-1, 0) = (-1, -1) by decide] at h

end B2


end CFSG.ClassicalInvolution.WeakCT
