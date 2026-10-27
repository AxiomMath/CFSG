module

public import CFSG.GH74.GLS.C3.Layer2.L4Star

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4.Star

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2.L4.Wreath CFSG.GH74.GLS.Layer3
  CFSG.GH74.GLS.C3.Layer2

@[expose] def w3 : Perm (Ω8 ⊕ Fin (1 + 2)) := Perm.sumCongr 1 (finRotate (1 + 2))

@[expose] def kHom : Perm (Fin (1 + 2)) →* Perm (Ω8 ⊕ Fin (1 + 2)) :=
  (Perm.sumCongrHom Ω8 (Fin (1 + 2))).comp (MonoidHom.inr (Perm Ω8) (Perm (Fin (1 + 2))))

theorem kHom_apply (τ : Perm (Fin (1 + 2))) : kHom τ = Perm.sumCongr 1 τ := rfl

theorem w3_eq : w3 = kHom (finRotate (1 + 2)) := rfl

theorem kHom_apply_inl (τ : Perm (Fin (1 + 2))) (p : Ω8) : kHom τ (Sum.inl p) = Sum.inl p := by
  simp [kHom_apply]

theorem w3_pow_three : w3 ^ 3 = 1 := by
  have h : (finRotate (1 + 2)) ^ 3 = 1 := by decide
  rw [w3_eq, ← map_pow, h, map_one]

theorem w3_ne_one : w3 ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : Perm (Ω8 ⊕ Fin (1 + 2)) => g (Sum.inr 0)) h
  simp only [w3, Perm.sumCongr_apply, Sum.map_inr, Perm.one_apply, Sum.inr.injEq] at h1
  revert h1
  decide

theorem sign_w3 : sign w3 = 1 := by
  rw [w3, Perm.sign_sumCongr, Perm.sign_one, one_mul]
  decide

theorem thStar_conj_w3 (ε : N4) :
    thStar 1 ε * w3 * (thStar 1 ε)⁻¹ = if prodHom ε = 1 then w3 else w3⁻¹ := by
  rw [thStar_apply, w3, Perm.sumCongr_inv, Perm.sumCongr_mul, Perm.sumCongr_mul]
  have h1 : th0 ε * 1 * (th0 ε)⁻¹ = 1 := by group
  rw [h1]
  rcases Int.units_eq_one_or (prodHom ε) with h | h
  · have hr : rho 1 ε = 1 := by
      show unitsHom (swap (0 : Fin (1 + 2)) 1) (Equiv.swap_mul_self _ _) (prodHom ε) = 1
      rw [h, unitsHom_one]
    rw [hr]
    simp only [h, ↓reduceIte]
    simp
  · have hne : prodHom ε ≠ 1 := by rw [h]; decide
    have hr : rho 1 ε = swap (0 : Fin (1 + 2)) 1 := by
      show unitsHom (swap (0 : Fin (1 + 2)) 1) (Equiv.swap_mul_self _ _) (prodHom ε) = _
      rw [h, unitsHom_neg_one]
    rw [hr]
    simp only [hne, ↓reduceIte]
    rw [Perm.sumCongr_inv]
    have h2 : swap (0 : Fin (1 + 2)) 1 * finRotate (1 + 2) * (swap (0 : Fin (1 + 2)) 1)⁻¹ =
        (finRotate (1 + 2))⁻¹ := by decide
    rw [h2]
    simp

theorem sStar_conj_w3 (π : Perm (Fin 4)) : sStar 1 π * w3 * (sStar 1 π)⁻¹ = w3 := by
  rw [sStar_apply, w3, Perm.sumCongr_inv, Perm.sumCongr_mul, Perm.sumCongr_mul]
  have h1 : sBlock π * 1 * (sBlock π)⁻¹ = 1 := by group
  rw [h1]
  simp

theorem zpow_w3_inl (k : ℤ) (p : Ω8) : (w3 ^ k) (Sum.inl p) = Sum.inl p := by
  rw [w3_eq, ← map_zpow]
  exact kHom_apply_inl _ p

theorem eq_one_of_mem_zpowers_w3 (ε : N4) (π : Perm (Fin 4))
    (h : thStar 1 ε * sStar 1 π ∈ zpowers w3) : ε = 1 ∧ π = 1 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  have hπ : π = 1 := by
    refine Equiv.ext fun i => ?_
    have h1 := congrArg (fun g : Perm (Ω8 ⊕ Fin (1 + 2)) => g (Sum.inl (i, 0))) hk
    simp only [zpow_w3_inl, thStar_apply, sStar_apply, Perm.mul_apply, Perm.sumCongr_apply,
      Sum.map_inl, sBlock_apply, th0_apply, Sum.inl.injEq, Prod.mk.injEq] at h1
    simp only [Perm.one_apply]
    exact (h1.1).symm
  subst hπ
  refine ⟨?_, rfl⟩
  funext i
  have h1 := congrArg (fun g : Perm (Ω8 ⊕ Fin (1 + 2)) => g (Sum.inl (i, 0))) hk
  simp only [zpow_w3_inl, thStar_apply, Perm.mul_apply, Perm.sumCongr_apply,
    Sum.map_inl, th0_apply, Sum.inl.injEq, Prod.mk.injEq, map_one, Perm.one_apply,
    true_and] at h1
  rcases Int.units_eq_one_or (ε i) with h2 | h2
  · simpa using h2
  · rw [h2, unitsHom_neg_one] at h1
    simp at h1

section Glue7

variable {m : ℕ} (e : Ω8 ⊕ Fin (1 + 2) ≃ Fin m) (h8 : 8 ≤ m)

theorem exists_mulEquiv_seven_of
    (hy : (Equiv.permCongr e) (Perm.sumCongr F8 1) = yPerm h8)
    (hC : Nat.card ↥(centralizer ({altY h8} : Set (alternatingGroup (Fin m)))) = 1152) :
    Nonempty (W7 ≃* ↥(centralizer ({altY h8} : Set (alternatingGroup (Fin m))))) := by
  classical
  obtain ⟨θ, s, hθ, hcomp, hθc, hsc⟩ := exists_hom_centralizer (k := 1) e h8 hy
  let P : Perm (Ω8 ⊕ Fin (1 + 2)) →* Perm (Fin m) := (Equiv.permCongrHom e).toMonoidHom
  have hP : ∀ g, P g = Equiv.permCongr e g := fun g => rfl
  have hPinj : Function.Injective P := (Equiv.permCongrHom e).injective
  have hwalt : P w3 ∈ alternatingGroup (Fin m) := by
    rw [mem_alternatingGroup, hP, Perm.sign_permCongr]
    exact sign_w3
  have hwcomm : (⟨P w3, hwalt⟩ : alternatingGroup (Fin m)) ∈
      centralizer ({altY h8} : Set (alternatingGroup (Fin m))) := by
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    show P w3 * yPerm h8 = yPerm h8 * P w3
    rw [← hy, ← hP, ← map_mul, ← map_mul, w3, Perm.sumCongr_mul, Perm.sumCongr_mul]
    simp
  let wC : ↥(centralizer ({altY h8} : Set (alternatingGroup (Fin m)))) :=
    ⟨⟨P w3, hwalt⟩, hwcomm⟩
  have hwC : (((wC : alternatingGroup (Fin m)) : Perm (Fin m))) = P w3 := rfl
  have hwC3 : wC ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show ((wC : alternatingGroup (Fin m)) : Perm (Fin m)) ^ 3 = 1
    rw [hwC, ← map_pow, w3_pow_three, map_one]
  have hwC1 : wC ≠ 1 := by
    intro h
    have h1 : ((wC : alternatingGroup (Fin m)) : Perm (Fin m)) = 1 :=
      congrArg (fun z : ↥(centralizer ({altY h8} : Set (alternatingGroup (Fin m)))) =>
        ((z : alternatingGroup (Fin m)) : Perm (Fin m))) h
    rw [hwC] at h1
    exact w3_ne_one (hPinj (h1.trans (map_one P).symm))
  have hθw : ∀ ε, θ ε * wC * (θ ε)⁻¹ = if prodHom ε = 1 then wC else wC⁻¹ := by
    intro ε
    apply Subtype.ext
    apply Subtype.ext
    have hε := hθc ε
    have h1 : ((((θ ε * wC * (θ ε)⁻¹ : ↥(centralizer ({altY h8} :
        Set (alternatingGroup (Fin m))))) : alternatingGroup (Fin m))) : Perm (Fin m)) =
        P (thStar 1 ε * w3 * (thStar 1 ε)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [hP, hε, hwC]
    rw [h1, thStar_conj_w3]
    by_cases h : prodHom ε = 1
    · simp only [h, ↓reduceIte]
      rfl
    · simp only [h, ↓reduceIte]
      show P w3⁻¹ = ((wC⁻¹ : ↥(centralizer ({altY h8} : Set (alternatingGroup (Fin m))))) :
        alternatingGroup (Fin m))
      rw [map_inv]
      rfl
  have hsw : ∀ π, s π * wC * (s π)⁻¹ = wC := by
    intro π
    apply Subtype.ext
    apply Subtype.ext
    have hπ := hsc π
    have h1 : ((((s π * wC * (s π)⁻¹ : ↥(centralizer ({altY h8} :
        Set (alternatingGroup (Fin m))))) : alternatingGroup (Fin m))) : Perm (Fin m)) =
        P (sStar 1 π * w3 * (sStar 1 π)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [hP, hπ, hwC]
    rw [h1, sStar_conj_w3]
  have hdisj : ∀ ε π, θ ε * s π ∈ zpowers wC → θ ε * s π = 1 := by
    intro ε π h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have h1 : ((((θ ε * s π : ↥(centralizer ({altY h8} :
        Set (alternatingGroup (Fin m))))) : alternatingGroup (Fin m))) : Perm (Fin m)) =
        P (thStar 1 ε * sStar 1 π) := by
      simp only [Subgroup.coe_mul, map_mul]
      rw [hθc ε, hsc π]
      rfl
    have h2 : ((((wC ^ k : ↥(centralizer ({altY h8} :
        Set (alternatingGroup (Fin m))))) : alternatingGroup (Fin m))) : Perm (Fin m)) =
        P (w3 ^ k) := by
      simp only [Subgroup.coe_zpow, map_zpow]
      rw [hwC]
    rw [hk] at h2
    have h3 : thStar 1 ε * sStar 1 π = w3 ^ k := hPinj (h1.symm.trans h2)
    have h4 : thStar 1 ε * sStar 1 π ∈ zpowers w3 := ⟨k, h3.symm⟩
    obtain ⟨hε1, hπ1⟩ := eq_one_of_mem_zpowers_w3 ε π h4
    rw [hε1, hπ1, map_one, map_one, one_mul]
  exact exists_mulEquiv_W7 θ hθ s hcomp wC hwC3 hwC1 hθw hsw hdisj hC

end Glue7

theorem exists_mulEquiv_seven :
    ∃ v' : alternatingGroup (Fin (7 + 4)), orderOf v' = 2 ∧
      numMoved (v' : Perm (Fin (7 + 4))) = 8 ∧
      Nonempty (W7 ≃* ↥(centralizer ({v'} : Set (alternatingGroup (Fin (7 + 4)))))) := by
  have h8 : 8 ≤ 7 + 4 := by norm_num
  refine ⟨altY h8, orderOf_altY h8, numMoved_altY h8, ?_⟩
  have hcard : Nat.card ↥(centralizer ({altY h8} : Set (alternatingGroup (Fin (7 + 4))))) = 1152 := by
    have h := card_centralizer_altY h8
    have : (7 + 4 - 8).factorial = 6 := by decide
    rw [this] at h
    omega
  exact exists_mulEquiv_seven_of (eΩ 1) h8 eΩ_three hcard

end CFSG.GH74.GLS.C3.Layer2.L4.Star
