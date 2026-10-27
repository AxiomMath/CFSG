module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Z3CubeAux
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Defs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

theorem exists_fixed_order_three_lift {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y} (z : Y)
    (hz : MulAut.conj z ∈ stabAut J) (hz3 : z ^ 3 ∈ Subgroup.center Y) {tb : barOf 3 J}
    (hfix : inducedBarHom J ⟨MulAut.conj z, hz⟩ tb = tb) (hord : orderOf tb = 3) :
    ∃ t : ↥J, z * (t : Y) * z⁻¹ = (t : Y) ∧ t ^ 3 = 1 ∧
      (QuotientGroup.mk t : barOf 3 J) ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup ↥J := GLAPPrimeCore 3 ↥J with hN
  set γ : ↥(stabAut J) := ⟨MulAut.conj z, hz⟩ with hγ
  obtain ⟨t₁, ht₁⟩ := QuotientGroup.mk_surjective tb
  let T : Type := {y : ↥J // (QuotientGroup.mk y : barOf 3 J) = tb}
  let ρ : MulAut ↥J := restrictAut γ.1 γ.2
  have hρy : ∀ y : ↥J, ((ρ y : ↥J) : Y) = z * (y : Y) * z⁻¹ := fun y => by
    show ((restrictAut γ.1 γ.2 y : ↥J) : Y) = _
    rw [restrictAut_coe]
    rfl
  have hρmk : ∀ y : ↥J, (QuotientGroup.mk (ρ y) : barOf 3 J) =
      inducedBarHom J γ (QuotientGroup.mk y) := fun y => (inducedBarHom_mk J γ y).symm
  have hρT : ∀ y : T, (QuotientGroup.mk (ρ y.1) : barOf 3 J) = tb := fun y => by
    rw [hρmk, y.2]
    exact hfix
  let g : T → T := fun y => ⟨ρ y.1, hρT y⟩
  have hginj : Function.Injective g := by
    intro y y' h
    apply Subtype.ext
    exact ρ.injective (congrArg Subtype.val h)
  haveI : Finite T := Subtype.finite
  let f : Equiv.Perm T := Equiv.ofBijective g hginj.bijective_of_finite
  have hρ3 : ∀ y : ↥J, ρ (ρ (ρ y)) = y := fun y => by
    apply Subtype.ext
    rw [hρy, hρy, hρy]
    have hc : (y : Y) * z ^ 3 = z ^ 3 * y := Subgroup.mem_center_iff.1 hz3 y
    calc z * (z * (z * (y : Y) * z⁻¹) * z⁻¹) * z⁻¹ = z ^ 3 * (y : Y) * (z ^ 3)⁻¹ := by
          simp only [pow_three, mul_inv_rev, mul_assoc]
      _ = (y : Y) := by rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hf3 : f ^ 3 = 1 := by
    refine Equiv.ext fun y => ?_
    rw [pow_three]
    exact Subtype.ext (hρ3 y.1)
  let eN : T ≃ ↥N :=
    { toFun := fun y => ⟨t₁⁻¹ * y.1, QuotientGroup.eq.1 (ht₁.trans y.2.symm)⟩
      invFun := fun n => ⟨t₁ * n.1, by
        show (QuotientGroup.mk (t₁ * n.1) : barOf 3 J) = tb
        rw [QuotientGroup.mk_mul, ht₁, (QuotientGroup.eq_one_iff n.1).2 n.2, mul_one]⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun n => Subtype.ext (by simp) }
  have hNc : Nat.Coprime 3 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have hT3 : ¬ 3 ∣ Nat.card T := by
    rw [Nat.card_congr eN]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hNc
  obtain ⟨y₀, hy₀⟩ := exists_fixedPoint_perm_of_coprime f hf3 hT3
  have hρy₀ : ρ y₀.1 = y₀.1 := congrArg Subtype.val hy₀
  set t₂ : ↥J := y₀.1 with ht₂
  have hmk2 : (QuotientGroup.mk t₂ : barOf 3 J) = tb := y₀.2
  have h3o : 3 ∣ orderOf t₂ := by
    have := orderOf_map_dvd (QuotientGroup.mk' N) t₂
    rw [show (QuotientGroup.mk' N) t₂ = (QuotientGroup.mk t₂ : barOf 3 J) from rfl, hmk2,
      hord] at this
    exact this
  have hpow : tb ^ 3 = 1 := by
    have := pow_orderOf_eq_one tb
    rwa [hord] at this
  have ht3N : t₂ ^ 3 ∈ N :=
    (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow, hmk2, hpow])
  have hndvd : ¬ 3 ∣ orderOf t₂ / 3 := by
    intro h
    have h1 : orderOf (t₂ ^ 3) = orderOf t₂ / 3 := by
      rw [orderOf_pow' _ (by norm_num), Nat.gcd_eq_right h3o]
    have h2 : orderOf (⟨t₂ ^ 3, ht3N⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, h1] at h2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hNc (h.trans h2)
  refine ⟨t₂ ^ (orderOf t₂ / 3), ?_, ?_, ?_⟩
  · have h1 : ρ (t₂ ^ (orderOf t₂ / 3)) = t₂ ^ (orderOf t₂ / 3) := by rw [map_pow, hρy₀]
    have h2 := congrArg Subtype.val h1
    rw [hρy] at h2
    exact h2
  · rw [← pow_mul, Nat.div_mul_cancel h3o, pow_orderOf_eq_one]
  · intro h
    rw [QuotientGroup.mk_pow, hmk2] at h
    have h4 : orderOf tb ∣ orderOf t₂ / 3 := orderOf_dvd_of_pow_eq_one h
    rw [hord] at h4
    exact hndvd h4

end CFSG.HardMathSupport.Dickson.Sec6.I1431
