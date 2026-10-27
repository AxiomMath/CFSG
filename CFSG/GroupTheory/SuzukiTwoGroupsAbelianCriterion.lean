module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.GroupTheory

open Subgroup

variable {U Y : Type*} [Group U] [Group Y]

theorem exists_smul_eq_of_free_of_card_eq [Finite U] [Finite Y] (ρ : Y →* MulAut U)
    (hfix : ∀ y : Y, y ≠ 1 → ∀ u : U, ρ y u = u → u = 1) (V : Subgroup U)
    (hVY : ∀ y : Y, ∀ v ∈ V, ρ y v ∈ V) (hcard : Nat.card Y + 1 = Nat.card V)
    {v₀ : U} (hv₀ : v₀ ∈ V) (hv₀1 : v₀ ≠ 1) {v : U} (hv : v ∈ V) (hv1 : v ≠ 1) :
    ∃ y : Y, ρ y v₀ = v := by
  classical
  let T : Type _ := {w : V // w ≠ 1}
  let f : Y → T := fun y => ⟨⟨ρ y v₀, hVY y v₀ hv₀⟩, fun h => hv₀1 (by
    have h' : ρ y v₀ = 1 := congrArg Subtype.val h
    simpa using congrArg (ρ y).symm h')⟩
  have hf : Function.Injective f := by
    intro y y' hyy'
    have h1 : ρ y v₀ = ρ y' v₀ := congrArg (fun w : T => ((w : V) : U)) hyy'
    have h2 : ρ (y'⁻¹ * y) v₀ = v₀ := by
      rw [map_mul, MulAut.mul_apply, h1, map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    by_contra hne
    exact hv₀1 (hfix (y'⁻¹ * y) (fun h => hne (by
      rw [inv_mul_eq_one] at h
      exact h.symm)) v₀ h2)
  have hT : Nat.card T = Nat.card V - 1 := by
    have : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  have hbij : Function.Bijective f :=
    (Function.Injective.bijective_of_nat_card_le hf (by omega))
  obtain ⟨y, hy⟩ := hbij.2 ⟨⟨v, hv⟩, fun h => hv1 (congrArg Subtype.val h)⟩
  exact ⟨y, congrArg (fun w : T => ((w : V) : U)) hy⟩

theorem isMulCommutative_of_fixedPointFree_cyclic [Finite U] [Finite Y] [IsCyclic Y] {n : ℕ}
    (hn : 1 ≤ n) (hU : Nat.card U = (2 ^ n) ^ 2) (hY : Nat.card Y = 2 ^ n - 1)
    (ρ : Y →* MulAut U) (hfix : ∀ y : Y, y ≠ 1 → ∀ u : U, ρ y u = u → u = 1)
    (V : Subgroup U) [V.Normal] (hVY : ∀ y : Y, ∀ v ∈ V, ρ y v ∈ V)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 (U ⧸ V)] (θ : U ⧸ V ≃* V)
    (hθ : ∀ (y : Y) (u : U),
      ((θ ((ρ y u : U) : U ⧸ V) : V) : U) = ρ y ((θ (u : U ⧸ V) : V) : U)) :
    IsMulCommutative U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hVcard : Nat.card V = 2 ^ n := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    have h2 : Nat.card (U ⧸ V) = Nat.card V := Nat.card_congr θ.toEquiv
    rw [h2, hU, ← pow_two] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  have hcard : Nat.card Y + 1 = Nat.card V := by
    rw [hY, hVcard]
    omega
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2 * n) (by rw [hU, ← pow_mul, mul_comm])
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVcard
    omega
  have : Group.IsNilpotent U := hU2.isNilpotent
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ V ⊓ center U, z ≠ 1 := by
    obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hVne))
    exact ⟨z, hz, fun h => hz1 (Subtype.ext h)⟩
  have hVZ : ∀ v ∈ V, v ∈ center U := by
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact one_mem _
    obtain ⟨y, rfl⟩ := exists_smul_eq_of_free_of_card_eq ρ hfix V hVY hcard
      (Subgroup.mem_inf.1 hz).1 hz1 hv hv1
    rw [Subgroup.mem_center_iff]
    intro g
    have hzc := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 hz).2 ((ρ y).symm g)
    calc g * ρ y z = ρ y ((ρ y).symm g * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = ρ y (z * (ρ y).symm g) := by rw [hzc]
      _ = ρ y z * g := by rw [map_mul, MulEquiv.apply_symm_apply]
  have hsqV : ∀ u : U, u ^ 2 ∈ V := by
    intro u
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (IsElementaryAbelian.exponent_dvd_p 2 (U ⧸ V)) (u : U ⧸ V)
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v₀ ∈ V, v₀ ≠ 1 := ⟨z, (Subgroup.mem_inf.1 hz).1, hz1⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, ((θ (u₀ : U ⧸ V) : V) : U) = v₀ := by
    obtain ⟨q, hq⟩ := θ.surjective ⟨v₀, hv₀⟩
    obtain ⟨u₀, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨u₀, by rw [hq]⟩
  have hYc : IsMulCommutative Y := IsCyclic.isMulCommutative
  have hYcomm : ∀ y y' : Y, y * y' = y' * y := fun y y' => mul_comm' y y'
  obtain ⟨τ, hτρ, hτ0⟩ : ∃ τ : U →* U,
      (∀ y : Y, ∀ x : U, τ (ρ y x) = ρ y (τ x)) ∧ τ v₀ = u₀ ^ 2 := by
    by_cases hw : u₀ ^ 2 = 1
    · exact ⟨1, fun y x => by simp, by simp [hw]⟩
    · obtain ⟨y₀, hy₀⟩ := exists_smul_eq_of_free_of_card_eq ρ hfix V hVY hcard hv₀ hv₀1
        (hsqV u₀) hw
      refine ⟨(ρ y₀).toMonoidHom, fun y x => ?_, hy₀⟩
      change ρ y₀ (ρ y x) = ρ y (ρ y₀ x)
      rw [← MulAut.mul_apply, ← map_mul, hYcomm, map_mul, MulAut.mul_apply]
  have hkey : ∀ u : U, u ^ 2 = τ ((θ (u : U ⧸ V) : V) : U) := by
    intro u
    by_cases hv1 : ((θ (u : U ⧸ V) : V) : U) = 1
    · have hu1 : (u : U ⧸ V) = 1 := by
        apply θ.injective
        rw [map_one]
        exact Subtype.ext hv1
      rw [QuotientGroup.eq_one_iff] at hu1
      rw [hv1, map_one, hVsq u hu1]
    · obtain ⟨y, hy⟩ := exists_smul_eq_of_free_of_card_eq ρ hfix V hVY hcard hv₀ hv₀1
        (θ (u : U ⧸ V)).2 hv1
      have h1 : ((ρ y u₀ : U) : U ⧸ V) = (u : U ⧸ V) := by
        apply θ.injective
        apply Subtype.ext
        rw [hθ, hu₀, hy]
      have ht : (ρ y u₀)⁻¹ * u ∈ V := QuotientGroup.eq.1 h1
      have hu : u = ρ y u₀ * ((ρ y u₀)⁻¹ * u) := by group
      have hcomm : Commute (ρ y u₀) ((ρ y u₀)⁻¹ * u) :=
        ((Subgroup.mem_center_iff.1 (hVZ _ ht)) (ρ y u₀))
      rw [← hy, hτρ, hτ0, map_pow]
      conv_lhs => rw [hu]
      rw [hcomm.mul_pow, hVsq _ ht, mul_one]
  refine IsMulCommutative.of_comm fun a b => ?_
  have hab : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
    rw [hkey, hkey a, hkey b, QuotientGroup.mk_mul, map_mul, Subgroup.coe_mul, map_mul]
  have h3 : a * (b * a) * b = a * (a * b) * b := by
    simpa [pow_two, mul_assoc] using hab
  exact (mul_left_cancel (mul_right_cancel h3)).symm

end CFSG.GroupTheory
