module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS1

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open QuaternionGroup
open scoped MatrixGroups

theorem isSolvable_of_cyclic_sylow_two {H : Type*} [Group H] [Finite H]
    (hcyc : ∀ P : Sylow 2 H, IsCyclic P) : Group.IsSolvable H := by
  classical
  by_cases hodd : Odd (Nat.card H)
  · exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  · have h2 : 2 ∣ Nat.card H := by
      have := Nat.not_odd_iff_even.mp hodd
      exact even_iff_two_dvd.mp this
    have hmin : (Nat.card H).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P⟩ : Nonempty (Sylow 2 H) := inferInstance
    have hP : IsCyclic P := hcyc P
    have hc := hP.normalizer_le_centralizer hmin
    let f := MonoidHom.transferSylow P hc
    have hNodd : Odd (Nat.card f.ker) := by
      have h2' : ¬ 2 ∣ Nat.card f.ker := MonoidHom.not_dvd_card_ker_transferSylow P hc
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2')
    have hNsolv : Group.IsSolvable f.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
    have : Group.IsSolvable ↥(P : Subgroup H) := inferInstance
    have : Group.IsSolvable f.range := inferInstance
    exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.range_subtype])


section Quat

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem zmod_two_mul_self_eq_zero : ((n : ZMod (2 * n)) + n) = 0 := by
  have : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self (2 * n)
  push_cast at this
  linear_combination this

theorem zmod_double_eq_zero {i : ZMod (2 * n)} (h : i + i = 0) : i = 0 ∨ i = n := by
  have h1 : ((2 * i.val : ℕ) : ZMod (2 * n)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination h
  have h2 := (ZMod.natCast_eq_zero_iff (2 * i.val) (2 * n)).mp h1
  have h3 : n ∣ i.val := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h2
  obtain ⟨c, hc⟩ := h3
  have hlt : i.val < 2 * n := ZMod.val_lt i
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hc2 : c < 2 := by
    by_contra hcc
    push Not at hcc
    have : n * 2 ≤ n * c := Nat.mul_le_mul_left n hcc
    omega
  interval_cases c
  · left
    rw [← ZMod.natCast_zmod_val i, hc]
    simp
  · right
    rw [← ZMod.natCast_zmod_val i, hc]
    simp

theorem quaternion_involution {x : QuaternionGroup n} (hx : x * x = 1) (hx1 : x ≠ 1) :
    x = a n := by
  cases x with
  | a i =>
    rw [a_mul_a] at hx
    have h1 : i + i = 0 := QuaternionGroup.a.inj (hx.trans one_def)
    rcases zmod_double_eq_zero h1 with h | h
    · exact absurd (by rw [h, one_def]) hx1
    · rw [h]
  | xa i =>
    exfalso
    rw [xa_mul_xa] at hx
    have h1 : (n : ZMod (2 * n)) = 0 := by
      have := QuaternionGroup.a.inj (hx.trans one_def)
      simpa using this
    have h2 := (ZMod.natCast_eq_zero_iff n (2 * n)).mp h1
    have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have := Nat.le_of_dvd hpos h2
    omega

omit [NeZero n] in
theorem a_pow (j : ZMod (2 * n)) (m : ℕ) :
    (a j : QuaternionGroup n) ^ m = a ((m : ZMod (2 * n)) * j) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, a_zero]
  | succ m ih =>
    rw [pow_succ, ih, a_mul_a]
    congr 1
    push_cast
    ring

theorem cyclic_of_no_quaternion_pair (S : Subgroup (QuaternionGroup n))
    (hS2 : ∀ x ∈ S, ∃ s : ℕ, orderOf x = 2 ^ s)
    (hno : ∀ x ∈ S, ∀ y ∈ S, x * x = a n → y * y = a n → x * y = a n * (y * x) → False) :
    IsCyclic S := by
  classical
  have hnn : (n : ZMod (2 * n)) + n = 0 := zmod_two_mul_self_eq_zero
  by_cases hA : ∀ x ∈ S, ∃ i, x = a i
  ·
    have hle : S ≤ Subgroup.zpowers (a 1 : QuaternionGroup n) := by
      intro x hx
      obtain ⟨i, rfl⟩ := hA x hx
      refine ⟨(i.val : ℤ), ?_⟩
      show (a 1 : QuaternionGroup n) ^ ((i.val : ℕ) : ℤ) = a i
      rw [zpow_natCast, a_one_pow, ZMod.natCast_zmod_val]
    exact Subgroup.isCyclic_of_le hle
  · push Not at hA
    obtain ⟨x₀, hx₀S, hx₀⟩ := hA
    obtain ⟨i₀, rfl⟩ : ∃ i₀, x₀ = xa i₀ := by
      cases x₀ with
      | a i => exact absurd rfl (hx₀ i)
      | xa i => exact ⟨i, rfl⟩
    have hC : ∀ j, a j ∈ S → a j * a j = 1 := by
      intro j hj
      by_contra hne
      obtain ⟨s, hs⟩ := hS2 _ hj
      have hs2 : 2 ≤ s := by
        by_contra hlt
        push Not at hlt
        apply hne
        have : orderOf (a j : QuaternionGroup n) ∣ 2 := by
          rw [hs]
          calc 2 ^ s ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
            _ = 2 := by norm_num
        have h2 := orderOf_dvd_iff_pow_eq_one.mp this
        simpa [pow_two] using h2
      set w : QuaternionGroup n := (a j) ^ (2 ^ (s - 2)) with hw
      have hwS : w ∈ S := S.pow_mem hj _
      have hw4 : orderOf w = 4 := by
        rw [hw, orderOf_pow_of_dvd (by positivity) (by rw [hs]; exact pow_dvd_pow 2 (by omega)), hs]
        have : 2 ^ s = 2 ^ (s - 2) * 4 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
          congr 1
          omega
        rw [this, Nat.mul_div_cancel_left _ (by positivity)]
      have hww : w * w = a n := by
        apply quaternion_involution
        · have : w ^ 4 = 1 := by rw [← hw4]; exact pow_orderOf_eq_one w
          calc w * w * (w * w) = w ^ 4 := by simp [pow_succ, mul_assoc]
            _ = 1 := this
        · intro h
          have : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
          rw [hw4] at this
          omega
      obtain ⟨j', hj'⟩ : ∃ j', w = a j' := ⟨_, by rw [hw, a_pow]⟩
      apply hno (xa i₀) hx₀S w hwS (xa_sq i₀ ▸ (by simp [sq])) hww
      ·
        rw [hj'] at hww ⊢
        rw [a_mul_a] at hww
        have h2 : j' + j' = n := QuaternionGroup.a.inj hww
        rw [xa_mul_a, a_mul_xa, a_mul_xa]
        congr 1
        linear_combination h2 + hnn
    have hX : ∀ k, xa k ∈ S → k = i₀ ∨ k = i₀ + n := by
      intro k hk
      have hm : xa i₀ * xa k ∈ S := S.mul_mem hx₀S hk
      rw [xa_mul_xa] at hm
      have h1 := hC _ hm
      rw [a_mul_a] at h1
      have h2 : ((n : ZMod (2 * n)) + k - i₀) + ((n : ZMod (2 * n)) + k - i₀) = 0 :=
        QuaternionGroup.a.inj (h1.trans one_def)
      rcases zmod_double_eq_zero h2 with h | h
      · right
        linear_combination h - hnn
      · left
        linear_combination h
    have hle : S ≤ Subgroup.zpowers (xa i₀ : QuaternionGroup n) := by
      intro y hy
      cases y with
      | a j =>
        have h1 := hC j hy
        rw [a_mul_a] at h1
        have h2 : j + j = 0 := QuaternionGroup.a.inj (h1.trans one_def)
        rcases zmod_double_eq_zero h2 with h | h
        · rw [h, a_zero]
          exact Subgroup.one_mem _
        · rw [h, ← xa_sq i₀]
          exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
      | xa k =>
        rcases hX k hy with h | h
        · rw [h]
          exact Subgroup.mem_zpowers _
        · rw [h]
          have h3 : (xa (i₀ + n) : QuaternionGroup n) = xa i₀ ^ 3 := by
            rw [pow_succ, xa_sq, a_mul_xa]
            congr 1
            linear_combination hnn
          rw [h3]
          exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3
    exact Subgroup.isCyclic_of_le hle

end Quat
section Quat2

variable {n : ℕ} [NeZero n]

theorem a_n_ne_one : (a (n : ZMod (2 * n)) : QuaternionGroup n) ≠ 1 := by
  intro h
  have h1 := QuaternionGroup.a.inj (h.trans one_def)
  have h2 := (ZMod.natCast_eq_zero_iff n (2 * n)).mp h1
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have := Nat.le_of_dvd hpos h2
  omega

end Quat2


theorem isCyclic_of_no_quaternion_pair_sl2 (F : Type*) [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (P : Subgroup SL(2, F)) (hP2 : IsPGroup 2 P)
    (hno : ∀ g₁ ∈ P, ∀ g₂ ∈ P, g₁ * g₁ = -1 → g₂ * g₂ = -1 →
      g₁ * g₂ = (-1 : SL(2, F)) * (g₂ * g₁) → False) : IsCyclic P := by
  classical
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  obtain ⟨k, hk, ⟨e⟩⟩ := specialLinearGroup_sylow_quaternion F hF Q
  have hne : NeZero (2 ^ k) := ⟨by positivity⟩
  set zq : ↥(Q : Subgroup SL(2, F)) := e.symm (a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k))) with hz
  have hezz : e zq = a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) := by rw [hz, MulEquiv.apply_symm_apply]
  have hzz : zq * zq = 1 := by
    apply e.injective
    rw [map_mul, hezz, a_mul_a, zmod_two_mul_self_eq_zero, a_zero, map_one]
  have hz1 : zq ≠ 1 := by
    intro h
    apply a_n_ne_one (n := 2 ^ k)
    rw [← hezz, h, map_one]
  have hzq : ((zq : ↥(Q : Subgroup SL(2, F))) : SL(2, F)) = -1 := by
    have hord : orderOf ((zq : ↥(Q : Subgroup SL(2, F))) : SL(2, F)) = 2 := by
      apply orderOf_eq_prime
      · have := congrArg Subtype.val hzz
        rw [pow_two]
        simpa using this
      · intro h
        exact hz1 (Subtype.ext h)
    exact ((specialLinearGroup_unique_involution F hF).2.2 _).mp hord
  set S : Subgroup (QuaternionGroup (2 ^ k)) := (P.subgroupOf Q).map e.toMonoidHom with hS
  have hS2 : ∀ x ∈ S, ∃ s : ℕ, orderOf x = 2 ^ s := by
    rintro x ⟨x', hx', rfl⟩
    have hx'P : ((x' : ↥(Q : Subgroup SL(2, F))) : SL(2, F)) ∈ P := hx'
    obtain ⟨m, hm⟩ := hP2 ⟨_, hx'P⟩
    have h1 : orderOf (⟨_, hx'P⟩ : ↥P) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    refine ⟨s, ?_⟩
    rw [MulEquiv.coe_toMonoidHom] at *
    calc orderOf (e x') = orderOf x' := MulEquiv.orderOf_eq e x'
      _ = orderOf ((x' : ↥(Q : Subgroup SL(2, F))) : SL(2, F)) := (Subgroup.orderOf_coe x').symm
      _ = orderOf (⟨_, hx'P⟩ : ↥P) := (Subgroup.orderOf_coe (⟨_, hx'P⟩ : ↥P))
      _ = 2 ^ s := hs
  have hSno : ∀ x ∈ S, ∀ y ∈ S, x * x = a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) →
      y * y = a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) →
      x * y = a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) * (y * x) → False := by
    rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩ hxx hyy hxy
    have hx'P : ((x' : ↥(Q : Subgroup SL(2, F))) : SL(2, F)) ∈ P := hx'
    have hy'P : ((y' : ↥(Q : Subgroup SL(2, F))) : SL(2, F)) ∈ P := hy'
    rw [MulEquiv.coe_toMonoidHom] at hxx hyy hxy
    have e1 : x' * x' = zq := by
      apply e.injective
      rw [map_mul, hxx, hezz]
    have e2 : y' * y' = zq := by
      apply e.injective
      rw [map_mul, hyy, hezz]
    have e3 : x' * y' = zq * (y' * x') := by
      apply e.injective
      rw [map_mul, map_mul, map_mul, hezz, hxy]
    refine hno _ hx'P _ hy'P ?_ ?_ ?_
    · rw [← hzq, ← e1]
      rfl
    · rw [← hzq, ← e2]
      rfl
    · rw [← hzq]
      exact congrArg Subtype.val e3
  have hScyc : IsCyclic S := cyclic_of_no_quaternion_pair S hS2 hSno
  have e1 : ↥(P.subgroupOf Q) ≃* ↥S := Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  have hc1 : IsCyclic ↥(P.subgroupOf Q) :=
    isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPQ).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hPQ).surjective


theorem quaternion_pair_fixed {M : Type*} [Group M] (c : M) (hc : ∀ x, c * x = x * c)
    (hcc : c * c = 1) (ζ : M ≃* M) {g₁ g₂ : M} (h₁ : g₁ * g₁ = c) (h₂ : g₂ * g₂ = c)
    (h12 : g₁ * g₂ = c * (g₂ * g₁)) (hζ₁ : ζ g₁ = g₁ ∨ ζ g₁ = c * g₁)
    (hζ₂ : ζ g₂ = g₂ ∨ ζ g₂ = c * g₂) : ∃ g, g * g = c ∧ ζ g = g := by
  rcases hζ₁ with h | h
  · exact ⟨g₁, h₁, h⟩
  rcases hζ₂ with h' | h'
  · exact ⟨g₂, h₂, h'⟩
  refine ⟨g₁ * g₂, ?_, ?_⟩
  · have hi : g₂ * g₁ = c * (g₁ * g₂) := by
      calc g₂ * g₁ = (c * c) * (g₂ * g₁) := by rw [hcc, one_mul]
        _ = c * (c * (g₂ * g₁)) := by group
        _ = c * (g₁ * g₂) := by rw [← h12]
    calc g₁ * g₂ * (g₁ * g₂) = g₁ * (g₂ * g₁) * g₂ := by group
      _ = g₁ * (c * (g₁ * g₂)) * g₂ := by rw [hi]
      _ = c * (g₁ * g₁) * (g₂ * g₂) := by
          calc g₁ * (c * (g₁ * g₂)) * g₂ = (g₁ * c) * (g₁ * g₂) * g₂ := by group
            _ = (c * g₁) * (g₁ * g₂) * g₂ := by rw [← hc g₁]
            _ = c * (g₁ * g₁) * (g₂ * g₂) := by group
      _ = c * c * c := by rw [h₁, h₂]
      _ = c := by rw [hcc, one_mul]
  · rw [map_mul, h, h']
    calc c * g₁ * (c * g₂) = (c * (g₁ * c)) * g₂ := by group
      _ = (c * (c * g₁)) * g₂ := by rw [← hc g₁]
      _ = (c * c) * g₁ * g₂ := by group
      _ = g₁ * g₂ := by rw [hcc, one_mul]



section SignFix

variable {F : Type} [Field F]

@[expose] def signFix (ζ : MulAut SL(2, F)) : Subgroup SL(2, F) where
  carrier := {h | ζ h = h ∨ ζ h = (-1 : SL(2, F)) * h}
  mul_mem' := by
    have hc : ∀ x : SL(2, F), (-1 : SL(2, F)) * x = x * (-1) := sl2_neg_one_central
    have hcc : (-1 : SL(2, F)) * (-1) = 1 := by
      apply Subtype.ext
      simp
    rintro h₁ h₂ (h1 | h1) (h2 | h2)
    · left
      show ζ (h₁ * h₂) = h₁ * h₂
      rw [map_mul, h1, h2]
    · right
      show ζ (h₁ * h₂) = (-1 : SL(2, F)) * (h₁ * h₂)
      rw [map_mul, h1, h2]
      calc h₁ * ((-1) * h₂) = (h₁ * (-1)) * h₂ := by group
        _ = ((-1) * h₁) * h₂ := by rw [← hc h₁]
        _ = (-1) * (h₁ * h₂) := by group
    · right
      show ζ (h₁ * h₂) = (-1 : SL(2, F)) * (h₁ * h₂)
      rw [map_mul, h1, h2]
      group
    · left
      show ζ (h₁ * h₂) = h₁ * h₂
      rw [map_mul, h1, h2]
      calc (-1 : SL(2, F)) * h₁ * ((-1) * h₂) = (-1) * (h₁ * (-1)) * h₂ := by group
        _ = (-1) * ((-1) * h₁) * h₂ := by rw [← hc h₁]
        _ = ((-1) * (-1)) * h₁ * h₂ := by group
        _ = h₁ * h₂ := by rw [hcc, one_mul]
  one_mem' := Or.inl (map_one ζ)
  inv_mem' := by
    have hc : ∀ x : SL(2, F), (-1 : SL(2, F)) * x = x * (-1) := sl2_neg_one_central
    have hcc : (-1 : SL(2, F)) * (-1) = 1 := by
      apply Subtype.ext
      simp
    have hci : (-1 : SL(2, F))⁻¹ = -1 := inv_eq_of_mul_eq_one_right hcc
    rintro h (h1 | h1)
    · left
      show ζ h⁻¹ = h⁻¹
      rw [map_inv, h1]
    · right
      show ζ h⁻¹ = (-1 : SL(2, F)) * h⁻¹
      rw [map_inv, h1, mul_inv_rev, hci]
      exact (hc h⁻¹).symm

theorem mem_signFix_iff (ζ : MulAut SL(2, F)) (h : SL(2, F)) :
    h ∈ signFix ζ ↔ ζ h = h ∨ ζ h = (-1 : SL(2, F)) * h := Iff.rfl

variable [Finite F]

theorem signFix_isSolvable (hF : ringChar F ≠ 2) (ζ : MulAut SL(2, F))
    (hbad : ∀ g : SL(2, F), g * g = -1 → ζ g ≠ g) : Group.IsSolvable (signFix ζ) := by
  classical
  have hc : ∀ x : SL(2, F), (-1 : SL(2, F)) * x = x * (-1) := sl2_neg_one_central
  have hcc : (-1 : SL(2, F)) * (-1) = 1 := by
    apply Subtype.ext
    simp
  refine isSolvable_of_cyclic_sylow_two fun P => ?_
  set P' : Subgroup SL(2, F) := (P : Subgroup ↥(signFix ζ)).map (signFix ζ).subtype with hP'
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map _
  have hno : ∀ g₁ ∈ P', ∀ g₂ ∈ P', g₁ * g₁ = -1 → g₂ * g₂ = -1 →
      g₁ * g₂ = (-1 : SL(2, F)) * (g₂ * g₁) → False := by
    rintro g₁ ⟨h₁, -, rfl⟩ g₂ ⟨h₂, -, rfl⟩ e₁ e₂ e₃
    obtain ⟨g, hg, hgf⟩ := quaternion_pair_fixed (-1 : SL(2, F)) hc hcc ζ e₁ e₂ e₃
      h₁.2 h₂.2
    exact hbad g hg hgf
  have hcyc : IsCyclic P' := isCyclic_of_no_quaternion_pair_sl2 F hF P' hP'2 hno
  have e1 : ↥(P : Subgroup ↥(signFix ζ)) ≃* ↥P' :=
    Subgroup.equivMapOfInjective _ (signFix ζ).subtype (signFix ζ).subtype_injective
  exact isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective

end SignFix

end CFSG.ClassicalInvolution.Asc77.AscFusion
