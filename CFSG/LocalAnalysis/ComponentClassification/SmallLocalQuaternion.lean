module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.QuaternionCentralizers

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup QuaternionGroup

variable {X : Type*} [Group X]

theorem mul_pow_rearrange {z x y : X} (hzx : Commute z x) (hzy : Commute z y)
    (hxy : Commute x y) (A B C A' B' C' : ℕ) :
    z ^ A * x ^ B * y ^ C * (z ^ A' * x ^ B' * y ^ C') =
      z ^ A * z ^ A' * (x ^ B * x ^ B') * (y ^ C * y ^ C') := by
  have h1 : Commute (y ^ C) (z ^ A') := (hzy.pow_pow A' C).symm
  have h2 : Commute (x ^ B) (z ^ A') := (hzx.pow_pow A' B).symm
  have h3 : Commute (y ^ C) (x ^ B') := (hxy.pow_pow B' C).symm
  calc z ^ A * x ^ B * y ^ C * (z ^ A' * x ^ B' * y ^ C')
      = z ^ A * (x ^ B * (y ^ C * z ^ A')) * x ^ B' * y ^ C' := by simp only [mul_assoc]
    _ = z ^ A * (x ^ B * (z ^ A' * y ^ C)) * x ^ B' * y ^ C' := by rw [h1.eq]
    _ = z ^ A * ((x ^ B * z ^ A') * y ^ C) * x ^ B' * y ^ C' := by simp only [mul_assoc]
    _ = z ^ A * ((z ^ A' * x ^ B) * y ^ C) * x ^ B' * y ^ C' := by rw [h2.eq]
    _ = z ^ A * z ^ A' * (x ^ B * (y ^ C * x ^ B')) * y ^ C' := by simp only [mul_assoc]
    _ = z ^ A * z ^ A' * (x ^ B * (x ^ B' * y ^ C)) * y ^ C' := by rw [h3.eq]
    _ = z ^ A * z ^ A' * (x ^ B * x ^ B') * (y ^ C * y ^ C') := by simp only [mul_assoc]

theorem exists_elementaryAbelian_eight {z x y : X} (hz : z ^ 2 = 1) (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hzx : Commute z x) (hzy : Commute z y) (hxy : Commute x y)
    (hind : ∀ a b c : ℕ, a < 2 → b < 2 → c < 2 → z ^ a * x ^ b * y ^ c = 1 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    ∃ E : Subgroup X, IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ z ∈ E ∧
      E ≤ closure {z, x, y} := by
  have hmod : ∀ w : X, w ^ 2 = 1 → ∀ m : ℕ, w ^ (m % 2) = w ^ m := fun w hw m =>
    (pow_eq_pow_mod m hw).symm
  let f : Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) → X := fun v =>
    z ^ (Multiplicative.toAdd v).1.val * x ^ (Multiplicative.toAdd v).2.1.val *
      y ^ (Multiplicative.toAdd v).2.2.val
  have hf : ∀ v w, f (v * w) = f v * f w := by
    intro v w
    simp only [f, toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add, hmod z hz, hmod x hx,
      hmod y hy, pow_add]
    exact (mul_pow_rearrange hzx hzy hxy _ _ _ _ _ _).symm
  let ψ : Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) →* X :=
    { toFun := f
      map_one' := by simp [f]
      map_mul' := hf }
  have hψ : ∀ v, ψ v = f v := fun v => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    rw [hψ] at hv
    obtain ⟨ha, hb, hc⟩ := hind _ _ _ (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hv
    rw [ZMod.val_eq_zero] at ha hb hc
    exact toAdd_eq_zero.mp (Prod.ext ha (Prod.ext hb hc))
  have hsq : ∀ v : Multiplicative (ZMod 2 × ZMod 2 × ZMod 2), v ^ 2 = 1 := by decide
  refine ⟨ψ.range, ?_, ?_, ⟨Multiplicative.ofAdd (1, 0, 0), ?_⟩, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨_, v, rfl⟩ := a
      obtain ⟨_, w, rfl⟩ := b
      apply Subtype.ext
      change ψ v * ψ w = ψ w * ψ v
      rw [← map_mul, ← map_mul, mul_comm]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
      obtain ⟨_, v, rfl⟩ := a
      apply Subtype.ext
      change ψ v ^ 2 = 1
      rw [← map_pow, hsq, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  · rw [hψ]
    simp only [f, toAdd_ofAdd, show (1 : ZMod 2).val = 1 from rfl,
      show (0 : ZMod 2).val = 0 from rfl, pow_one, pow_zero, mul_one]
  · rintro _ ⟨v, rfl⟩
    rw [hψ]
    exact mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
      (pow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _)

theorem quaternion_factor {W : Subgroup X} {h : ℕ} [NeZero h]
    (e : W ≃* QuaternionGroup (2 * h)) {z : X} (hzW : z ∈ W) (hz1 : z ≠ 1)
    (hzc : ∀ w ∈ W, w * z = z * w) :
    (∀ w ∈ W, (∀ w' ∈ W, w' * w = w * w') → w = 1 ∨ w = z) ∧
      ∃ u ∈ W, ∃ v ∈ W, u * u = z ∧ v * v = z ∧ u * v = z * (v * u) ∧
        ∀ b c : ℕ, b < 2 → c < 2 → (u ^ b * v ^ c = 1 ∨ u ^ b * v ^ c = z) → b = 0 ∧ c = 0 := by
  have hh : 0 < h := Nat.pos_of_ne_zero (NeZero.ne h)
  have hcenter := (CFSG.GroupTheory.quaternion_centralizers (m := 2 * h) (by omega)).2.2.1
  have hcent : ∀ w : W, (∀ w' : W, w' * w = w * w') →
      e w = a 0 ∨ e w = a ((2 * h : ℕ) : ZMod (2 * (2 * h))) := by
    intro w hw
    apply (hcenter (e w)).mp
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hw g']
  have hez : e ⟨z, hzW⟩ = a ((2 * h : ℕ) : ZMod (2 * (2 * h))) := by
    rcases hcent ⟨z, hzW⟩ fun w' => Subtype.ext (hzc w' w'.2) with h0 | h1
    · refine absurd ?_ hz1
      have : (⟨z, hzW⟩ : W) = 1 := e.injective (by rw [h0, map_one]; rfl)
      exact congrArg Subtype.val this
    · exact h1
  refine ⟨fun w hw hwc => ?_, ?_⟩
  · rcases hcent ⟨w, hw⟩ fun w' => Subtype.ext (hwc w' w'.2) with h0 | h1
    · left
      have : (⟨w, hw⟩ : W) = 1 := e.injective (by rw [h0, map_one]; rfl)
      exact congrArg Subtype.val this
    · right
      have : (⟨w, hw⟩ : W) = ⟨z, hzW⟩ := e.injective (by rw [h1, hez])
      exact congrArg Subtype.val this
  have hzsymm : e.symm (a ((2 * h : ℕ) : ZMod (2 * (2 * h)))) = ⟨z, hzW⟩ := by
    rw [← hez, e.symm_apply_apply]
  have hcoe : ∀ g : QuaternionGroup (2 * h),
      ((e.symm g : W) : X) = z ↔ g = a ((2 * h : ℕ) : ZMod (2 * (2 * h))) := by
    intro g
    constructor
    · intro hg
      have h1 : e.symm g = ⟨z, hzW⟩ := Subtype.ext hg
      rw [← hzsymm] at h1
      exact e.symm.injective h1
    · rintro rfl
      rw [hzsymm]
  have hcoe1 : ∀ g : QuaternionGroup (2 * h), ((e.symm g : W) : X) = 1 ↔ g = 1 := by
    intro g
    constructor
    · intro hg
      exact (MulEquiv.map_eq_one_iff e.symm).mp (Subtype.ext hg)
    · rintro rfl
      rw [map_one]
      rfl
  have hval : ∀ k : ℕ, k < 2 * (2 * h) → ((k : ZMod (2 * (2 * h)))).val = k := fun k hk => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have hh0 : (h : ZMod (2 * (2 * h))) ≠ 0 := by
    intro H
    have h1 := congrArg ZMod.val H
    rw [hval h (by omega), ZMod.val_zero] at h1
    omega
  have hhn : (h : ZMod (2 * (2 * h))) ≠ ((2 * h : ℕ) : ZMod (2 * (2 * h))) := by
    intro H
    have h1 := congrArg ZMod.val H
    rw [hval h (by omega), hval (2 * h) (by omega)] at h1
    omega
  refine ⟨e.symm (a (h : ZMod (2 * (2 * h)))), (e.symm _).2, e.symm (xa 0), (e.symm _).2,
    ?_, ?_, ?_, ?_⟩
  · rw [← coe_mul, ← map_mul, a_mul_a, hcoe]
    congr 1
    push_cast
    ring
  · rw [← coe_mul, ← map_mul, xa_mul_xa, hcoe, add_zero, sub_zero]
  · have key : a (h : ZMod (2 * (2 * h))) * xa 0 =
        a ((2 * h : ℕ) : ZMod (2 * (2 * h))) * (xa 0 * a (h : ZMod (2 * (2 * h)))) := by
      rw [a_mul_xa, xa_mul_a, a_mul_xa]
      congr 1
      push_cast
      ring
    have h1 := congrArg (fun g => ((e.symm g : W) : X)) key
    simp only [map_mul, coe_mul] at h1
    rw [h1, hzsymm]
  · intro b c hb hc hbc
    interval_cases b <;> interval_cases c
    · exact ⟨rfl, rfl⟩
    · simp only [pow_zero, pow_one, one_mul] at hbc
      rcases hbc with h1 | h1
      · rw [hcoe1, one_def] at h1
        exact nomatch h1
      · rw [hcoe] at h1
        exact nomatch h1
    · simp only [pow_zero, pow_one, mul_one] at hbc
      rcases hbc with h1 | h1
      · rw [hcoe1, one_def, a.injEq] at h1
        exact absurd h1 hh0
      · rw [hcoe, a.injEq] at h1
        exact absurd h1 hhn
    · simp only [pow_one] at hbc
      rw [← coe_mul, ← map_mul, a_mul_xa] at hbc
      rcases hbc with h1 | h1
      · rw [hcoe1, one_def] at h1
        exact nomatch h1
      · rw [hcoe] at h1
        exact nomatch h1

theorem commuting_quaternion_pair_common_involution_rank_three [Finite X] {U V : Subgroup X}
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) {r s : ℕ} (hr : 3 ≤ r) (hs : 3 ≤ s)
    (hU : Nonempty (U ≃* QuaternionGroup (2 ^ (r - 2))))
    (hV : Nonempty (V ≃* QuaternionGroup (2 ^ (s - 2))))
    {z : X} (hz : orderOf z = 2) (hzU : z ∈ U) (hzV : z ∈ V) :
    U ⊓ V = zpowers z ∧
      (∃ E : Subgroup X, E ≤ U ⊔ V ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ z ∈ E) ∧
      3 ≤ pRank 2 ↥(U ⊔ V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eU⟩ := hU
  obtain ⟨eV⟩ := hV
  obtain ⟨kU, hkU⟩ : ∃ k, 2 ^ (r - 2) = 2 * k :=
    ⟨2 ^ (r - 3), by rw [← pow_succ']; congr 1; omega⟩
  obtain ⟨kV, hkV⟩ : ∃ k, 2 ^ (s - 2) = 2 * k :=
    ⟨2 ^ (s - 3), by rw [← pow_succ']; congr 1; omega⟩
  have : NeZero kU := ⟨by rintro rfl; simp at hkU⟩
  have : NeZero kV := ⟨by rintro rfl; simp at hkV⟩
  rw [hkU] at eU
  rw [hkV] at eV
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hzz : z * z = 1 := by rw [← pow_two, hz2]
  obtain ⟨hcentU, u₁, hu₁, v₁, hv₁, hu₁u₁, hv₁v₁, hu₁v₁, hindU⟩ :=
    quaternion_factor eU hzU hz1 fun w hw => hUV w hw z hzV
  obtain ⟨-, u₂, hu₂, v₂, hv₂, hu₂u₂, hv₂v₂, hu₂v₂, -⟩ :=
    quaternion_factor eV hzV hz1 fun w hw => (hUV z hzU w hw).symm
  have hUVz : ∀ w ∈ U ⊓ V, w = 1 ∨ w = z := fun w hw =>
    hcentU w (mem_inf.mp hw).1 fun w' hw' => hUV w' hw' w (mem_inf.mp hw).2
  have hinter : U ⊓ V = zpowers z := by
    refine le_antisymm (fun w hw => ?_) (zpowers_le.mpr (mem_inf.mpr ⟨hzU, hzV⟩))
    rcases hUVz w hw with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  have hzu₁ : Commute z u₁ := (hUV u₁ hu₁ z hzV).symm
  have hzv₁ : Commute z v₁ := (hUV v₁ hv₁ z hzV).symm
  have hzu₂ : Commute z u₂ := hUV z hzU u₂ hu₂
  have hzv₂ : Commute z v₂ := hUV z hzU v₂ hv₂
  have hu₁u₂ : Commute u₁ u₂ := hUV u₁ hu₁ u₂ hu₂
  have hv₁v₂ : Commute v₁ v₂ := hUV v₁ hv₁ v₂ hv₂
  have hx2 : (u₁ * u₂) ^ 2 = 1 := by
    rw [hu₁u₂.mul_pow, pow_two, pow_two, hu₁u₁, hu₂u₂, ← pow_two, hz2]
  have hy2 : (v₁ * v₂) ^ 2 = 1 := by
    rw [hv₁v₂.mul_pow, pow_two, pow_two, hv₁v₁, hv₂v₂, ← pow_two, hz2]
  have hzx : Commute z (u₁ * u₂) := hzu₁.mul_right hzu₂
  have hzy : Commute z (v₁ * v₂) := hzv₁.mul_right hzv₂
  have hxy : Commute (u₁ * u₂) (v₁ * v₂) := by
    have hzA : Commute z (v₁ * u₁) := hzv₁.mul_right hzu₁
    calc u₁ * u₂ * (v₁ * v₂) = u₁ * (u₂ * v₁) * v₂ := by simp only [mul_assoc]
      _ = u₁ * (v₁ * u₂) * v₂ := by rw [(hUV v₁ hv₁ u₂ hu₂).symm]
      _ = (u₁ * v₁) * (u₂ * v₂) := by simp only [mul_assoc]
      _ = z * (v₁ * u₁) * (z * (v₂ * u₂)) := by rw [hu₁v₁, hu₂v₂]
      _ = z * ((v₁ * u₁) * z) * (v₂ * u₂) := by simp only [mul_assoc]
      _ = z * (z * (v₁ * u₁)) * (v₂ * u₂) := by rw [← hzA.eq]
      _ = (v₁ * u₁) * (v₂ * u₂) := by rw [← mul_assoc z z, hzz, one_mul]
      _ = v₁ * (u₁ * v₂) * u₂ := by simp only [mul_assoc]
      _ = v₁ * (v₂ * u₁) * u₂ := by rw [hUV u₁ hu₁ v₂ hv₂]
      _ = v₁ * v₂ * (u₁ * u₂) := by simp only [mul_assoc]
  have hind : ∀ a b c : ℕ, a < 2 → b < 2 → c < 2 →
      z ^ a * (u₁ * u₂) ^ b * (v₁ * v₂) ^ c = 1 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c ha hb hc habc
    rw [hu₁u₂.mul_pow, hv₁v₂.mul_pow] at habc
    have hcross : Commute (u₂ ^ b) (v₁ ^ c) := (Commute.pow_pow (hUV v₁ hv₁ u₂ hu₂).symm b c)
    have hmem : z ^ a * u₁ ^ b * v₁ ^ c ∈ U ⊓ V := by
      refine mem_inf.mpr ⟨mul_mem (mul_mem (pow_mem hzU a) (pow_mem hu₁ b)) (pow_mem hv₁ c), ?_⟩
      have e : z ^ a * u₁ ^ b * v₁ ^ c = (u₂ ^ b * v₂ ^ c)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc z ^ a * u₁ ^ b * v₁ ^ c * (u₂ ^ b * v₂ ^ c) =
            z ^ a * u₁ ^ b * (v₁ ^ c * u₂ ^ b) * v₂ ^ c := by simp only [mul_assoc]
          _ = z ^ a * u₁ ^ b * (u₂ ^ b * v₁ ^ c) * v₂ ^ c := by rw [hcross.eq]
          _ = z ^ a * (u₁ ^ b * u₂ ^ b) * (v₁ ^ c * v₂ ^ c) := by simp only [mul_assoc]
          _ = 1 := habc
      rw [e]
      exact inv_mem (mul_mem (pow_mem hu₂ b) (pow_mem hv₂ c))
    have hbc : b = 0 ∧ c = 0 := by
      refine hindU b c hb hc ?_
      interval_cases a
      · rw [pow_zero, one_mul] at hmem
        exact hUVz _ hmem
      · rw [pow_one] at hmem
        rcases hUVz _ hmem with h1 | h1
        · right
          calc u₁ ^ b * v₁ ^ c = z * (z * u₁ ^ b * v₁ ^ c) := by
                rw [← mul_assoc z, ← mul_assoc z, hzz, one_mul]
            _ = z := by rw [h1, mul_one]
        · left
          calc u₁ ^ b * v₁ ^ c = z * (z * u₁ ^ b * v₁ ^ c) := by
                rw [← mul_assoc z, ← mul_assoc z, hzz, one_mul]
            _ = 1 := by rw [h1, hzz]
    obtain ⟨rfl, rfl⟩ := hbc
    refine ⟨?_, rfl, rfl⟩
    simp only [pow_zero, mul_one] at habc
    interval_cases a
    · rfl
    · exact absurd (by simpa using habc) hz1
  obtain ⟨E, hE, hcard, hzE, hEcl⟩ := exists_elementaryAbelian_eight hz2 hx2 hy2 hzx hzy hxy hind
  have hEUV : E ≤ U ⊔ V := by
    refine hEcl.trans (closure_le _ |>.mpr ?_)
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact mem_sup_left hzU
    · exact mul_mem_sup hu₁ hu₂
    · exact mul_mem_sup hv₁ hv₂
  refine ⟨hinter, ⟨E, hEUV, hE, hcard, hzE⟩, ?_⟩
  have hbdd : BddAbove {k : ℕ | ∃ A : Subgroup ↥(U ⊔ V), IsElementaryAbelian 2 A ∧
      Nat.card A = 2 ^ k} := by
    refine ⟨Nat.card ↥(U ⊔ V), ?_⟩
    rintro k ⟨A, -, hA⟩
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ = Nat.card A := hA.symm
      _ ≤ Nat.card ↥(U ⊔ V) := Nat.card_le_card_of_injective _ Subtype.val_injective
  have : IsElementaryAbelian 2 E := hE
  refine le_csSup hbdd ⟨E.subgroupOf (U ⊔ V), IsElementaryAbelian.subgroupOf hEUV, ?_⟩
  rw [Nat.card_congr (subgroupOfEquivOfLe hEUV).toEquiv, hcard]
  norm_num

end CFSG.ComponentClassification.SmallLocal
