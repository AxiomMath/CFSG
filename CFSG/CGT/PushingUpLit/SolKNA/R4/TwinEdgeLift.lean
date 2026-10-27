module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThm4
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin

section Lift

variable {G : Type} [Group G] [Finite G]

theorem commutator_mul_center (a b u v : G) (hu : u ∈ Subgroup.center G)
    (hv : v ∈ Subgroup.center G) :
    (a * u) * (b * v) * (a * u)⁻¹ * (b * v)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hu' : ∀ g : G, g * u = u * g := Subgroup.mem_center_iff.mp hu
  have hv' : ∀ g : G, g * v = v * g := Subgroup.mem_center_iff.mp hv
  have hxy : (a * u) * (b * v) = (a * b) * (u * v) := by
    calc (a * u) * (b * v) = a * (u * b) * v := by group
      _ = a * (b * u) * v := by rw [← hu' b]
      _ = (a * b) * (u * v) := by group
  have hyx : (b * v) * (a * u) = (b * a) * (u * v) := by
    calc (b * v) * (a * u) = b * (v * a) * u := by group
      _ = b * (a * v) * u := by rw [← hv' a]
      _ = (b * a) * (v * u) := by group
      _ = (b * a) * (u * v) := by rw [← hv' u]
  calc (a * u) * (b * v) * (a * u)⁻¹ * (b * v)⁻¹ =
        ((a * u) * (b * v)) * ((b * v) * (a * u))⁻¹ := by group
    _ = ((a * b) * (u * v)) * ((b * a) * (u * v))⁻¹ := by rw [hxy, hyx]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_of_map_center_eq {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ) {J M : Subgroup G}
    (hJ : J ∈ Δ) (hM : M ∈ Δ)
    (hmap : J.map (QuotientGroup.mk' (Subgroup.center G)) =
      M.map (QuotientGroup.mk' (Subgroup.center G)))
    {x y : G} (hx : x ∈ J) (hy : y ∈ J) (h4 : 4 ∣ orderOf (x * y * x⁻¹ * y⁻¹)) : J = M := by
  by_contra hne
  have hΩ4 := (hΩ.omega4 J hJ M hM hne).1
  have hmem : ∀ w ∈ J, ∃ m ∈ M, m⁻¹ * w ∈ Subgroup.center G := by
    intro w hw
    have : QuotientGroup.mk' (Subgroup.center G) w ∈
        M.map (QuotientGroup.mk' (Subgroup.center G)) :=
      hmap ▸ Subgroup.mem_map_of_mem _ hw
    obtain ⟨m, hm, hmw⟩ := this
    refine ⟨m, hm, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hmw
    exact hmw
  obtain ⟨m₁, hm₁, hz₁⟩ := hmem x hx
  obtain ⟨m₂, hm₂, hz₂⟩ := hmem y hy
  have hxm : x = m₁ * (m₁⁻¹ * x) := by group
  have hym : y = m₂ * (m₂⁻¹ * y) := by group
  have hc : x * y * x⁻¹ * y⁻¹ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by
    rw [hxm, hym]
    simpa only [mul_inv_cancel_left] using
      commutator_mul_center m₁ m₂ (m₁⁻¹ * x) (m₂⁻¹ * y) hz₁ hz₂
  have hcM : x * y * x⁻¹ * y⁻¹ ∈ M := by
    rw [hc]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
  have hcJ : x * y * x⁻¹ * y⁻¹ ∈ J :=
    J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy)
  have hcmem : x * y * x⁻¹ * y⁻¹ ∈ J ⊓ M := Subgroup.mem_inf.mpr ⟨hcJ, hcM⟩
  have hdvd : orderOf (x * y * x⁻¹ * y⁻¹) ∣ Nat.card ↥(J ⊓ M) := by
    have := orderOf_dvd_natCard (⟨_, hcmem⟩ : ↥(J ⊓ M))
    rwa [Subgroup.orderOf_mk] at this
  have h4d : 2 ^ 2 ∣ Nat.card ↥(J ⊓ M) := by
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [← this]
    exact h4.trans hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp h4d
  omega

end Lift

section QuatComm

theorem quaternion_comm_a_xa {n : ℕ} [NeZero n] :
    (QuaternionGroup.a 1 : QuaternionGroup n) * QuaternionGroup.xa 0 *
      (QuaternionGroup.a 1)⁻¹ * (QuaternionGroup.xa 0)⁻¹ = QuaternionGroup.a 2 := by
  have h2n : (2 : ZMod (2 * n)) * (n : ZMod (2 * n)) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 * n)
  have e1 : (QuaternionGroup.a 1 : QuaternionGroup n)⁻¹ = QuaternionGroup.a (-1) := rfl
  have e2 : (QuaternionGroup.xa 0 : QuaternionGroup n)⁻¹ =
      QuaternionGroup.xa ((n : ZMod (2 * n)) + 0) := rfl
  rw [e1, e2, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa]
  congr 1
  linear_combination h2n

theorem orderOf_quaternion_a_two {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    orderOf (QuaternionGroup.a 2 : QuaternionGroup n) = n := by
  rw [QuaternionGroup.orderOf_a]
  have hval : (2 : ZMod (2 * n)).val = 2 := by
    rw [show (2 : ZMod (2 * n)) = ((2 : ℕ) : ZMod (2 * n)) by norm_num, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hval, show Nat.gcd (2 * n) 2 = 2 from Nat.gcd_eq_right (dvd_mul_right 2 n)]
  omega

end QuatComm

section MemberComm

variable {r : ℕ} {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

theorem F2ConfigR.exists_commutator_four_dvd (hr : 4 ≤ r) (hc : F2ConfigR r J L L₀)
    {K : Subgroup G} (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) :
    ∃ x ∈ K, ∃ y ∈ K, 4 ∣ orderOf (x * y * x⁻¹ * y⁻¹) := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨e⟩ := hc.min.hyp.quat K hK _ (isSylow2In_map_sylow K S)
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  refine ⟨((e.symm (QuaternionGroup.a 1) : ↥((S : Subgroup K).map K.subtype)) : G),
    Subgroup.map_subtype_le _ (e.symm (QuaternionGroup.a 1)).2,
    ((e.symm (QuaternionGroup.xa 0) : ↥((S : Subgroup K).map K.subtype)) : G),
    Subgroup.map_subtype_le _ (e.symm (QuaternionGroup.xa 0)).2, ?_⟩
  have hcomm : (((e.symm (QuaternionGroup.a 1) : ↥((S : Subgroup K).map K.subtype)) : G) *
      ((e.symm (QuaternionGroup.xa 0) : ↥((S : Subgroup K).map K.subtype)) : G) *
      ((e.symm (QuaternionGroup.a 1) : ↥((S : Subgroup K).map K.subtype)) : G)⁻¹ *
      ((e.symm (QuaternionGroup.xa 0) : ↥((S : Subgroup K).map K.subtype)) : G)⁻¹) =
      ((e.symm (QuaternionGroup.a 2) : ↥((S : Subgroup K).map K.subtype)) : G) := by
    have h := congrArg (fun q : QuaternionGroup (2 ^ (r - 2)) =>
      ((e.symm q : ↥((S : Subgroup K).map K.subtype)) : G))
      (quaternion_comm_a_xa (n := 2 ^ (r - 2)))
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h
  rw [hcomm, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
    orderOf_quaternion_a_two (n := 2 ^ (r - 2)) (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega))]
  calc 4 = 2 ^ 2 := by norm_num
    _ ∣ 2 ^ (r - 2) := pow_dvd_pow 2 (by omega)

end MemberComm

end CFSG.CGT.PushingUpLit.SolKNA.R4
