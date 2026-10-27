module

public import CFSG.ClassicalInvolution.Uniform.U4Inner
public import CFSG.ClassicalInvolution.Uniform.U4Wiel2
public import CFSG.ClassicalInvolution.Asc77.AscSix66Aux

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem exists_sq_eq_of_isSylow2In {K V : Subgroup F} {z : F} (hK : Mem3 K z)
    (hV : IsSylow2In V K) : ∃ a ∈ V, a * a = z := by
  obtain ⟨a, haV, ha4⟩ := IsQuatSub.exists_orderOf_four (hK.isQuatSub_of_isSylow2In hV)
  refine ⟨a, haV, ?_⟩
  have h1 : (a * a) * (a * a) = 1 := by
    have : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
    calc (a * a) * (a * a) = a ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := this
  rcases (hK.isUniqueInvolution).unique (a * a) (K.mul_mem (hV.1 haV) (hV.1 haV)) h1 with h | h
  · exfalso
    have : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [ha4] at this
    omega
  · exact h

theorem exists_sq_eq_comm_of_trivial {K R : Subgroup F} {z t : F} (hK : Mem3 K z)
    (hR2 : IsPGroup 2 R) (hRK : IsSylow2In (R ⊓ K) K) (htR : t ∈ R)
    (hT0 : ∀ x ∈ K, ⁅t, x⁆ ∈ oddCoreOf K) : ∃ a ∈ R ⊓ K, a * a = z ∧ t * a = a * t := by
  obtain ⟨a, haR, ha2⟩ := exists_sq_eq_of_isSylow2In hK hRK
  refine ⟨a, haR, ha2, ?_⟩
  have h1 : t * a * t⁻¹ * a⁻¹ ∈ oddCoreOf K := by
    have := hT0 a haR.2
    rwa [commutatorElement_def] at this
  have h2 : t * a * t⁻¹ * a⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem htR haR.1) (R.inv_mem htR)) (R.inv_mem haR.1)
  have h3 : t * a * t⁻¹ * a⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
      (hR2.to_le (Subgroup.zpowers_le.mpr h2))
  calc t * a = (t * a * t⁻¹ * a⁻¹) * a * t := by group
    _ = a * t := by rw [h3]; group

omit [Finite F] in
theorem mul_self_eq_of_orderOf_four {J : Subgroup F} {t v : F} (hJt : IsUniqueInvolution J t)
    (hvJ : v ∈ J) (hv4 : orderOf v = 4) : v * v = t := by
  have hv22 : (v * v) * (v * v) = 1 := by
    have : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
    simpa [pow_succ, mul_assoc] using this
  rcases hJt.unique (v * v) (J.mul_mem hvJ hvJ) hv22 with h | h
  · exfalso
    have : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hv4] at this
    omega
  · exact h

omit [Finite F] in
theorem isPGroup_zpowers_of_orderOf_four {v : F} (hv4 : orderOf v = 4) :
    IsPGroup 2 (Subgroup.zpowers v) := by
  refine IsPGroup.of_card (n := 2) ?_
  rw [Nat.card_zpowers, hv4]
  norm_num

theorem nontrivAction {K : Subgroup F} {z : F} (hK : Mem3 K z)
    {J : Subgroup F}
    {t : F} (hJ : Mem3 J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J)
    (hv4 : orderOf v = 4) (hvz : v * z = z * v) (hvK : v * v ∈ Subgroup.normalizer (K : Set F))
    (hv : v ∉ Subgroup.normalizer (K : Set F)) : ¬ ∀ k ∈ K, ⁅v * v, k⁆ ∈ oddCoreOf K := by
  intro hT0
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) := isPGroup_zpowers_of_orderOf_four hv4
  have hvv : v * v = t := mul_self_eq_of_orderOf_four (hJ.isUniqueInvolution) hvJ hv4
  obtain ⟨R, hR2, hvR, -, hRK, -, hRcomm, hRinv⟩ :=
    exists_twin_sylow hK hv2 hvz (conjSub_inv_ne hv) hvK
  have htR : t ∈ R := hvv ▸ R.mul_mem hvR hvR
  have hT0' : ∀ x ∈ K, ⁅t, x⁆ ∈ oddCoreOf K := by
    intro x hx
    rw [← hvv]
    exact hT0 x hx
  obtain ⟨a₀, ha₀, ha₀2, hta₀⟩ := exists_sq_eq_comm_of_trivial hK hR2 hRK htR hT0'
  have hv3 : 3 ≤ Nat.card (Subgroup.zpowers v) := by rw [Nat.card_zpowers, hv4]; omega
  have hzJ : z ∈ Subgroup.normalizer (J : Set F) :=
    hJ.mem_normalizer_of_commute_of_mem_noncentral hvJ hv2 hv3 hvz.symm
  have hZ : (∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) → False := fun hζ =>
    false_of_trivBoth hK hJ hne hvJ hvv hvz hzJ hvK hv hζ hT0 hR2 ha₀ hRinv ha₀2 hta₀
  obtain ⟨k, hkK, hk2, hkact⟩ :=
    exists_inner_order_four hK hJ hne hvJ hv2 hv4 hvz hv hRcomm hRinv ha₀ ha₀2 hta₀ hZ
  refine hK.not_forall_comm_of_sq_eq hkK hk2 ?_
  intro u hu
  have hA := hT0' u hu
  have hB := hkact u hu
  have e : ⁅u, k⁆ = (⁅t, u⁆)⁻¹ * (t * u * t⁻¹ * (k * u * k⁻¹)⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h1 : ⁅u, k⁆ ∈ oddCoreOf K := by
    rw [e]
    exact (oddCoreOf K).mul_mem ((oddCoreOf K).inv_mem hA) hB
  rw [← commutatorElement_inv]
  exact (oddCoreOf K).inv_mem h1

end CFSG.ClassicalInvolution.Uniform.U4
