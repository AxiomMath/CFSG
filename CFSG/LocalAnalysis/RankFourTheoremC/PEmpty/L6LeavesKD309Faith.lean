module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Linear
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup

variable {Y V : Type} [Group Y] [AddCommGroup V] [Module (ZMod 2) V]

def vecStab (ρ : Representation (ZMod 2) Y V) (v : V) : Subgroup Y where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply]
    change ρ a v = v at ha
    change ρ b v = v at hb
    rw [hb, ha]
  inv_mem' {a} ha := by
    change ρ a⁻¹ v = v
    change ρ a v = v at ha
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

theorem fixed_of_mem_zpowers {ρ : Representation (ZMod 2) Y V} {z : Y} {v : V}
    (hv : ρ z v = v) {h : Y} (hh : h ∈ zpowers z) : ρ h v = v :=
  (zpowers_le.mpr (show z ∈ vecStab ρ v from hv)) hh

theorem ker_inf_range_eq_bot [Finite Y] {ρ : Representation (ZMod 2) Y V} {z : Y}
    (hz : orderOf z = 5) :
    Disjoint (LinearMap.ker (ρ z - 1)) (LinearMap.range (ρ z - 1)) := by
  classical
  letI : Fintype (zpowers z) := Fintype.ofFinite _
  have hodd : Odd (Fintype.card (zpowers z)) := by
    rw [Fintype.card_eq_nat_card, Nat.card_zpowers, hz]
    decide
  refine Disjoint.mono ?_ ?_ (disjoint_fixSub_commSub ρ (zpowers z) hodd)
  · intro v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact mem_fixSub.mpr fun h hh => fixed_of_mem_zpowers hv hh
  · rintro _ ⟨w, rfl⟩
    exact apply_sub_one_mem_commSub (mem_zpowers z) w

theorem range_invariant {ρ : Representation (ZMod 2) Y V} {z g : Y} (hg : g * z = z * g)
    {v : V} (hv : v ∈ LinearMap.range (ρ z - 1)) : ρ g v ∈ LinearMap.range (ρ z - 1) := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨ρ g w, ?_⟩
  have h : ρ g * ρ z = ρ z * ρ g := by rw [← map_mul, ← map_mul, hg]
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, h]

theorem faithful_on_range [Finite Y] {ρ : Representation (ZMod 2) Y V}
    (hker : IsPGroup 2 ρ.ker) {P : Subgroup Y} (hP : IsPGroup 5 P) {z : Y} (hzP : z ∈ P)
    (hz : orderOf z = 5) (hzc : ∀ g ∈ P, g * z = z * g)
    (hZ : ∀ w ∈ P, (∀ g ∈ P, g * w = w * g) → w ^ 5 = 1 → w ∈ zpowers z) {g : Y} (hgP : g ∈ P)
    (hg : ∀ v ∈ LinearMap.range (ρ z - 1), ρ g v = v) : g = 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_contra hg1
  let K : Subgroup P :=
    { carrier := {k | ∀ v ∈ LinearMap.range (ρ z - 1), ρ (k : Y) v = v}
      one_mem' := by intro v _; simp
      mul_mem' := by
        intro a b ha hb v hv
        change ρ ((a : Y) * (b : Y)) v = v
        rw [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
      inv_mem' := by
        intro a ha v hv
        change ρ ((a : Y)⁻¹) v = v
        conv_lhs => rw [← ha v hv]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  haveI hKn : K.Normal := by
    refine ⟨fun k hk x v hv => ?_⟩
    have hx : ∀ u ∈ LinearMap.range (ρ z - 1), ρ (x : Y) u ∈ LinearMap.range (ρ z - 1) :=
      fun u hu => range_invariant (hzc x x.2) hu
    have hx' : ∀ u ∈ LinearMap.range (ρ z - 1), ρ ((x : Y)⁻¹) u ∈ LinearMap.range (ρ z - 1) :=
      fun u hu => range_invariant (g := (x : Y)⁻¹)
        (by
          have := hzc x x.2
          calc (x : Y)⁻¹ * z = (x : Y)⁻¹ * (z * x) * (x : Y)⁻¹ := by group
            _ = (x : Y)⁻¹ * (x * z) * (x : Y)⁻¹ := by rw [this]
            _ = z * (x : Y)⁻¹ := by group) hu
    change ρ ((x : Y) * (k : Y) * (x : Y)⁻¹) v = v
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    have h1 := hk (ρ ((x : Y)⁻¹) v) (hx' v hv)
    rw [h1, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hKne : K ≠ ⊥ := by
    intro h
    have : (⟨g, hgP⟩ : P) ∈ K := fun v hv => hg v hv
    rw [h, Subgroup.mem_bot] at this
    exact hg1 (congrArg Subtype.val this)
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hN : K ⊓ center ↥P ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hKne
  have hN5 : IsPGroup 5 ↥(K ⊓ center ↥P) := hP.to_subgroup _
  obtain ⟨n, hn⟩ := hN5.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hN
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hn
  have h5 : 5 ∣ Nat.card ↥(K ⊓ center ↥P) := by
    rw [hn]
    exact dvd_pow_self 5 hn0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hwK : (w : P) ∈ K := w.2.1
  have hwc : (w : P) ∈ center ↥P := w.2.2
  have hwY : ((w : P) : Y) ∈ P := (w : P).2
  have hwo : orderOf (((w : P) : Y)) = 5 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hwcomm : ∀ x ∈ P, x * ((w : P) : Y) = ((w : P) : Y) * x := by
    intro x hx
    have := Subgroup.mem_center_iff.mp hwc ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hw5 : ((w : P) : Y) ^ 5 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one _
  have hwz : ((w : P) : Y) ∈ zpowers z := hZ _ hwY hwcomm hw5
  have hzcard : Nat.card (zpowers z) = 5 := by rw [Nat.card_zpowers, hz]
  have hzw : zpowers ((w : P) : Y) = zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hwz) ?_
    rw [hzcard, Nat.card_zpowers, hwo]
  have hzfix : ∀ v ∈ LinearMap.range (ρ z - 1), ρ z v = v := by
    intro v hv
    refine fixed_of_mem_zpowers (z := ((w : P) : Y)) (hwK v hv) ?_
    rw [hzw]
    exact mem_zpowers z
  have hzone : ρ z = 1 := by
    refine LinearMap.ext fun u => ?_
    have h1 : (ρ z - 1) u ∈ LinearMap.range (ρ z - 1) := ⟨u, rfl⟩
    have h2 : (ρ z - 1) u ∈ LinearMap.ker (ρ z - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hzfix _ h1
    have h3 := (Submodule.disjoint_def.mp (ker_inf_range_eq_bot (ρ := ρ) hz)) _ h2 h1
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h3
    exact h3
  have hzker : z ∈ ρ.ker := by rw [MonoidHom.mem_ker]; exact hzone
  obtain ⟨k, hk⟩ := hker ⟨z, hzker⟩
  have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : 5 ∣ 2 ^ k := hz ▸ orderOf_dvd_of_pow_eq_one hk'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
