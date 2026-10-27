module

public import CFSG.ClassicalInvolution.Q3.TL4E3E4Sec
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Good

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint
open scoped commutatorElement

theorem E3.exists_lift_three {X : Type} [Group X] (hZ2 : IsPGroup 2 ↥(Subgroup.center X))
    {t : X} {yb : X ⧸ Subgroup.center X} (hy3 : yb ^ 3 = 1)
    (hyt : yb * QuotientGroup.mk' (Subgroup.center X) t =
      QuotientGroup.mk' (Subgroup.center X) t * yb) :
    ∃ y : X, y ^ 3 = 1 ∧ QuotientGroup.mk' (Subgroup.center X) y = yb ∧ y * t = t * y := by
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) yb
  have hy3Z : y₀ ^ 3 ∈ Subgroup.center X := by
    have h : QuotientGroup.mk' (Subgroup.center X) (y₀ ^ 3) = 1 := by rw [map_pow]; exact hy3
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  obtain ⟨m, hm⟩ := hZ2 ⟨y₀ ^ 3, hy3Z⟩
  have hm' : (y₀ ^ 3) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h4 : (4 : ℕ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  have hyy : (y₀ ^ 4 ^ m) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h4, pow_mul, hm', one_pow]
  have hπy : QuotientGroup.mk' (Subgroup.center X) (y₀ ^ 4 ^ m) =
      QuotientGroup.mk' (Subgroup.center X) y₀ := by
    rw [map_pow]
    have h41 : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [← Nat.div_add_mod (4 ^ m) 3, h41, pow_add, pow_mul, hy3, one_pow, one_mul, pow_one]
  generalize y₀ ^ 4 ^ m = y at hyy hπy
  refine ⟨y, hyy, hπy, ?_⟩
  have hν : y * t * y⁻¹ * t⁻¹ ∈ Subgroup.center X := by
    have h : QuotientGroup.mk' (Subgroup.center X) (y * t * y⁻¹ * t⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπy, hyt]
      group
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  generalize hνdef : y * t * y⁻¹ * t⁻¹ = ν at hν
  have hyt' : y * t = ν * t * y := by rw [← hνdef]; group
  have hk : ∀ k : ℕ, y ^ k * t = ν ^ k * t * y ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : y * ν ^ k = ν ^ k * y :=
        Subgroup.mem_center_iff.mp ((Subgroup.center X).pow_mem hν k) y
      calc y ^ (k + 1) * t = y * (y ^ k * t) := by rw [pow_succ', mul_assoc]
        _ = y * (ν ^ k * t * y ^ k) := by rw [ih]
        _ = ν ^ k * (y * t) * y ^ k := by
          rw [← mul_assoc, ← mul_assoc, hc]
          group
        _ = ν ^ (k + 1) * t * y ^ (k + 1) := by
          rw [hyt']
          group
  have hν3 : ν ^ 3 = 1 := by
    have h := hk 3
    rw [hyy, one_mul, mul_one] at h
    exact mul_eq_right.mp h.symm
  have hν1 : ν = 1 := by
    obtain ⟨j, hj⟩ := hZ2 ⟨ν, hν⟩
    have hj' : ν ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hd1 : orderOf ν ∣ Nat.gcd 3 (2 ^ j) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hν3) (orderOf_dvd_of_pow_eq_one hj')
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right j (by norm_num))] at hd1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)
  rw [hyt', hν1, one_mul]

@[expose] def TightE4NoGood : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (t : X),
    TightDatum R S t → TightCls X R S t → ¬ TightInO2 t → TightE4 X → ¬ GoodThreeElement R t


theorem tightE4NoGood_of
    (hng : ∀ (M : Type) [Group M] [Finite M], PhilipHall.QuaternionBridge.ExLie M →
      E4QuatNoGood M) : TightE4NoGood := by
  intro X _ _ R S t hd hc hO2 hE4 hgood
  obtain ⟨x, k, hxC, hx3, ⟨r, hrR, hxr⟩, hxD⟩ := hgood
  obtain ⟨-, -, -, -, -, -, hZ, -, hM⟩ := E3.e4_center hd hc hO2 hE4
  have hO : TightOddCent t := secIdE4OddCent_proved X R S t hd hc hO2 hZ hM
  have hR2 : IsPGroup 2 ↥R := hd.isPGroup_of_oddCent hO
  have hK : tightCore R = R := tightCore_eq_self_of_isPGroup hR2
  have hQ := Vtx.quatTwinDatum_quot hd hc hO2 hZ hM
  rw [hK] at hQ
  have hZ2 : IsPGroup 2 ↥(Subgroup.center X) := Vtx.isPGroup_center_of_oddFree hc.2.2
  set π := QuotientGroup.mk' (Subgroup.center X) with hπ
  have hxK : conjSub (π x) (R.map π) = R.map π := by
    rw [conjSub_map, conjSub_eq_of_mem_normalizer (hd.le_normalizer hxC)]
  have hxr' : x * r ≠ r * x := by
    intro h
    apply hxr
    rw [commutatorElement_def, h, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hact : ∃ c ∈ R.map π, π x * c ≠ c * π x := by
    refine ⟨π r, Subgroup.mem_map_of_mem π hrR, fun h => hxr' ?_⟩
    have hmem : x * r * x⁻¹ * r⁻¹ ∈ R ⊓ Subgroup.center X := by
      refine ⟨R.mul_mem ?_ (R.inv_mem hrR), ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hxC) r).mp hrR
        exact h1
      · have h1 : π (x * r * x⁻¹ * r⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
          group
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hRZ := PhilipHall.QuaternionBridge.core_inf_eq_bot hd hZ2
      (Vtx.not_mem_center_of_not_tightInO2 hd.order hO2)
    rw [hK, Subgroup.eq_bot_iff_forall] at hRZ
    have h1 := hRZ _ hmem
    calc x * r = x * r * x⁻¹ * r⁻¹ * (r * x) := by group
      _ = r * x := by rw [h1, one_mul]
  obtain ⟨yb, hy3, hyC, hxy⟩ :=
    hng _ hM _ _ hQ (π x) k (by rw [← map_pow, hx3, map_one]) hxK hact
  have hyt : yb * π t = π t * yb := hyC _ (Subgroup.mem_map_of_mem π hd.mem_right)
  obtain ⟨y, hy3', rfl, hyt'⟩ := E3.exists_lift_three hZ2 hy3 hyt
  have hyR : ∀ r ∈ R, y * r = r * y := by
    intro r hr
    have hyr : π y * π r = π r * π y := hyC _ (Subgroup.mem_map_of_mem π hr)
    obtain ⟨y', -, hyy', hy'r⟩ := E3.exists_lift_three hZ2 hy3 hyr
    obtain ⟨z, hz, hzy⟩ : ∃ z ∈ Subgroup.center X, y' = z * y := by
      refine ⟨y' * y⁻¹, ?_, by group⟩
      have h1 : π (y' * y⁻¹) = 1 := by rw [map_mul, map_inv, hyy', mul_inv_cancel]
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [hzy] at hy'r
    have hzr : r * z = z * r := Subgroup.mem_center_iff.mp hz r
    have h2 : z * (y * r) = z * (r * y) := by
      calc z * (y * r) = z * y * r := by group
        _ = r * (z * y) := hy'r
        _ = r * z * y := by group
        _ = z * (r * y) := by rw [hzr]; group
    exact mul_left_cancel h2
  have hyC' : y ∈ Subgroup.centralizer ({t} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyt'
  have h1 := hxD y hyC' fun r hr => by
    rw [commutatorElement_def, hyR r hr, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  unfold TightOddCent at hO
  rw [hO, Subgroup.mem_bot, commutatorElement_def] at h1
  apply hxy
  have h2 : x * y = y * x := by
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  rw [← map_mul, ← map_mul, h2]

end CFSG.ClassicalInvolution.Q3.TL4
