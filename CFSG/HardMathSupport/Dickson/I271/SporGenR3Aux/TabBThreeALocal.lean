module


public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeCore
public import Certificates.Certificate17575
public import Certificates.Data.TabBThreeL1Levels

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

open CFSG.Monster.B.Classical.E6Adjoint CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Fischer
open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std CFSG.Monster.B.E6.StdF4
open CFSG.LieType.Chevalley.C2E6Overlap (K barHom)

theorem eq_of_mem_rootClass_of_inverts {x : stdGroup} (hx : x ∈ rootClass)
    (hinv : x * (rootInv * tMinus) * x⁻¹ = (rootInv * tMinus)⁻¹) :
    x = rootInv ∨ x = tMinus ∨ x = rootInv * tMinus * rootInv :=
  Certificates.certificate17575 hx hinv

theorem braid_of_pow_three {G : Type*} [Group G] {p q : G} (hp : p * p = 1) (hq : q * q = 1)
    (h3 : (p * q) ^ 3 = 1) : p * q * p = q * p * q := by
  have hqi : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have h : p * q * p * (q * p * q) = 1 := by
    rw [← h3, pow_three]
    group
  rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev, mul_inv_rev, hqi, hpi, mul_assoc]

open CFSG.HardMathSupport.Dickson.I271.TabBThreeL1 (eq_of_mem_rootClass_of_inverts
  braid_of_pow_three)

end CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.E6.StdF4
open CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar)
open CFSG.HardMathSupport.Dickson.I271.TabBThreeL1 (eq_of_mem_rootClass_of_inverts
  braid_of_pow_three)

theorem tabBThree_pt_inverts (H : ∀ x : CVert, LocalHom x)
    {u a b y : CVert} (ha : a ∈ cgraph.neighborSet u) (hb : b ∈ cgraph.neighborSet u)
    (hy : y ∈ cgraph.neighborSet u)
    (hinv : clabelS y * (clabelS a * clabelS b) * clabelS y = (clabelS a * clabelS b)⁻¹) :
    (H u).pt ⟨y, hy⟩ * ((H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩) * (H u).pt ⟨y, hy⟩ =
      ((H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩)⁻¹ := by
  obtain ⟨A, hAv, hA⟩ : ∃ A : (H u).stab, (A : Shat) = clabelS a ∧
      (H u).rho A = (H u).pt ⟨a, ha⟩ := ⟨_, rfl, rho_clabelS H ha⟩
  obtain ⟨B, hBv, hB⟩ : ∃ B : (H u).stab, (B : Shat) = clabelS b ∧
      (H u).rho B = (H u).pt ⟨b, hb⟩ := ⟨_, rfl, rho_clabelS H hb⟩
  obtain ⟨Y, hYv, hY⟩ : ∃ Y : (H u).stab, (Y : Shat) = clabelS y ∧
      (H u).rho Y = (H u).pt ⟨y, hy⟩ := ⟨_, rfl, rho_clabelS H hy⟩
  have hinvS : Y * (A * B) * Y = (A * B)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hAv, hBv, hYv]
    exact hinv
  have hAB' : (H u).rho (A * B) = (H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩ := by
    rw [map_mul, hA, hB]
  have h1 : (H u).rho (Y * (A * B) * Y) =
      (H u).pt ⟨y, hy⟩ * ((H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩) * (H u).pt ⟨y, hy⟩ := by
    rw [map_mul, map_mul, hAB', hY]
  have h2 : (H u).rho ((A * B)⁻¹) = ((H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩)⁻¹ := by
    rw [map_inv, hAB']
  exact h1.symm.trans ((congrArg (H u).rho hinvS).trans h2)

theorem tabBThree_orderOf_pt_mul_pt (H : ∀ x : CVert, LocalHom x)
    {u a b : CVert} (ha : a ∈ cgraph.neighborSet u) (hb : b ∈ cgraph.neighborSet u)
    (h3 : orderOf (clabelS a * clabelS b) = 3) :
    orderOf ((H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩) = 3 := by
  obtain ⟨A, hAv, hA⟩ : ∃ A : (H u).stab, (A : Shat) = clabelS a ∧
      (H u).rho A = (H u).pt ⟨a, ha⟩ := ⟨_, rfl, rho_clabelS H ha⟩
  obtain ⟨B, hBv, hB⟩ : ∃ B : (H u).stab, (B : Shat) = clabelS b ∧
      (H u).rho B = (H u).pt ⟨b, hb⟩ := ⟨_, rfl, rho_clabelS H hb⟩
  have hAB' : (H u).rho (A * B) = (H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩ := by
    rw [map_mul, hA, hB]
  have hAB : orderOf (A * B) = 3 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, hAv, hBv]
    exact h3
  have hdvd := orderOf_map_dvd (H u).rho (A * B)
  rw [hAB', hAB] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
  · exfalso
    have hpb : (H u).pt ⟨b, hb⟩ * (H u).pt ⟨b, hb⟩ = 1 :=
      mul_self_of_mem_rootClassStar ((H u).pt_mem _)
    have he : (H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩ = 1 := orderOf_eq_one_iff.1 h1
    have hab : (H u).pt ⟨a, ha⟩ = (H u).pt ⟨b, hb⟩ := by
      calc (H u).pt ⟨a, ha⟩ = (H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩ * (H u).pt ⟨b, hb⟩ := by
            rw [mul_assoc, hpb, mul_one]
        _ = (H u).pt ⟨b, hb⟩ := by rw [he, one_mul]
    have hab' : a = b := congrArg Subtype.val ((H u).pt_injective hab)
    subst hab'
    have hsq : clabelS a * clabelS a = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, coe_clabelS, ← sq, ← (H a).orderOf_clabel, pow_orderOf_eq_one]
      rfl)
    rw [hsq, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  · exact h1

theorem tabBThree_eq_of_inverts_of_mem_neighborSet (H : ∀ x : CVert, LocalHom x)
    {u a b y : CVert} (ha : a ∈ cgraph.neighborSet u) (hb : b ∈ cgraph.neighborSet u)
    (hy : y ∈ cgraph.neighborSet u) (h3 : orderOf (clabelS a * clabelS b) = 3)
    (hinv : clabelS y * (clabelS a * clabelS b) * clabelS y = (clabelS a * clabelS b)⁻¹) :
    y = a ∨ y = b ∨ y = cvMul a (clabelS b) := by
  have hinvG := tabBThree_pt_inverts H ha hb hy hinv
  have h3' := tabBThree_orderOf_pt_mul_pt H ha hb h3
  obtain ⟨g, hga, hgb, -, -⟩ := exists_opposite (H u) h3'
  have hY'm : ((H u).iv ⟨y, hy⟩ : stdGroup) ∈ rootClass := ((H u).iv ⟨y, hy⟩).2
  have hY'i : ((H u).iv ⟨y, hy⟩ : stdGroup)⁻¹ = (H u).iv ⟨y, hy⟩ :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact sq_of_mem_rootClass hY'm)
  have hrel : ((H u).iv ⟨y, hy⟩ : stdGroup) * (g * rootInv * g⁻¹ * (g * tMinus * g⁻¹)) *
      (H u).iv ⟨y, hy⟩ = (g * rootInv * g⁻¹ * (g * tMinus * g⁻¹))⁻¹ := by
    rw [hga, hgb]
    have h1 : SemidirectProduct.inl (((H u).iv ⟨y, hy⟩ : stdGroup) *
        ((H u).iv ⟨a, ha⟩ * (H u).iv ⟨b, hb⟩) * (H u).iv ⟨y, hy⟩) =
        (H u).pt ⟨y, hy⟩ * ((H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩) * (H u).pt ⟨y, hy⟩ := by
      rw [map_mul, map_mul, map_mul]
    have h2 : SemidirectProduct.inl ((((H u).iv ⟨a, ha⟩ : stdGroup) * (H u).iv ⟨b, hb⟩)⁻¹) =
        ((H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩)⁻¹ := by
      rw [map_inv, map_mul]
    exact SemidirectProduct.inl_injective (h1.trans (hinvG.trans h2.symm))
  obtain ⟨X, hXdef⟩ : ∃ X : stdGroup, X = g⁻¹ * ((H u).iv ⟨y, hy⟩ : stdGroup) * g := ⟨_, rfl⟩
  have hX : X ∈ rootClass := by
    obtain ⟨k, hk⟩ := (mem_rootClass_iff _).1 hY'm
    refine (mem_rootClass_iff _).2 ⟨g⁻¹ * k, ?_⟩
    rw [hXdef, ← hk, rootMap, rootMap]
    group
  have hXinv : X * (rootInv * tMinus) * X⁻¹ = (rootInv * tMinus)⁻¹ := by
    calc X * (rootInv * tMinus) * X⁻¹ = g⁻¹ * (((H u).iv ⟨y, hy⟩ : stdGroup) *
          (g * rootInv * g⁻¹ * (g * tMinus * g⁻¹)) * ((H u).iv ⟨y, hy⟩ : stdGroup)⁻¹) * g := by
          rw [hXdef]
          group
      _ = g⁻¹ * (((H u).iv ⟨y, hy⟩ : stdGroup) * (g * rootInv * g⁻¹ * (g * tMinus * g⁻¹)) *
          (H u).iv ⟨y, hy⟩) * g := by rw [hY'i]
      _ = (rootInv * tMinus)⁻¹ := by
          rw [hrel]
          group
  have hYX : ((H u).iv ⟨y, hy⟩ : stdGroup) = g * X * g⁻¹ := by
    rw [hXdef]
    group
  rcases eq_of_mem_rootClass_of_inverts hX hXinv with h | h | h
  · left
    have e : (H u).iv ⟨y, hy⟩ = (H u).iv ⟨a, ha⟩ := Subtype.ext (by rw [hYX, h, hga])
    exact congrArg Subtype.val ((H u).iv.injective e)
  · right; left
    have e : (H u).iv ⟨y, hy⟩ = (H u).iv ⟨b, hb⟩ := Subtype.ext (by rw [hYX, h, hgb])
    exact congrArg Subtype.val ((H u).iv.injective e)
  · right; right
    obtain ⟨B, hBv, hB⟩ : ∃ B : (H u).stab, (B : Shat) = clabelS b ∧
        (H u).rho B = (H u).pt ⟨b, hb⟩ := ⟨_, rfl, rho_clabelS H hb⟩
    have hc := (H u).cvMul_mem B ha
    have hpa : (H u).pt ⟨a, ha⟩ * (H u).pt ⟨a, ha⟩ = 1 :=
      mul_self_of_mem_rootClassStar ((H u).pt_mem _)
    have hpb : (H u).pt ⟨b, hb⟩ * (H u).pt ⟨b, hb⟩ = 1 :=
      mul_self_of_mem_rootClassStar ((H u).pt_mem _)
    have h3p : ((H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩) ^ 3 = 1 := by
      rw [← h3']
      exact pow_orderOf_eq_one _
    have hbr := braid_of_pow_three hpa hpb h3p
    have hpbi : ((H u).pt ⟨b, hb⟩)⁻¹ = (H u).pt ⟨b, hb⟩ := inv_eq_of_mul_eq_one_right hpb
    have e1 : ((H u).iv ⟨y, hy⟩ : stdGroup) =
        (H u).iv ⟨a, ha⟩ * (H u).iv ⟨b, hb⟩ * (H u).iv ⟨a, ha⟩ := by
      rw [hYX, h, ← hga, ← hgb]
      group
    have h1 : SemidirectProduct.inl (((H u).iv ⟨a, ha⟩ : stdGroup) * (H u).iv ⟨b, hb⟩ *
        (H u).iv ⟨a, ha⟩) = (H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩ * (H u).pt ⟨a, ha⟩ := by
      rw [map_mul, map_mul]
    have hyc : (H u).pt ⟨y, hy⟩ = (H u).pt ⟨_, hc⟩ := by
      calc (H u).pt ⟨y, hy⟩ = (H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩ * (H u).pt ⟨a, ha⟩ :=
            (congrArg SemidirectProduct.inl e1).trans h1
        _ = ((H u).pt ⟨b, hb⟩)⁻¹ * (H u).pt ⟨a, ha⟩ * (H u).pt ⟨b, hb⟩ := by rw [hbr, hpbi]
        _ = ((H u).rho B)⁻¹ * (H u).pt ⟨a, ha⟩ * (H u).rho B := by rw [hB]
        _ = (H u).pt ⟨_, hc⟩ := ((H u).act B ⟨a, ha⟩ hc).symm
    have hyc' : y = cvMul a B := congrArg Subtype.val ((H u).pt_injective hyc)
    exact hyc'.trans (congrArg (cvMul a) hBv)

end CFSG.HardMathSupport.Dickson.I271
