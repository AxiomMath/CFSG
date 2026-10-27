module

public import CFSG.LargeExtraspecial.OrthoF2Eichler
public import CFSG.LieType.SeitzGeneration.OrthCommutator

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_apply_self eichler_conj
  eichler_mem_orthogonalGroup eichler_mem_rootGroup eichler_mul
  eichler_zero_right rootGroup_commute)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

namespace OrthoF2

theorem orderOf_eichler_mul_eichler_of_nonsingular {a b c : V} (ha : q a = 0) (hb : q b = 0)
    (hab : polar q a b = 1) (hac : polar q a c = 0) (hbc : polar q b c = 0) (hc : q c = 1) :
    orderOf (eichler q a c * eichler q b c) = 3 := by
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  set t₁ := eichler q a c with ht₁def
  set t₂ := eichler q b c with ht₂def
  have ht₁ : t₁ * t₁ = 1 := by rw [ht₁def]; exact eichler_mul_self hac
  have ht₂ : t₂ * t₂ = 1 := by rw [ht₂def]; exact eichler_mul_self hbc
  have ht₁inv : t₁⁻¹ = t₁ := inv_eq_iff_mul_eq_one.mpr ht₁
  have ht₂inv : t₂⁻¹ = t₂ := inv_eq_iff_mul_eq_one.mpr ht₂
  have ht₁a : t₁ a = a := by rw [ht₁def]; exact eichler_apply_self a c
  have ht₁b : t₁ b = b + c + a := by
    rw [ht₁def, eichler_apply_zmod2 ha hac b, polar_comm q b a, hab, hbc, hc]
    simp
  have ht₁c : t₁ c = c := by
    rw [ht₁def, eichler_apply_zmod2 ha hac c, polar_comm q c a, hac,
      polar_self_eq_zero q c, hc]
    simp
  have ht₂a : t₂ a = a + c + b := by
    rw [ht₂def, eichler_apply_zmod2 hb hbc a, hab, hac, hc]
    simp
  have ht₂c : t₂ c = c := by
    rw [ht₂def, eichler_apply_zmod2 hb hbc c, polar_comm q c b, hbc,
      polar_self_eq_zero q c, hc]
    simp
  have ht₁_acb : t₁ (a + c + b) = b := by
    rw [map_add, map_add, ht₁a, ht₁c, ht₁b]
    rw [show a + c + (b + c + a) = (a + a) + (c + c) + b from by abel]
    simp [vec_add_self]
  have hconj₁ : t₁ * t₂ * t₁⁻¹ = eichler q (t₁ b) (t₁ c) := by
    rw [ht₁def, ht₂def]
    exact eichler_conj (eichler_mem_orthogonalGroup q a c) b c
  have hconj₂ : t₂ * t₁ * t₂⁻¹ = eichler q (t₂ a) (t₂ c) := by
    rw [ht₂def, ht₁def]
    exact eichler_conj (eichler_mem_orthogonalGroup q b c) a c
  have hbraid₁ : t₁ * t₂ * t₁⁻¹ = eichler q (a + b + c) c := by
    rw [hconj₁, ht₁b, ht₁c, show b + c + a = a + b + c from by abel]
  have hbraid₂ : t₂ * t₁ * t₂⁻¹ = eichler q (a + b + c) c := by
    rw [hconj₂, ht₂a, ht₂c, show a + c + b = a + b + c from by abel]
  have hbraid : t₁ * t₂ * t₁ = t₂ * t₁ * t₂ := by
    have h := hbraid₁.trans hbraid₂.symm
    rwa [ht₁inv, ht₂inv] at h
  have hcube : (t₁ * t₂) ^ 3 = 1 := by
    have h3 : (t₁ * t₂) ^ 3 = (t₁ * t₂ * t₁) * (t₂ * t₁ * t₂) := by
      rw [pow_three']
      simp only [mul_assoc]
    rw [h3, ← hbraid]
    calc (t₁ * t₂ * t₁) * (t₁ * t₂ * t₁)
        = t₁ * t₂ * (t₁ * t₁) * t₂ * t₁ := by simp only [mul_assoc]
      _ = t₁ * t₂ * 1 * t₂ * t₁ := by rw [ht₁]
      _ = t₁ * (t₂ * t₂) * t₁ := by simp only [mul_assoc, mul_one]
      _ = t₁ * 1 * t₁ := by rw [ht₂]
      _ = 1 := by rw [mul_one, ht₁]
  have hτa : (t₁ * t₂) a = b := by
    rw [LinearEquiv.mul_apply, ht₂a, ht₁_acb]
  have hbane : b ≠ a := by
    intro h
    rw [h, polar_self_eq_zero q a] at hab
    exact zero_ne_one hab
  have hne : t₁ * t₂ ≠ 1 := by
    intro h1
    have h2 : (t₁ * t₂) a = b := hτa
    rw [h1] at h2
    simp only [LinearEquiv.coe_one, id] at h2
    exact hbane h2.symm
  exact orderOf_eq_prime hcube hne

theorem orderOf_eichler_mul_eichler_of_hyperbolic {a b c d : V} (ha : q a = 0) (hb : q b = 0)
    (hc : q c = 0) (hd : q d = 0) (hab : polar q a b = 1) (hcd : polar q c d = 1)
    (hac : polar q a c = 0) (had : polar q a d = 0) (hbc : polar q b c = 0)
    (hbd : polar q b d = 0) :
    orderOf (eichler q a c * eichler q b d) = 3 := by
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  set t₁ := eichler q a c with ht₁def
  set t₂ := eichler q b d with ht₂def
  have ht₁ : t₁ * t₁ = 1 := by rw [ht₁def]; exact eichler_mul_self hac
  have ht₂ : t₂ * t₂ = 1 := by rw [ht₂def]; exact eichler_mul_self hbd
  have ht₁inv : t₁⁻¹ = t₁ := inv_eq_iff_mul_eq_one.mpr ht₁
  have ht₂inv : t₂⁻¹ = t₂ := inv_eq_iff_mul_eq_one.mpr ht₂
  have ht₁a : t₁ a = a := by rw [ht₁def]; exact eichler_apply_self a c
  have ht₁b : t₁ b = b + c := by
    rw [ht₁def, eichler_apply_zmod2 ha hac b, polar_comm q b a, hab, hbc, hc]
    simp
  have ht₁d : t₁ d = d + a := by
    rw [ht₁def, eichler_apply_zmod2 ha hac d, polar_comm q d a, had, polar_comm q d c, hcd,
      hc]
    simp
  have ht₂a : t₂ a = a + d := by
    rw [ht₂def, eichler_apply_zmod2 hb hbd a, hab, had, hd]
    simp
  have ht₂c : t₂ c = c + b := by
    rw [ht₂def, eichler_apply_zmod2 hb hbd c, polar_comm q c b, hbc, hcd, hd]
    simp
  have hqbc : q (b + c) = 0 := by
    rw [map_add_eq, hb, hc, hbc]
    simp
  have hqda : q (d + a) = 0 := by
    rw [map_add_eq, hd, ha, polar_comm q d a, had]
    simp
  have hpol : polar q (b + c) (d + a) = 0 := by
    simp only [polar_add_left, polar_add_right, hbd, polar_comm q b a, hab, hcd,
      polar_comm q c a, hac]
    decide
  have hswap : eichler q (b + c) (d + a) = eichler q (a + d) (c + b) := by
    rw [CFSG.LieType.SeitzGeneration.OrthBlk.eichler_swap hqbc hqda hpol]
    rw [vec_neg, show d + a = a + d from by abel, show b + c = c + b from by abel]
  have hconj₁ : t₁ * t₂ * t₁⁻¹ = eichler q (t₁ b) (t₁ d) := by
    rw [ht₁def, ht₂def]
    exact eichler_conj (eichler_mem_orthogonalGroup q a c) b d
  have hconj₂ : t₂ * t₁ * t₂⁻¹ = eichler q (t₂ a) (t₂ c) := by
    rw [ht₂def, ht₁def]
    exact eichler_conj (eichler_mem_orthogonalGroup q b d) a c
  have hbraid₁ : t₁ * t₂ * t₁⁻¹ = eichler q (b + c) (d + a) := by
    rw [hconj₁, ht₁b, ht₁d]
  have hbraid₂ : t₂ * t₁ * t₂⁻¹ = eichler q (a + d) (c + b) := by
    rw [hconj₂, ht₂a, ht₂c]
  have hbraid : t₁ * t₂ * t₁ = t₂ * t₁ * t₂ := by
    have h := hbraid₁.trans (hswap.trans hbraid₂.symm)
    rwa [ht₁inv, ht₂inv] at h
  have ht₁_ad : t₁ (a + d) = d := by
    rw [map_add, ht₁a, ht₁d]
    rw [show a + (d + a) = (a + a) + d from by abel]
    simp [vec_add_self]
  have hcube : (t₁ * t₂) ^ 3 = 1 := by
    have h3 : (t₁ * t₂) ^ 3 = (t₁ * t₂ * t₁) * (t₂ * t₁ * t₂) := by
      rw [pow_three']
      simp only [mul_assoc]
    rw [h3, ← hbraid]
    calc (t₁ * t₂ * t₁) * (t₁ * t₂ * t₁)
        = t₁ * t₂ * (t₁ * t₁) * t₂ * t₁ := by simp only [mul_assoc]
      _ = t₁ * t₂ * 1 * t₂ * t₁ := by rw [ht₁]
      _ = t₁ * (t₂ * t₂) * t₁ := by simp only [mul_assoc, mul_one]
      _ = t₁ * 1 * t₁ := by rw [ht₂]
      _ = 1 := by rw [mul_one, ht₁]
  have hτa : (t₁ * t₂) a = d := by
    rw [LinearEquiv.mul_apply, ht₂a, ht₁_ad]
  have hdane : d ≠ a := by
    intro h
    rw [h, polar_comm q c a, hac] at hcd
    exact zero_ne_one hcd
  have hne : t₁ * t₂ ≠ 1 := by
    intro h1
    have h2 : (t₁ * t₂) a = d := hτa
    rw [h1] at h2
    simp only [LinearEquiv.coe_one, id] at h2
    exact hdane h2.symm
  exact orderOf_eq_prime hcube hne

theorem orderOf_eichler_mul_eichler_of_hyperbolic_swap {a b c d : V} (ha : q a = 0)
    (hb : q b = 0) (hc : q c = 0) (hd : q d = 0) (hab : polar q a b = 1)
    (hcd : polar q c d = 1) (hac : polar q a c = 0) (had : polar q a d = 0)
    (hbc : polar q b c = 0) (hbd : polar q b d = 0) :
    orderOf (eichler q a d * eichler q b c) = 3 :=
  orderOf_eichler_mul_eichler_of_hyperbolic ha hb hd hc hab
    (by rw [polar_comm q d c]; exact hcd) had hac hbd hbc

theorem commute_eichler_mul_eichler_of_hyperbolic {a b c d : V} (ha : q a = 0) (hb : q b = 0)
    (hc : q c = 0) (hd : q d = 0) (hab : polar q a b = 1) (hcd : polar q c d = 1)
    (hac : polar q a c = 0) (had : polar q a d = 0) (hbc : polar q b c = 0)
    (hbd : polar q b d = 0) :
    Commute (eichler q a c * eichler q b d) (eichler q a d * eichler q b c) := by
  have h₁₃ : Commute (eichler q a c) (eichler q a d) :=
    rootGroup_commute (eichler_mem_rootGroup hac) (eichler_mem_rootGroup had)
  have h₁₄ : Commute (eichler q a c) (eichler q b c) := by
    rw [CFSG.LieType.SeitzGeneration.OrthBlk.eichler_swap ha hc hac,
      CFSG.LieType.SeitzGeneration.OrthBlk.eichler_swap hb hc hbc]
    simp only [vec_neg]
    exact rootGroup_commute (eichler_mem_rootGroup (by rw [polar_comm q c a, hac]))
      (eichler_mem_rootGroup (by rw [polar_comm q c b, hbc]))
  have h₂₃ : Commute (eichler q b d) (eichler q a d) := by
    rw [CFSG.LieType.SeitzGeneration.OrthBlk.eichler_swap hb hd hbd,
      CFSG.LieType.SeitzGeneration.OrthBlk.eichler_swap ha hd had]
    simp only [vec_neg]
    exact rootGroup_commute (eichler_mem_rootGroup (by rw [polar_comm q d b, hbd]))
      (eichler_mem_rootGroup (by rw [polar_comm q d a, had]))
  have h₂₄ : Commute (eichler q b d) (eichler q b c) :=
    rootGroup_commute (eichler_mem_rootGroup hbd) (eichler_mem_rootGroup hbc)
  exact (h₁₃.mul_right h₁₄).mul_left (h₂₃.mul_right h₂₄)

theorem eichler_mul_eichler_not_mem_zpowers_of_hyperbolic {a b c d : V} (ha : q a = 0)
    (hb : q b = 0) (hc : q c = 0) (hd : q d = 0) (hab : polar q a b = 1)
    (hcd : polar q c d = 1) (hac : polar q a c = 0) (had : polar q a d = 0)
    (hbc : polar q b c = 0) (hbd : polar q b d = 0) :
    eichler q a d * eichler q b c ∉ Subgroup.zpowers (eichler q a c * eichler q b d) := by
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  set t₁ := eichler q a c with ht₁def
  set t₂ := eichler q b d with ht₂def
  set t₃ := eichler q a d with ht₃def
  set t₄ := eichler q b c with ht₄def
  set τ := t₁ * t₂ with hτdef
  set σ := t₃ * t₄ with hσdef
  intro hmem
  have hτord : orderOf τ = 3 := by
    rw [hτdef, ht₁def, ht₂def]
    exact orderOf_eichler_mul_eichler_of_hyperbolic ha hb hc hd hab hcd hac had hbc hbd
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hkmod : τ ^ (k % (3 : ℤ)) = σ := by
    rw [← hk, show (3 : ℤ) = (orderOf τ : ℤ) from by rw [hτord]; norm_num]
    exact zpow_mod_orderOf τ k
  have ht₁a : t₁ a = a := by rw [ht₁def]; exact eichler_apply_self a c
  have ht₂a : t₂ a = a + d := by
    rw [ht₂def, eichler_apply_zmod2 hb hbd a, hab, had, hd]
    simp
  have ht₁d : t₁ d = d + a := by
    rw [ht₁def, eichler_apply_zmod2 ha hac d, polar_comm q d a, had, polar_comm q d c, hcd,
      hc]
    simp
  have ht₁_ad : t₁ (a + d) = d := by
    rw [map_add, ht₁a, ht₁d]
    rw [show a + (d + a) = (a + a) + d from by abel]
    simp [vec_add_self]
  have hτa : τ a = d := by
    rw [hτdef, LinearEquiv.mul_apply, ht₂a, ht₁_ad]
  have ht₂d : t₂ d = d := by
    rw [ht₂def, eichler_apply_zmod2 hb hbd d, polar_comm q d b, hbd, polar_self_eq_zero q d,
      hd]
    simp
  have hτd : τ d = d + a := by
    rw [hτdef, LinearEquiv.mul_apply, ht₂d, ht₁d]
  have hτ₂a : (τ * τ) a = d + a := by
    rw [LinearEquiv.mul_apply, hτa, hτd]
  have ht₃a : t₃ a = a := by rw [ht₃def]; exact eichler_apply_self a d
  have ht₄a : t₄ a = a + c := by
    rw [ht₄def, eichler_apply_zmod2 hb hbc a, hab, hac, hc]
    simp
  have ht₃c : t₃ c = c + a := by
    rw [ht₃def, eichler_apply_zmod2 ha had c, polar_comm q c a, hac, hcd, hd]
    simp
  have hσa : σ a = c := by
    rw [hσdef, LinearEquiv.mul_apply, ht₄a, map_add, ht₃a, ht₃c]
    rw [show a + (c + a) = (a + a) + c from by abel]
    simp [vec_add_self]
  have hm0 : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
  have hmlt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases h : k % (3 : ℤ)
  · simp only [zpow_zero] at hkmod
    have hca : c = a := by
      have h1 : (1 : V ≃ₗ[ZMod 2] V) a = σ a :=
        congrArg (fun e : V ≃ₗ[ZMod 2] V => e a) hkmod
      simp only [LinearEquiv.coe_one, id] at h1
      rw [hσa] at h1
      exact h1.symm
    rw [hca, had] at hcd
    exact zero_ne_one hcd
  · simp only [zpow_one] at hkmod
    have hcd' : c = d := by
      have h1 : σ a = τ a := by rw [hkmod]
      rw [hσa, hτa] at h1
      exact h1
    rw [hcd', polar_self_eq_zero q d] at hcd
    exact zero_ne_one hcd
  · simp only [zpow_two] at hkmod
    have hca : c = d + a := by
      have h1 : σ a = (τ * τ) a := by
        rw [← hkmod]
      rw [hσa, hτ₂a] at h1
      exact h1
    have h0 : polar q (d + a) d = 0 := by
      rw [polar_add_left, polar_self_eq_zero q d, had]
      simp
    rw [hca, h0] at hcd
    exact zero_ne_one hcd

end OrthoF2

end CFSG.LargeExtraspecial
