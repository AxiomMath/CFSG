module

public import CFSG.CGT.Stroth77.Stroth34Defs
public import CFSG.CGT.Stroth77.StrothAmbient
public import CFSG.CGT.Stroth77.StrothFrameD

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

abbrev H47C_S (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
    (dD : StrothWeakTypeData D (.t200 m)) : Subgroup G :=
  (F.S : Subgroup G) ⊓ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G)

@[expose] def H47StrongClosure : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ x ∈ Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2)),
      ∀ g ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G),
        g⁻¹ * x * g ∈ H47C_S F dD →
        g⁻¹ * x * g ∈ Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2))

@[expose] def H47GeneratorFusion : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ g ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G),
      g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g ∈ H47C_S F dD →
      g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g ∈
        Subgroup.zpowers ((dD.c : G) ^ 2 ^ (m - 2))

@[expose] def H47Extremal : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ g ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G),
      g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g ∈ H47C_S F dD →
      ∃ k ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G),
        (k⁻¹ * (g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g) * k =
            (dD.c : G) ^ 2 ^ (m - 2) ∨
          k⁻¹ * (g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g) * k =
            ((dD.c : G) ^ 2 ^ (m - 2))⁻¹) ∧
        ∀ s ∈ H47C_S F dD,
          s * (g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g) =
            (g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g) * s →
          k⁻¹ * s * k ∈ (F.S : Subgroup G)

theorem H47_c₂_sq {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))
    (hm : 2 ≤ m) :
    ((dD.c : G) ^ 2 ^ (m - 2)) * ((dD.c : G) ^ 2 ^ (m - 2)) =
      (dD.c : G) ^ 2 ^ (m - 1) := by
  rw [← pow_add, ← two_mul, ← pow_succ', show m - 2 + 1 = m - 1 by omega]

theorem H47_c₂_mem_C_S {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t200 m)} (h : F.IsD D dD) :
    (dD.c : G) ^ 2 ^ (m - 2) ∈ H47C_S F dD := by
  haveI := dD.isMulCommutative
  refine Subgroup.mem_inf.mpr ⟨h.le_S (D.pow_mem dD.c.2 _), ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mul_comm_of_mem_isMulCommutative D (D.pow_mem dD.c.2 _)
      (D.pow_mem dD.c.2 _))

theorem H47StrongClosure_of_generator (hgen : H47GeneratorFusion) : H47StrongClosure := by
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel x hx g hg hy
  set c₁ := (dD.c : G) ^ 2 ^ (m - 1) with hc₁
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  have hsq : c₂ * c₂ = c₁ := by rw [hc₂, hc₁]; exact H47_c₂_sq dD hm
  have hc₂T : c₂ ∈ H47C_S F dD := H47_c₂_mem_C_S h
  have hAT : Subgroup.zpowers c₂ ≤ H47C_S F dD := Subgroup.zpowers_le.mpr hc₂T
  have hc₂2 : c₂ ^ (2 : ℤ) = c₁ := by rw [zpow_two]; exact hsq
  have hc₁A : c₁ ∈ Subgroup.zpowers c₂ := by
    rw [show c₁ = c₂ ^ (2 : ℤ) by rw [hc₂2]]
    exact Subgroup.mem_zpowers_iff.mpr ⟨2, rfl⟩
  have hc₁powA : ∀ t : ℤ, c₁ ^ t ∈ Subgroup.zpowers c₂ := fun t =>
    Subgroup.zpow_mem (Subgroup.zpowers c₂) hc₁A t
  have hc₁powT : ∀ t : ℤ, c₁ ^ t ∈ H47C_S F dD := fun t => hAT (hc₁powA t)
  have hgcomm : g⁻¹ * c₁ * g = c₁ := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg
    calc g⁻¹ * c₁ * g = g⁻¹ * (c₁ * g) := by group
      _ = g⁻¹ * (g * c₁) := by rw [h1]
      _ = c₁ := by group
  have hgzpow : ∀ t : ℤ, g⁻¹ * c₁ ^ t * g = c₁ ^ t := by
    intro t
    calc g⁻¹ * c₁ ^ t * g = (g⁻¹ * c₁ * (g⁻¹)⁻¹) ^ t := by rw [conj_zpow, inv_inv]
      _ = (g⁻¹ * c₁ * g) ^ t := by rw [inv_inv]
      _ = c₁ ^ t := by rw [hgcomm]
  obtain ⟨k, hkx⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hy' : g⁻¹ * x * g = g⁻¹ * c₂ ^ k * g := by rw [← hkx]
  rcases Int.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  ·
    have hx1 : x = c₁ ^ t := by
      rw [← hkx]
      rw [show t + t = 2 * t by ring]
      calc c₂ ^ (2 * t) = (c₂ ^ (2 : ℤ)) ^ t := by rw [zpow_mul]
        _ = c₁ ^ t := by rw [hc₂2]
    have hy1 : g⁻¹ * x * g = c₁ ^ t := by
      rw [hx1]
      exact hgzpow t
    rw [hy1] at hy ⊢
    exact hc₁powA t
  ·
    have hx1 : x = c₁ ^ t * c₂ := by
      rw [← hkx]
      rw [show 2 * t + 1 = 2 * t + 1 by rfl]
      calc c₂ ^ (2 * t + 1) = c₂ ^ (2 * t) * c₂ := by rw [zpow_add, zpow_one]
        _ = (c₂ ^ (2 : ℤ)) ^ t * c₂ := by rw [zpow_mul]
        _ = c₁ ^ t * c₂ := by rw [hc₂2]
    have hy1 : g⁻¹ * x * g = c₁ ^ t * (g⁻¹ * c₂ * g) := by
      rw [hx1]
      have h1 : g⁻¹ * (c₁ ^ t * c₂) * g = (g⁻¹ * c₁ ^ t * g) * (g⁻¹ * c₂ * g) := by group
      rw [h1]
      congr 1
      exact hgzpow t
    have hzT : g⁻¹ * c₂ * g ∈ H47C_S F dD := by
      have h1 : g⁻¹ * c₂ * g = (c₁ ^ t)⁻¹ * (g⁻¹ * x * g) := by
        rw [hy1]; group
      rw [h1]
      exact (H47C_S F dD).mul_mem ((H47C_S F dD).inv_mem (hc₁powT t)) hy
    have hzA := hgen F hm dD h hSN hnc e he hS hrel g hg hzT
    have hyA : g⁻¹ * x * g ∈ Subgroup.zpowers c₂ := by
      rw [hy1]
      exact (Subgroup.zpowers c₂).mul_mem (hc₁powA t) hzA
    exact hyA

end CFSG.CGT.Stroth77
